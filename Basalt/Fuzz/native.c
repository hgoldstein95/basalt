/*
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Michael Hicks
*/
/* The C half of Basalt's libFuzzer bridge; `Basalt/Fuzz/Runner.lean` is the Lean half, and
   fuzz-run/README.md ("The C bridge") the overview. libFuzzer's loop hands `LLVMFuzzerTestOneInput`
   one *input*, a byte buffer, at a time, and the Lean callback runs one *test* of the property on
   it, the *run* of that input; how many bytes the run read is its *cursor*
   (`Basalt/Fuzz/Basic.lean`).

   The sections, in order: libFuzzer's entry points, and helpers; the coverage counters
   (`BASALT_COV_OUT` and the `io-cov` backend); features, as libFuzzer counts them (an edge and its
   hit-count bucket); hybrid campaigns (`--hybrid`), which alternate random *rounds* with fuzzing ones
   and hand a random round's *finds*, the tests that reached a new feature, to libFuzzer as *seeds*
   (`Basalt/Fuzz/Cover.lean`); truncation (`--truncate`); the run report; the custom mutator; running
   a test; and starting a campaign. */
#include <lean/lean.h>
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <unistd.h>

/* ---------------------------------------------------------------------------------------------
   libFuzzer's entry points, and helpers

   What this file calls in libFuzzer (its driver and its default mutations), the Lean callback it
   holds for the campaign, and the small helpers every section uses.
   --------------------------------------------------------------------------------------------- */

/* libFuzzer's driver entry point. Two spellings, selected at compile time:

   - Default (LLVM >= 12): the stable C entry `LLVMFuzzerRunDriver`.
   - `-DBASALT_FUZZ_LEGACY_DRIVER`: clang 11 and earlier expose no C entry, so we call the C++
     symbol `fuzzer::FuzzerDriver` by its mangled name.

   `fuzz-run/build.sh` picks the spelling by probing the runtime archive for the C entry. */
#ifdef BASALT_FUZZ_LEGACY_DRIVER
extern int _ZN6fuzzer12FuzzerDriverEPiPPPcPFiPKhmE(
    int *argc, char ***argv, int (*cb)(const uint8_t *, size_t));
#define BASALT_FUZZER_RUN_DRIVER _ZN6fuzzer12FuzzerDriverEPiPPPcPFiPKhmE
#else
extern int LLVMFuzzerRunDriver(
    int *argc, char ***argv, int (*cb)(const uint8_t *, size_t));
#define BASALT_FUZZER_RUN_DRIVER LLVMFuzzerRunDriver
#endif

/* libFuzzer's own default mutation suite, callable on any buffer we hand it. Declared here rather
   than included because the vendored runtime ships no headers. */
extern size_t LLVMFuzzerMutate(uint8_t *Data, size_t Size, size_t MaxSize);

static lean_object *g_run = NULL;   /* the Lean closure `ByteArray -> IO UInt8`, held for the run */

__attribute__((noreturn)) static void basalt_fuzz_die(const char *what) {
  fprintf(stderr, "[basalt] fatal: %s\n", what);
  fflush(NULL);
  exit(1);
}

/* Grow one of this file's own `malloc`ed buffers (`p`, of `*cap` elements of `elt` bytes) to hold at
   least `need`, doubling. libFuzzer's buffers are never passed here: its input is only read, or
   written within the `MaxSize` it hands the custom mutator. */
static void *basalt_grow_buf(void *p, size_t *cap, size_t need, size_t elt) {
  if (need <= *cap) return p;
  size_t c = *cap ? *cap : 64;
  while (c < need) c *= 2;
  void *q = realloc(p, c * elt);
  if (!q) basalt_fuzz_die("out of memory");
  *cap = c;
  return q;
}

/* ---------------------------------------------------------------------------------------------
   The coverage counters

   SanitizerCoverage's 8-bit counters and PC table are the linker-concatenated `__sancov_*`
   sections, in the same object order. libFuzzer resets the counters before every run, so after a
   run they are that run's.
   --------------------------------------------------------------------------------------------- */

#ifdef __APPLE__
#include <mach-o/dyld.h>
extern uint8_t __start___sancov_cntrs[] __asm("section$start$__DATA$__sancov_cntrs");
extern uint8_t __stop___sancov_cntrs[] __asm("section$end$__DATA$__sancov_cntrs");
extern const uintptr_t __start___sancov_pcs[] __asm("section$start$__DATA$__sancov_pcs");
extern const uintptr_t __stop___sancov_pcs[] __asm("section$end$__DATA$__sancov_pcs");
/* `nm` prints Mach-O addresses unslid, so an offset is the PC less the image's ASLR slide. */
static uintptr_t basalt_image_base(void) { return (uintptr_t)_dyld_get_image_vmaddr_slide(0); }
#else
extern uint8_t __start___sancov_cntrs[] __attribute__((weak));
extern uint8_t __stop___sancov_cntrs[] __attribute__((weak));
extern const uintptr_t __start___sancov_pcs[] __attribute__((weak));
extern const uintptr_t __stop___sancov_pcs[] __attribute__((weak));
extern const char __executable_start[] __attribute__((weak));
static uintptr_t basalt_image_base(void) { return (uintptr_t)__executable_start; }
#endif

/* How many counters this binary has (the ELF symbols are weak, so absent ones are null). */
static size_t basalt_ncounters(void) {
  uintptr_t start = (uintptr_t)__start___sancov_cntrs, stop = (uintptr_t)__stop___sancov_cntrs;
  return start != 0 && stop > start ? (size_t)(stop - start) : 0;
}

/* Cumulative edge coverage, for comparing backends. libFuzzer reports only a campaign-wide count,
   which also counts Basalt's own plumbing, and that differs between backends. So when
   `BASALT_COV_OUT` names a file, the campaign's tests are numbered from 1, and `g_cov.first[i]` holds
   the number of the test that first hit edge `i` (counter `i`), or 0 if none has: counting from 1
   leaves 0, the value `calloc` gives, to mean "never hit". Coverage after `n` tests is then the number
   of edges with `0 < first[i] <= n`, so one dump gives the whole curve. At exit every edge is written
   as `<offset> <first>`, the offset from the executable base so `nm` can attribute it to a function,
   and `<file>.time` the milliseconds elapsed at every 1000th test, which maps tests to time. Both are
   kept in memory and written once, at exit. */
static struct {
  uint32_t *first;           /* per counter, the test that first hit it, from 1 (0: none yet)     */
  size_t n;                  /* counters                                                          */
  uint32_t runs;             /* tests counted so far                                              */
  uint64_t *ms;              /* `ms[k]`: milliseconds elapsed at test `1000 * (k + 1)`            */
  size_t nms, cap_ms;
  struct timespec t0;        /* when the campaign started                                         */
} g_cov;

/* After a test: count it, record each counter it hit for the first time, and at every 1000th test the
   elapsed time. The counters are the test's own, since they are cleared before it. */
static void basalt_cov_accumulate(void) {
  g_cov.runs++;
  /* Most counters are zero, so they are read a word at a time and only a word's nonzero bytes are
     visited. */
  const uint8_t *c = __start___sancov_cntrs;
  size_t i = 0;
#if __BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__
  for (; i + 8 <= g_cov.n; i += 8) {
    uint64_t w;
    memcpy(&w, c + i, 8);
    while (w) {
      unsigned k = (unsigned)__builtin_ctzll(w) / 8;   /* the lowest nonzero byte, counter i + k */
      if (!g_cov.first[i + k]) g_cov.first[i + k] = g_cov.runs;
      w &= ~(0xffULL << (8 * k));
    }
  }
#endif
  for (; i < g_cov.n; i++)
    if (c[i] && !g_cov.first[i]) g_cov.first[i] = g_cov.runs;
  if (g_cov.runs % 1000 == 0) {
    struct timespec t;
    clock_gettime(CLOCK_MONOTONIC, &t);
    g_cov.ms = basalt_grow_buf(g_cov.ms, &g_cov.cap_ms, g_cov.nms + 1, sizeof *g_cov.ms);
    g_cov.ms[g_cov.nms++] = (uint64_t)(t.tv_sec - g_cov.t0.tv_sec) * 1000 +
                            (uint64_t)((t.tv_nsec - g_cov.t0.tv_nsec) / 1000000);
  }
}

/* At exit: write `<offset> <first test>` for every counter to `BASALT_COV_OUT`, and
   `<tests> <milliseconds>` at every 1000th test to `<file>.time`. */
static void basalt_cov_dump(void) {
  const char *path = getenv("BASALT_COV_OUT");
  if (!g_cov.first || !path) return;
  FILE *f = fopen(path, "w");
  if (f) {
    for (size_t i = 0; i < g_cov.n; i++)
      fprintf(f, "%lx %u\n", (unsigned long)(__start___sancov_pcs[2 * i] - basalt_image_base()),
              (unsigned)g_cov.first[i]);
    fclose(f);
  }
  char tpath[4096];
  snprintf(tpath, sizeof tpath, "%s.time", path);
  if ((f = fopen(tpath, "w"))) {
    for (size_t k = 0; k < g_cov.nms; k++)
      fprintf(f, "%zu %llu\n", 1000 * (k + 1), (unsigned long long)g_cov.ms[k]);
    fclose(f);
  }
}

/* At the start of a campaign: if `BASALT_COV_OUT` names a file, allocate `first` and start the clock;
   otherwise leave `first` NULL, which turns every other `basalt_cov_*` into a no-op. */
static void basalt_cov_init(void) {
  const char *path = getenv("BASALT_COV_OUT");
  g_cov.n = basalt_ncounters();
  if (!path || !g_cov.n) return;
  if ((size_t)(__stop___sancov_pcs - __start___sancov_pcs) != 2 * g_cov.n) return;
  g_cov.first = calloc(g_cov.n, sizeof *g_cov.first);
  if (!g_cov.first) return;
  atexit(basalt_cov_dump);
  clock_gettime(CLOCK_MONOTONIC, &g_cov.t0);
}

/* `io-cov`'s two calls around each test, in place of libFuzzer's loop (`Basalt.Fuzz.covBeforeTestImpl`
   and `covAfterTestImpl`). Before it the counters are cleared, as libFuzzer clears them before each
   run, and the first call sets up `g_cov`; after it they are accumulated as a fuzzing run's are.
   Without `BASALT_COV_OUT` both do nothing. */
LEAN_EXPORT lean_object *basalt_cov_before_test(void) {
  static int ready;
  if (!ready) { ready = 1; basalt_cov_init(); }
  if (g_cov.first) memset(__start___sancov_cntrs, 0, g_cov.n);
  return lean_box(0);
}

LEAN_EXPORT lean_object *basalt_cov_after_test(void) {
  if (g_cov.first) basalt_cov_accumulate();
  return lean_box(0);
}

/* ---------------------------------------------------------------------------------------------
   Features, as libFuzzer counts them

   A feature is an edge together with the bucket of its 8-bit counter (1, 2, 3, 4–7, 8–15, 16–31,
   32–127, 128+). libFuzzer's own bookkeeping (`TracePC::CollectFeatures`) is internal C++ with no
   stable entry, so a hybrid campaign reads the counters itself after each test to check it for new
   coverage.
   --------------------------------------------------------------------------------------------- */

/* libFuzzer's `CounterToFeature`: an 8-bit counter's hit-count bucket, 0..7. */
static inline uint32_t basalt_bucket(uint8_t c) {
  return c >= 128 ? 7 : c >= 32 ? 6 : c >= 16 ? 5 : c >= 8 ? 4 : c >= 4 ? 3 : c - 1;
}

static struct {
  size_t    n;               /* counters                                                          */
  uint32_t *run;             /* the last run's features (counter index * 8 + bucket)              */
  size_t    nrun;
} g_feat;

static void basalt_feat_init(void) {
  g_feat.n = basalt_ncounters();
  if (!g_feat.n) basalt_fuzz_die("no SanitizerCoverage counters in this binary");
  g_feat.run = malloc(g_feat.n * sizeof *g_feat.run);
  if (!g_feat.run) basalt_fuzz_die("out of memory for the coverage map");
}

/* Read the last run's features into `g_feat.run`. Most counters are zero, so the counters are read a
   word at a time, and only a word's nonzero bytes are visited. */
static void basalt_feat_read(void) {
  const uint8_t *c = __start___sancov_cntrs;
  size_t nf = 0, i = 0;
#if __BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__
  for (; i + 8 <= g_feat.n; i += 8) {
    uint64_t w;
    memcpy(&w, c + i, 8);
    while (w) {
      unsigned k = (unsigned)__builtin_ctzll(w) / 8;   /* the lowest nonzero byte, counter i + k */
      g_feat.run[nf++] = (uint32_t)((i + k) * 8 + basalt_bucket((uint8_t)(w >> (8 * k))));
      w &= ~(0xffULL << (8 * k));
    }
  }
#endif
  for (; i < g_feat.n; i++)
    if (c[i]) g_feat.run[nf++] = (uint32_t)(i * 8 + basalt_bucket(c[i]));
  g_feat.nrun = nf;
}

static inline int basalt_bit(const uint8_t *map, uint32_t f) { return map[f >> 3] & (1u << (f & 7)); }
static inline void basalt_set_bit(uint8_t *map, uint32_t f) { map[f >> 3] |= (uint8_t)(1u << (f & 7)); }

/* Mark the last run's features in `seen` (a bit per feature); how many were new to it. */
static size_t basalt_feat_mark(uint8_t *seen) {
  size_t fresh = 0;
  for (size_t i = 0; i < g_feat.nrun; i++) {
    uint32_t f = g_feat.run[i];
    if (basalt_bit(seen, f)) continue;
    basalt_set_bit(seen, f);
    fresh++;
  }
  return fresh;
}

/* ---------------------------------------------------------------------------------------------
   Hybrid campaigns (`--hybrid`)

   One libFuzzer loop, two modes. In a *random* round the callback ignores libFuzzer's buffer, runs
   the property at `RecordGen`, and returns -1, so libFuzzer neither keeps the input nor records its
   features; this file checks each test for new coverage itself, and the Lean side keeps the
   recorded bytes of the new ones. In a *fuzz* round the callback runs libFuzzer's buffer at
   `FuzzGen` as usual. On a switch to fuzzing the Lean side's set cover of the round's finds is
   queued, and the custom mutator hands it to libFuzzer one seed per call, so each enters the corpus
   by libFuzzer's own admission rule. When to switch is `basalt_hy_step`'s decision;
   fuzz-run/README.md gives the rules.
   --------------------------------------------------------------------------------------------- */

enum { HY_FUZZ = 0, HY_RANDOM = 1 };

/* The first tests of a round, which no rule ends it within. */
#define BASALT_STALE_FLOOR 256

static struct {
  struct {                     /* set once, by `basalt_hybrid_config`                             */
    int          on;
    lean_object *run_random;   /* `ByteArray -> IO UInt8`: a random round's test, at `RecordGen`  */
    lean_object *cover;        /* `IO (Array ByteArray)`: the set cover of the round's finds      */
    uint64_t     fixed;        /* `--hybrid=N`: the random round's length; 0: the stale rule      */
  } cfg;
  struct {                     /* where the campaign is                                           */
    int          started;      /* libFuzzer has called the mutator, so the loop is running        */
    int          mode;         /* `HY_RANDOM` or `HY_FUZZ`                                        */
    uint64_t     total, n;     /* tests run: in the campaign, in this round                       */
    uint64_t     last_find;    /* the round's test of its last find (0: none)                     */
  } round;
  struct {                     /* the finds, which the stale rule reads                           */
    uint64_t     all;          /* F: tests that reached a feature no earlier test did             */
    uint64_t     in_round;     /* those of this random round                                      */
    double       len_sum;      /* their lengths in bytes, summed                                  */
  } finds;
  struct {                     /* coverage, a bit per feature                                     */
    uint8_t     *seen;         /* reached by some test of either mode                             */
    uint8_t     *fresh;        /* first reached in this random round                              */
  } map;
  struct {                     /* the last random test, as `basalt_hybrid_judge` found it         */
    size_t       fresh;        /* its features new to the campaign                                */
    uint64_t     len;          /* its length in bytes                                             */
  } judged;
  struct {                     /* the set cover, waiting to be handed to libFuzzer                */
    lean_object *seeds;        /* an `Array ByteArray`, or NULL once handed over                  */
    size_t       pos;          /* the next one                                                    */
  } queue;
} g_hy;

/* Check a passed random test for new coverage, from its `RecordGen` callback: the features the set
   cover is over, or an empty array if the test is not a find. `len` is the length of its recorded
   bytes. */
LEAN_EXPORT lean_object *basalt_hybrid_judge(uint64_t len) {
  basalt_feat_read();
  size_t fresh = 0, nk = 0;
  for (size_t i = 0; i < g_feat.nrun; i++) {
    uint32_t f = g_feat.run[i];
    /* Seen, but not in this round: an earlier round reached it, so the cover need not. */
    if (basalt_bit(g_hy.map.seen, f) && !basalt_bit(g_hy.map.fresh, f)) continue;
    /* Kept for the cover, compacted into `g_feat.run`. */
    g_feat.run[nk++] = f;
    /* New to the campaign: this is what makes the test a find. */
    if (basalt_bit(g_hy.map.seen, f)) continue;
    basalt_set_bit(g_hy.map.seen, f);
    basalt_set_bit(g_hy.map.fresh, f);
    fresh++;
  }
  /* For `basalt_hy_step`, which the callback's caller runs next. */
  g_hy.judged.fresh = fresh;
  g_hy.judged.len = len;
  if (!fresh) return lean_mk_empty_array();
  g_hy.finds.in_round++;
  lean_object *a = lean_alloc_array(nk, nk);
  for (size_t i = 0; i < nk; i++) lean_array_cptr(a)[i] = lean_box_uint32(g_feat.run[i]);
  return a;
}

/* At a switch to fuzzing: queue the set cover of this random round's finds. */
static void basalt_hy_cover(void) {
  /* `g_hy.cfg.cover` is a Lean closure (`Basalt/Fuzz/Cover.lean`) over the finds `goHybrid`
     keeps. */
  lean_inc(g_hy.cfg.cover);                           /* apply consumes the function object   */
  lean_object *res = lean_apply_1(g_hy.cfg.cover, lean_io_mk_world());
  if (!lean_io_result_is_ok(res)) {
    lean_io_result_show_error(res);
    basalt_fuzz_die("the random round's set cover failed");
  }
  lean_object *q = lean_io_result_get_value(res);
  lean_inc(q);
  lean_dec(res);
  /* Seeds of the last cover not yet handed to libFuzzer are dropped. */
  if (g_hy.queue.seeds) lean_dec(g_hy.queue.seeds);
  g_hy.queue.seeds = q;
  g_hy.queue.pos = 0;
  /* The next random round's finds are checked against what it alone reaches. */
  memset(g_hy.map.fresh, 0, g_feat.n);
  fprintf(stderr, "[basalt] random round: %llu finds, %zu seeds after set cover\n",
          (unsigned long long)g_hy.finds.in_round, lean_array_size(q));
  g_hy.finds.in_round = 0;
}

/* Switch modes, starting a new round. */
static void basalt_hy_switch(void) {
  fprintf(stderr, "[basalt] switch to %s after test %llu (%llu in the round; %llu finds)\n",
          g_hy.round.mode == HY_RANDOM ? "fuzzing" : "random", (unsigned long long)g_hy.round.total,
          (unsigned long long)g_hy.round.n, (unsigned long long)g_hy.finds.all);
  /* Leaving a random round: its finds become libFuzzer's seeds. */
  if (g_hy.round.mode == HY_RANDOM) basalt_hy_cover();
  g_hy.round.mode = g_hy.round.mode == HY_RANDOM ? HY_FUZZ : HY_RANDOM;
  /* Each mode is judged by its own effort, counted from the start of its round. */
  g_hy.round.n = g_hy.round.last_find = 0;
}

/* The stale rule's `E`: how many tests a round may go without a find. */
static double basalt_stale_effort(void) {
  /* `L̄ · ln L̄`, `L̄` the finds' mean length in bytes: about the random-position mutations it takes
     to touch each of an input's bytes once (the coupon collector's bound). */
  double lbar = g_hy.finds.all ? g_hy.finds.len_sum / (double)g_hy.finds.all : 1;
  double e = lbar > 1 ? lbar * log(lbar) : 1;
  /* Fuzzing spends that on every corpus input; the finds stand in for the corpus's size. */
  if (g_hy.round.mode == HY_FUZZ) e *= (double)(g_hy.finds.all ? g_hy.finds.all : 1);
  return e;
}

/* After every test once the loop has started: count it, and switch if the rule says so. `fresh` is
   whether it was a find, `len` its length in bytes. */
static void basalt_hy_step(int fresh, uint64_t len) {
  g_hy.round.n++;
  g_hy.round.total++;
  if (fresh) {
    g_hy.finds.all++;
    g_hy.finds.len_sum += (double)len;
    g_hy.round.last_find = g_hy.round.n;
  }
  /* `--hybrid=N`: one switch, after `N` random tests. */
  if (g_hy.cfg.fixed) {
    if (g_hy.round.mode == HY_RANDOM && g_hy.round.n >= g_hy.cfg.fixed) basalt_hy_switch();
    return;
  }
  /* The stale rule, in either mode: `E` tests since the round's last find, and never within the
     floor. */
  if (g_hy.round.n >= BASALT_STALE_FLOOR &&
      (double)(g_hy.round.n - g_hy.round.last_find) >= basalt_stale_effort())
    basalt_hy_switch();
}

/* The hybrid's share of the custom mutator: in a random round, keep libFuzzer from mutating; in a
   fuzzing round, hand over the random round's seeds. Returns 0 to leave the call to the ordinary
   mutator. */
static size_t basalt_hy_mutate(uint8_t *Data, size_t Size, size_t MaxSize) {
  /* libFuzzer runs its initial inputs before it first mutates; the campaign starts here. */
  if (!g_hy.round.started) {
    g_hy.round.started = 1;
    g_hy.round.mode = HY_RANDOM;
  }
  /* A random test ignores the buffer, so any buffer will do: the one in hand, unchanged. */
  if (g_hy.round.mode == HY_RANDOM) {
    if (!Size) { Data[0] = 0; return 1; }
    return Size;
  }
  /* The next queued seed replaces this mutation, so libFuzzer runs it and admits it to its corpus
     by its own rule. */
  while (g_hy.queue.seeds) {
    if (g_hy.queue.pos == lean_array_size(g_hy.queue.seeds)) {   /* all handed over */
      lean_dec(g_hy.queue.seeds);
      g_hy.queue.seeds = NULL;
      break;
    }
    lean_object *sd = lean_array_get_core(g_hy.queue.seeds, g_hy.queue.pos++);
    /* `MaxSize` is below `-max_len` only under a `-len_control` ramp, which cuts a longer seed. */
    size_t n = lean_sarray_size(sd) < MaxSize ? lean_sarray_size(sd) : MaxSize;
    if (n) { memcpy(Data, lean_sarray_cptr(sd), n); return n; }
  }
  return 0;
}

/* Arm a hybrid campaign, before `basalt_fuzz_go`. */
LEAN_EXPORT lean_object *basalt_hybrid_config(lean_object *run_random, lean_object *cover,
                                              uint64_t fixed) {
#ifdef BASALT_FUZZ_LEGACY_DRIVER
  /* The legacy driver ignores a `-1` return, so it would admit a random round's buffers, which are
     not those tests' inputs, into the corpus. */
  basalt_fuzz_die("--hybrid needs libFuzzer from LLVM 12 or later (this one ignores a -1 return)");
#endif
  g_hy.cfg.on = 1;
  g_hy.cfg.run_random = run_random;
  g_hy.cfg.cover = cover;
  g_hy.cfg.fixed = fixed;                               /* `SwitchRule.encode`'s                 */
  return lean_io_result_mk_ok(lean_box(0));             /* `IO`, unlike the `BaseIO` externs here */
}

/* ---------------------------------------------------------------------------------------------
   Truncation (`--truncate`)

   Before libFuzzer mutates the input it has just run, the input is cut to the bytes its run read,
   so that the mutation lands on bytes the run used. The cut input runs exactly as before, since
   `readByte` reads `0` past the end. Only the input just run is cut: an input libFuzzer picks from
   its corpus to start a mutation chain has no run at hand to say how much of it was read.
   --------------------------------------------------------------------------------------------- */

static int g_trunc;           /* `--truncate`                                                    */

/* The campaign's totals, each counted up test by test and reported at exit. */
static struct {
  uint64_t runs;              /* tests on libFuzzer's buffer                                     */
  uint64_t random;            /* a hybrid campaign's random-round tests                         */
  uint64_t starved;           /* runs that read past the end of their buffer                    */
  uint64_t max_deficit;       /* how far off `-max_len` is, if it is                            */
  uint64_t cut, cut_bytes;    /* inputs truncated, and the bytes that removed                   */
} g_stats;

static uint64_t g_cursor;     /* the bytes the current run read, from `basalt_fuzz_note_cursor`  */

/* The last run's input and how many bytes it read. */
static struct { uint8_t *buf; size_t size, cap; uint64_t cursor; int valid; } g_last;

/* Called from Lean at the end of each run with how many bytes it read, past the end included.
   Called while `LLVMFuzzerTestOneInput` is still on the stack, so it is the current run's. */
LEAN_EXPORT lean_object *basalt_fuzz_note_cursor(uint64_t cursor) {
  g_cursor = cursor;
  return lean_box(0);                               /* Unit */
}

/* After a run, under `--truncate`: remember it as the last run. */
static void basalt_after_run(const uint8_t *Data, size_t Size) {
  g_last.buf = basalt_grow_buf(g_last.buf, &g_last.cap, Size ? Size : 1, 1);
  if (Size) memcpy(g_last.buf, Data, Size);
  g_last.size = Size;
  g_last.cursor = g_cursor;
  g_last.valid = 1;
}

/* The size to cut `Data` to before mutating it: its cursor, if it is the last run's input. */
static size_t basalt_truncate(const uint8_t *Data, size_t Size) {
  /* Not the input just run (a chain's start, picked from the corpus): no run says what it read. */
  if (!g_last.valid || Size != g_last.size || (Size && memcmp(Data, g_last.buf, Size) != 0))
    return Size;
  uint64_t cursor = g_last.cursor;
  /* The run read all of it, or past its end: nothing to cut. */
  if (cursor >= Size) return Size;
  if (cursor == 0) cursor = 1;          /* libFuzzer's mutators want a nonempty input               */
  g_stats.cut++;
  g_stats.cut_bytes += Size - cursor;
  return (size_t)cursor;
}

/* ---------------------------------------------------------------------------------------------
   The run report

   The `[basalt] runs …` line a campaign ends with: how many tests ran, how many read past the end
   of their input, and what each option did. Its counts are kept in `g_stats` as the campaign goes.
   --------------------------------------------------------------------------------------------- */

/* The campaign's buffer statistics, on stderr. Called from two disjoint exits — `atexit` for the
   `-runs`-exhausted path, and the failure path below, which `abort()`s past `atexit` handlers.
   Printed from C rather than returned to Lean because a `String`-returning extern is the one shape
   of this bridge that gets the `BaseIO` ABI wrong silently. */
static void basalt_fuzz_report_stats(void) {
  if (!g_stats.runs && !g_stats.random) return;   /* libFuzzer exited before a test (`-help=1`) */
  fprintf(stderr, "[basalt] runs %llu", (unsigned long long)(g_stats.runs + g_stats.random));
  if (g_hy.cfg.on) fprintf(stderr, " (%llu in random rounds)", (unsigned long long)g_stats.random);
  fprintf(stderr, ", starved %llu (max deficit %llu B)", (unsigned long long)g_stats.starved,
          (unsigned long long)g_stats.max_deficit);
  if (g_trunc)
    fprintf(stderr, "; truncated %llu inputs, %.1f bytes each on average",
            (unsigned long long)g_stats.cut,
            g_stats.cut ? (double)g_stats.cut_bytes / (double)g_stats.cut : 0.0);
  fprintf(stderr, "\n");
}

/* ---------------------------------------------------------------------------------------------
   The custom mutator

   libFuzzer calls `LLVMFuzzerCustomMutator` in place of its own mutations, before each test of a
   mutated input. Basalt's options act there; unless one supplies the input itself (a hybrid
   campaign handing over a seed), the call ends in libFuzzer's default suite.
   --------------------------------------------------------------------------------------------- */

/* This replaces libFuzzer's mutator: a hybrid campaign's share first (`basalt_hy_mutate`), then
   truncation under `--truncate`, then libFuzzer's default suite.

   `Seed` is libFuzzer's own PRNG output and is unused.

   The visibility attribute is load-bearing: libFuzzer finds this by
   `dlsym(RTLD_DEFAULT, "LLVMFuzzerCustomMutator")`, so under the hidden-visibility default the
   symbol stays `private external`, the lookup fails silently, and the campaign runs the default
   mutators untruncated. `fuzz-run/build.sh` checks the linked binary exports it. */
__attribute__((visibility("default")))
size_t LLVMFuzzerCustomMutator(uint8_t *Data, size_t Size, size_t MaxSize, unsigned Seed) {
  (void)Seed;
  /* A hybrid campaign may take the call: to idle in a random round, or to hand over a seed. */
  if (g_hy.cfg.on) {
    size_t hy = basalt_hy_mutate(Data, Size, MaxSize);
    if (hy) return hy;
  }
  if (g_trunc) Size = basalt_truncate(Data, Size);
  return LLVMFuzzerMutate(Data, Size, MaxSize);
}

/* ---------------------------------------------------------------------------------------------
   Running a test

   libFuzzer calls `LLVMFuzzerTestOneInput` once per input. It runs the property on the input
   through the Lean callback, counts the run, and answers libFuzzer: `0` to consider the input for
   its corpus, `-1` to reject it (a discard), and, on a failure, an `abort()` that has libFuzzer
   save the input as an artifact. In a hybrid campaign's random round `basalt_hy_random_test` runs
   instead, and always answers `-1`: the input is not its test.
   --------------------------------------------------------------------------------------------- */

/* Apply a Lean `ByteArray -> IO UInt8` callback to a copy of libFuzzer's buffer; the code it returns. */
static uint8_t basalt_apply(lean_object *f, const uint8_t *Data, size_t Size) {
  lean_object *arr = lean_alloc_sarray(1, Size, Size);
  memcpy(lean_sarray_cptr(arr), Data, Size);
  lean_inc(f);                                        /* apply consumes the function object   */
  lean_object *res = lean_apply_2(f, arr, lean_io_mk_world());
  if (!lean_io_result_is_ok(res)) {
    /* An exception -- this signals a broken harness, so end the campaign. */
    lean_io_result_show_error(res);
    lean_dec(res);
    basalt_fuzz_die("the property raised an exception");
  }
  uint8_t code = (uint8_t)lean_unbox(lean_io_result_get_value(res));
  lean_dec(res);
  return code;
}

/* A random round's test, in place of a run of libFuzzer's buffer. */
static int basalt_hy_random_test(const uint8_t *Data, size_t Size) {
  /* The callback ignores the buffer, draws its test at `RecordGen`, and, if it passes, calls
     `basalt_hybrid_judge`, which sets `g_hy.judged`. */
  g_hy.judged.fresh = 0;
  uint8_t code = basalt_apply(g_hy.cfg.run_random, Data, Size);
  g_stats.random++;
  if (g_cov.first) basalt_cov_accumulate();
  if (code == 1) {
    /* The Lean side reported it and saved the recorded bytes. Exit past libFuzzer: its exit hook
       would save the buffer in hand as the crash, and that buffer is not this test's input. */
    basalt_cov_dump();
    basalt_fuzz_report_stats();
    fflush(NULL);
    _exit(77);
  }
  basalt_hy_step(g_hy.judged.fresh != 0, g_hy.judged.len);
  /* Not this test's input: libFuzzer must neither keep the buffer nor learn from its coverage. */
  return -1;
}

/* Libfuzzer harness -- called by libFuzzer loop during testing.
   Failure model follows bolero (lib/bolero-libfuzzer): the Lean closure prints the counterexample,
   returns code 1, and we abort(). libFuzzer's signal handler then saves the crashing input as an
   artifact (reproduce with `basalt-fuzz replay`) and exits with its error code. */
int LLVMFuzzerTestOneInput(const uint8_t *Data, size_t Size) {
  if (g_hy.cfg.on && g_hy.round.started && g_hy.round.mode == HY_RANDOM)
    return basalt_hy_random_test(Data, Size);
  g_cursor = 0;
  uint8_t code = basalt_apply(g_run, Data, Size);

  g_stats.runs++;
  if (g_cov.first) basalt_cov_accumulate();
  if (g_cursor > Size) {
    g_stats.starved++;
    if (g_cursor - Size > g_stats.max_deficit) g_stats.max_deficit = g_cursor - Size;
  }
  if (g_trunc) basalt_after_run(Data, Size);
  if (g_hy.cfg.on && g_hy.round.started) {
    size_t fresh = 0;
    if (code != 2) {                      /* libFuzzer ignores a rejected run's features too  */
      basalt_feat_read();
      fresh = basalt_feat_mark(g_hy.map.seen);
    }
    basalt_hy_step(fresh != 0, g_cursor);
  }

  if (code == 1) {
    basalt_cov_dump();                                /* abort() skips the atexit handlers     */
    basalt_fuzz_report_stats();
    fflush(NULL);                                     /* the Lean side flushed its own handles */
    abort();                                          /* property failed → libFuzzer saves it */
  }
  return (code == 2) ? -1 : 0;    /* discard → not added to the corpus (LLVM >= 12; the legacy
                                     driver ignores the code) */
}

/* ---------------------------------------------------------------------------------------------
   Starting a campaign

   `basalt_fuzz_go`, the bridge's entry from Lean (`goImpl`, `Runner.lean`): arm the options, then
   hand libFuzzer's driver the command line.
   --------------------------------------------------------------------------------------------- */

/* Called from Lean's `main` via @[extern]. Stores the closure and hands control to libFuzzer.
   Returns only if the campaign completes without a failure (a failure aborts the process). */
LEAN_EXPORT lean_object *basalt_fuzz_go(lean_object *run, lean_object *argv, uint8_t truncate) {
  g_run = run;
  g_trunc = truncate;
  atexit(basalt_fuzz_report_stats);                /* the `-runs`-exhausted path exits here */
  if (g_hy.cfg.on) {
    basalt_feat_init();
    g_hy.map.seen = calloc(g_feat.n, 1);
    g_hy.map.fresh = calloc(g_feat.n, 1);
    if (!g_hy.map.seen || !g_hy.map.fresh)
      basalt_fuzz_die("out of memory for the hybrid campaign's coverage map");
  }
  basalt_cov_init();

  /* `av` and its strings are deliberately never freed: the driver may rewrite both `argc` and `av`
     as it consumes its own flags, so the pointers we would free are not the ones we allocated. */
  size_t n = lean_array_size(argv);
  char **av = (char **)malloc((n + 2) * sizeof(char *));
  if (!av) basalt_fuzz_die("out of memory building the fuzzer command line");
  av[0] = strdup("basalt-fuzz");
  for (size_t i = 0; i < n; i++)
    av[i + 1] = strdup(lean_string_cstr(lean_array_get_core(argv, i)));
  for (size_t i = 0; i < n + 1; i++)
    if (!av[i]) basalt_fuzz_die("out of memory building the fuzzer command line");
  av[n + 1] = NULL;
  int argc = (int)n + 1;

  BASALT_FUZZER_RUN_DRIVER(&argc, &av, LLVMFuzzerTestOneInput);

  lean_dec(g_run);
  g_run = NULL;
  lean_dec(argv);
  return lean_io_result_mk_ok(lean_box(0));
}
