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
   (`BASALT_COV_OUT` and the `io-cov` backend); truncation (`--truncate`); the run report; the custom
   mutator; running a test; and starting a campaign. */
#include <lean/lean.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

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
   Truncation (`--truncate`)

   Before libFuzzer mutates the input it has just run, the input is cut to the bytes its run read,
   so that the mutation lands on bytes the run used. The cut input runs exactly as before, since
   `readByte` reads `0` past the end. Only the input just run is cut: an input libFuzzer picks from
   its corpus to start a mutation chain has no run at hand to say how much of it was read.
   --------------------------------------------------------------------------------------------- */

static int g_trunc;           /* `--truncate`                                                    */

static struct {
  uint64_t runs;
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
  if (!g_stats.runs) return;
  fprintf(stderr, "[basalt] runs %llu, starved %llu (max deficit %llu B)",
          (unsigned long long)g_stats.runs, (unsigned long long)g_stats.starved,
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
   mutated input; Basalt's options act there, and the call ends in libFuzzer's default suite.
   --------------------------------------------------------------------------------------------- */

/* This replaces libFuzzer's mutator: truncate under `--truncate`, then libFuzzer's default suite.

   `Seed` is libFuzzer's own PRNG output and is unused.

   The visibility attribute is load-bearing: libFuzzer finds this by
   `dlsym(RTLD_DEFAULT, "LLVMFuzzerCustomMutator")`, so under the hidden-visibility default the
   symbol stays `private external`, the lookup fails silently, and the campaign runs the default
   mutators untruncated. `fuzz-run/build.sh` checks the linked binary exports it. */
__attribute__((visibility("default")))
size_t LLVMFuzzerCustomMutator(uint8_t *Data, size_t Size, size_t MaxSize, unsigned Seed) {
  (void)Seed;
  if (g_trunc) Size = basalt_truncate(Data, Size);
  return LLVMFuzzerMutate(Data, Size, MaxSize);
}

/* ---------------------------------------------------------------------------------------------
   Running a test

   libFuzzer calls `LLVMFuzzerTestOneInput` once per input. It runs the property on the input
   through the Lean callback, counts the run, and answers libFuzzer: `0` to consider the input for
   its corpus, `-1` to reject it (a discard), and, on a failure, an `abort()` that has libFuzzer
   save the input as an artifact.
   --------------------------------------------------------------------------------------------- */

/* Libfuzzer harness -- called by libFuzzer loop during testing.
   Failure model follows bolero (lib/bolero-libfuzzer): the Lean closure prints the counterexample,
   returns code 1, and we abort(). libFuzzer's signal handler then saves the crashing input as an
   artifact (reproduce with `basalt-fuzz replay`) and exits with its error code. */
int LLVMFuzzerTestOneInput(const uint8_t *Data, size_t Size) {
  g_cursor = 0;
  lean_object *arr = lean_alloc_sarray(1, Size, Size);
  memcpy(lean_sarray_cptr(arr), Data, Size);

  lean_inc(g_run);                                    /* apply consumes the function object   */
  /* res : IO UInt8; Lean function applied to the world token; consumes arr. */
  lean_object *res = lean_apply_2(g_run, arr, lean_io_mk_world());

  uint8_t code;
  if (lean_io_result_is_ok(res)) {
    code = (uint8_t)lean_unbox(lean_io_result_get_value(res));
    lean_dec(res);
  } else {
    /* An exception -- this signals a broken harness, so end the campaign. */
    lean_io_result_show_error(res);
    lean_dec(res);
    basalt_fuzz_die("the property raised an exception");
  }

  g_stats.runs++;
  if (g_cov.first) basalt_cov_accumulate();
  if (g_cursor > Size) {
    g_stats.starved++;
    if (g_cursor - Size > g_stats.max_deficit) g_stats.max_deficit = g_cursor - Size;
  }
  if (g_trunc) basalt_after_run(Data, Size);

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
