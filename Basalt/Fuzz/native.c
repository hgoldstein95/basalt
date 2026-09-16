/*
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Michael Hicks
*/
#include <lean/lean.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

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

/* ---------------------------------------------------------------------------------------------
   Buffer growth (`--grow`, off by default)

   A generator can outrun its buffer, and `Basalt.Fuzz.readByte` gives it `0` past the end. Those
   zeros are invisible to the fuzzer: not being in the input, no byte mutator can reach the positions
   that produced them. `--grow` materializes them — a run reports how far it overshot, and the next
   mutation of *those same bytes* starts from the extended form, which decodes to the same value
   because reading a stored `0` is reading past the end.

   fuzz-run/README.md owns the design, the libFuzzer facts that bound it, and the measurement — which
   does not support growth helping, hence the default.
   --------------------------------------------------------------------------------------------- */

static int g_grow = 0;

/* The one starved input growth may act on, held by value because identity is the whole question (see
   `basalt_fuzz_slot_matches`). `deficit` is nonzero exactly while the slot holds a live request;
   `pending` carries one from `basalt_fuzz_note` to the caller that has the bytes to go with it. */
static struct {
  uint8_t *buf;
  size_t   cap;               /* allocated, never shrunk; see `basalt_fuzz_record_short`        */
  size_t   size;
  uint32_t deficit;
  uint32_t pending;
} g_short;

static struct {
  uint64_t runs;
  uint64_t starved;           /* runs that read past the end of their buffer                    */
  uint32_t max_deficit;       /* how far off `-max_len` is, if it is                            */
  uint64_t grew;
  uint64_t cap_blocked;       /* wanted more but was already at `-max_len`                      */
} g_stats;

/* The deficit's only route from Lean to C: `FuzzGen`'s cursor computes it (`Basalt/Fuzz/Core.lean`),
   nothing on this side can derive it, and the callback's return is already spoken for by the outcome
   code. Called once per input while `LLVMFuzzerTestOneInput` is still on the stack, so `pending` is
   the current run's when the caller pairs it with the bytes.

   A `BaseIO` extern takes no world token and returns its value *unwrapped*: no
   `lean_io_result_mk_ok`, unlike `basalt_fuzz_go`'s `IO`. Wrapping it hands Lean a constructor where
   it expects the value; for a `String` return that meant reading an object header as a length and
   allocating until libFuzzer reported an out-of-memory. */
LEAN_EXPORT lean_object *basalt_fuzz_note(uint32_t deficit) {
  g_stats.runs++;
  if (deficit) {
    g_stats.starved++;
    if (deficit > g_stats.max_deficit) g_stats.max_deficit = deficit;
    g_short.pending = deficit;
  }
  return lean_box(0);                               /* Unit */
}

/* Take a copy of an input that ran short. Failing to allocate forgoes a growth, not the campaign.

   The capacity doubles rather than tracking `Size`, for a reason outside this file: this runs inside
   `LLVMFuzzerTestOneInput`, and libFuzzer counts mallocs against frees across the callback
   (`MallocFreeTracer`) to decide whether to run LeakSanitizer. Allocating on every growing input would
   answer "more mallocs than frees" continually and spend real time in leak checks that can find
   nothing, `buf` being a live global. */
static void basalt_fuzz_record_short(const uint8_t *Data, size_t Size, uint32_t deficit) {
  if (Size > g_short.cap) {
    size_t cap = g_short.cap ? g_short.cap : 64;
    while (cap < Size) cap *= 2;
    uint8_t *p = (uint8_t *)realloc(g_short.buf, cap);
    if (!p) return;
    g_short.buf = p;
    g_short.cap = cap;
  }
  if (Size) memcpy(g_short.buf, Data, Size);
  g_short.size = Size;
  g_short.deficit = deficit;
}

/* Whether `Data` is the input the slot's deficit was measured on, which growth demands: extending a
   *different* buffer is harmful rather than merely wasteful, since its tail is a region its own
   generator never asked for and the mutation that follows can land there. `Fuzzer::MutateAndTestOne`
   mutates one buffer in place for up to `-mutate_depth` iterations, so a mid-round call is on exactly
   the bytes that just ran, while iteration 0 of a round is on a freshly copied corpus unit and fails
   here as it must. The size test rejects those on one compare, so `memcmp` runs only on a tie. */
static int basalt_fuzz_slot_matches(const uint8_t *Data, size_t Size) {
  return g_short.deficit && Size == g_short.size
      && (Size == 0 || memcmp(Data, g_short.buf, Size) == 0);
}

/* The campaign's buffer statistics, on stderr. Called from two disjoint exits — `atexit` for the
   `-runs`-exhausted path, and the failure path below, which `abort()`s past `atexit` handlers.
   Printed from C rather than returned to Lean because a `String`-returning extern is the one shape
   of this bridge that gets the `BaseIO` ABI wrong silently (see `basalt_fuzz_note`). */
static void basalt_fuzz_report_stats(void) {
  if (!g_stats.runs) return;
  fprintf(stderr, "[basalt] runs %llu, starved %llu (max deficit %u B)",
          (unsigned long long)g_stats.runs, (unsigned long long)g_stats.starved,
          g_stats.max_deficit);
  if (g_grow)
    fprintf(stderr, ", grew %llu times, %llu at the -max_len cap\n",
            (unsigned long long)g_stats.grew, (unsigned long long)g_stats.cap_blocked);
  else
    fprintf(stderr, " [--grow off]\n");
}

/* Defining this replaces libFuzzer's whole default suite for the campaign (`Mutators` holds only
   `Mutate_Custom`), which is why every path ends in `LLVMFuzzerMutate` — the default suite,
   dictionaries and TORC included. Growth is a prefix to it, not an alternative: the zeros are
   materialized and then the extended buffer is mutated in the same call.

   The append is end-anchored on purpose. libFuzzer's own `Mutate_CopyPart` also extends, but inserts
   at a random offset, which re-aligns every subsequent `choose` and scrambles the whole generated
   value; appending leaves every existing draw meaning what it meant. Nothing holds the extension
   afterwards — `LLVMFuzzerMutate` may erase the tail it was just handed — and that is intended: one
   growth makes the tail visible to the suite, it does not legislate the result.

   `Seed` is libFuzzer's own PRNG output and is unused: the tail is determined, not chosen.

   The visibility attribute is load-bearing: libFuzzer finds this by
   `dlsym(RTLD_DEFAULT, "LLVMFuzzerCustomMutator")`, so under the hidden-visibility default the
   symbol stays `private external`, the lookup fails silently, and the campaign runs the default
   mutators as if `--grow` had never been asked for. `fuzz-run/build.sh` checks the linked binary
   exports it. */
__attribute__((visibility("default")))
size_t LLVMFuzzerCustomMutator(uint8_t *Data, size_t Size, size_t MaxSize, unsigned Seed) {
  (void)Seed;
  if (g_grow && basalt_fuzz_slot_matches(Data, Size)) {
    size_t want = g_short.deficit;
    g_short.deficit = 0;                          /* one growth per observation                  */
    if (Size >= MaxSize) {
      g_stats.cap_blocked++;                      /* -max_len is the ceiling on structure size   */
    } else {
      if (want > MaxSize - Size) want = MaxSize - Size;
      memset(Data + Size, 0, want);
      g_stats.grew++;
      Size += want;
    }
  }
  return LLVMFuzzerMutate(Data, Size, MaxSize);
}

/* Failure model follows bolero (lib/bolero-libfuzzer): the Lean closure prints the counterexample,
   returns code 1, and we abort(). libFuzzer's signal handler then saves the crashing input as an
   artifact (reproduce with `basalt-fuzz replay`) and exits with its error code. */
int LLVMFuzzerTestOneInput(const uint8_t *Data, size_t Size) {
  g_short.pending = 0;                                /* `basalt_fuzz_note` sets it if this run runs short */
  lean_object *arr = lean_alloc_sarray(1, Size, Size);
  memcpy(lean_sarray_cptr(arr), Data, Size);

  lean_inc(g_run);                                    /* apply consumes the function object   */
  /* : IO UInt8, applied to the world token; consumes arr. */
  lean_object *res = lean_apply_2(g_run, arr, lean_io_mk_world());

  uint8_t code;
  if (lean_io_result_is_ok(res)) {
    code = (uint8_t)lean_unbox(lean_io_result_get_value(res));
    lean_dec(res);
  } else {
    /* The Lean side answers every outcome with a code, so an exception here is a broken harness
       rather than a rejected input: end the campaign instead of reporting inputs no one ran. */
    lean_io_result_show_error(res);
    lean_dec(res);
    basalt_fuzz_die("the property raised an exception");
  }

  /* Only here are the bytes and their deficit both in hand. A discarded run (`code == 2`) is recorded
     too: it is still the buffer the next mid-round mutation will be handed. */
  if (g_grow && g_short.pending) basalt_fuzz_record_short(Data, Size, g_short.pending);

  if (code == 1) {
    basalt_fuzz_report_stats();                       /* abort() skips the atexit handler      */
    fflush(NULL);                                     /* the Lean side flushed its own handles */
    abort();                                          /* property failed → libFuzzer saves it */
  }
  return (code == 2) ? -1 : 0;    /* discard → not added to the corpus (LLVM >= 12; the legacy
                                     driver ignores the code) */
}

/* Called from Lean's `main` via @[extern]. Stores the closure and hands control to libFuzzer.
   Returns only if the campaign completes without a failure (a failure aborts the process). */
LEAN_EXPORT lean_object *basalt_fuzz_go(lean_object *run, lean_object *argv, uint8_t grow) {
  g_run = run;
  g_grow = grow;
  atexit(basalt_fuzz_report_stats);   /* the `-runs`-exhausted path exits here, not through Lean */

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
