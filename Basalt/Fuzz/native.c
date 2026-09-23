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
   mutation starts from the extended form.

   fuzz-run/README.md gives the design and some preliminary experimental data.
   --------------------------------------------------------------------------------------------- */

static int g_grow = 0;

/* If the last run reported a deficit, it is stored in `g_last_run_deficit`. That run's buffer
   is stored in `g_short`. The custom mutator checks if the last run had a deficit, and if
   the to-be mutated buffer is the same as last one, in which case it will zero-extend that
   buffer before mutating it. */
static uint32_t g_last_run_deficit = 0;

static struct {
  uint8_t *buf;
  size_t   cap;               /* allocated, never shrunk; see `basalt_fuzz_record_short`        */
  size_t   size;
} g_short;

/* Stats about the fuzzing run. */
static struct {
  uint64_t runs;
  uint64_t starved;           /* runs that read past the end of their buffer                    */
  uint32_t max_deficit;       /* how far off `-max_len` is, if it is                            */
  uint64_t grew;
  uint64_t cap_blocked;       /* wanted more but was already at `-max_len`                      */
} g_stats;

/* Called from Lean at the conclusion of a single property test run to note whether the run
   demanded more bytes than were available (so deficit is non-zero). Called while
   `LLVMFuzzerTestOneInput` is still on the stack, so `g_last_run_deficit` is the current run's. */
LEAN_EXPORT lean_object *basalt_fuzz_note_deficit(uint32_t deficit) {
  g_stats.runs++;
  if (deficit) {
    g_stats.starved++;
    if (deficit > g_stats.max_deficit) g_stats.max_deficit = deficit;
    if (g_grow) g_last_run_deficit = deficit;         /* no slot is maintained with `--grow` off      */
  }
  return lean_box(0);                               /* Unit */
}

/* Called from LLVMFuzzerTestOneInput at the conclusion of the Lean function's property test
   run in the case that there was a deficit. This function makes a copy of the input, which
   a subsequent custom mutator call will check, to make sure that it is zero-extending
   the right buffer. `g_last_run_deficit` is already set; this pairs it with its bytes, or retires it
   if that cannot be done. */
static void basalt_fuzz_record_short(const uint8_t *Data, size_t Size) {
  if (Size > g_short.cap) {
    size_t cap = g_short.cap ? g_short.cap : 64;
    while (cap < Size) cap *= 2;
    uint8_t *p = (uint8_t *)realloc(g_short.buf, cap);
    if (!p) {
      g_last_run_deficit = 0;      /* no growth, so can't zero-extend the deficit buffer. */
      return;
    }
    g_short.buf = p;
    g_short.cap = cap;
  }
  if (Size) memcpy(g_short.buf, Data, Size);
  g_short.size = Size;
}

/* Whether `Data` is the input the slot's deficit was measured on. */
static int basalt_fuzz_slot_matches(const uint8_t *Data, size_t Size) {
  return Size == g_short.size && (Size == 0 || memcmp(Data, g_short.buf, Size) == 0);
}

/* The campaign's buffer statistics, on stderr. Called from two disjoint exits — `atexit` for the
   `-runs`-exhausted path, and the failure path below, which `abort()`s past `atexit` handlers.
   Printed from C rather than returned to Lean because a `String`-returning extern is the one shape
   of this bridge that gets the `BaseIO` ABI wrong silently (see `basalt_fuzz_note_deficit`). */
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

/* This replaces libFuzzer's mutator. If we are in --grow mode, and the prior run
   experienced a deficit, and did so when using the provided `Data` buffer, then this code
   will grow buffer (not exceeding its `MaxSize`) and zero-extend its contents up to the
   deficit, prior to mutating. If there was no deficit or we were not in --grow
   mode, we go straight to mutation, which is just the default behavior.

   `Seed` is libFuzzer's own PRNG output and is unused: the tail is determined, not chosen.

   The visibility attribute is load-bearing: libFuzzer finds this by
   `dlsym(RTLD_DEFAULT, "LLVMFuzzerCustomMutator")`, so under the hidden-visibility default the
   symbol stays `private external`, the lookup fails silently, and the campaign runs the default
   mutators as if `--grow` had never been asked for. `fuzz-run/build.sh` checks the linked binary
   exports it. */
__attribute__((visibility("default")))
size_t LLVMFuzzerCustomMutator(uint8_t *Data, size_t Size, size_t MaxSize, unsigned Seed) {
  (void)Seed;
  size_t want = g_last_run_deficit;
  if (g_grow && want && basalt_fuzz_slot_matches(Data, Size)) {
    g_last_run_deficit = 0;                          /* one growth per observation                  */
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

/* Libfuzzer harness -- called by libFuzzer loop during testing.
   Failure model follows bolero (lib/bolero-libfuzzer): the Lean closure prints the counterexample,
   returns code 1, and we abort(). libFuzzer's signal handler then saves the crashing input as an
   artifact (reproduce with `basalt-fuzz replay`) and exits with its error code. */
int LLVMFuzzerTestOneInput(const uint8_t *Data, size_t Size) {
  g_last_run_deficit = 0;                    /* `basalt_fuzz_note_deficit` sets it if this run runs short */
  lean_object *arr = lean_alloc_sarray(1, Size, Size);
  memcpy(lean_sarray_cptr(arr), Data, Size);

  lean_inc(g_run);                                    /* apply consumes the function object   */
  /* Run the target Lean function */
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

  /* If there was a deficit, save the offending buffer. Will be checked by the custom mutator. */
  if (g_last_run_deficit) basalt_fuzz_record_short(Data, Size);

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
