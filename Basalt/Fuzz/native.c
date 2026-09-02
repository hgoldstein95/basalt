/*
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All rights reserved.
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

static lean_object *g_run = NULL;   /* the Lean closure `ByteArray -> IO UInt8`, held for the run */

__attribute__((noreturn)) static void basalt_fuzz_die(const char *what) {
  fprintf(stderr, "[basalt] fatal: %s\n", what);
  fflush(NULL);
  exit(1);
}

/* Failure model follows bolero (lib/bolero-libfuzzer): the Lean closure prints the counterexample,
   returns code 1, and we abort(). libFuzzer's signal handler then saves the crashing input as an
   artifact (reproduce with `basalt-fuzz replay`) and exits with its error code. */
int LLVMFuzzerTestOneInput(const uint8_t *Data, size_t Size) {
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

  if (code == 1) {
    fflush(NULL);                                     /* the Lean side flushed its own handles */
    abort();                                          /* property failed → libFuzzer saves it */
  }
  return (code == 2) ? -1 : 0;    /* discard → not added to the corpus (LLVM >= 12; the legacy
                                     driver ignores the code) */
}

/* Called from Lean's `main` via @[extern]. Stores the closure and hands control to libFuzzer.
   Returns only if the campaign completes without a failure (a failure aborts the process). */
LEAN_EXPORT lean_object *basalt_fuzz_go(lean_object *run, lean_object *argv, lean_object *w) {
  (void)w;
  g_run = run;

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
