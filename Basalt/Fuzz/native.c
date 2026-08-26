#include <lean/lean.h>
#include <stdint.h>
#include <string.h>
#include <stdlib.h>

/* libFuzzer's driver. clang 11 exposes no C entry LLVMFuzzerRunDriver, so we call the C++ symbol
   fuzzer::FuzzerDriver by its mangled name (verified present in libclang_rt.fuzzer_no_main). */
extern int _ZN6fuzzer12FuzzerDriverEPiPPPcPFiPKhmE(
    int *argc, char ***argv, int (*cb)(const uint8_t *, size_t));

static lean_object *g_run = NULL;   /* the Lean closure `ByteArray -> IO UInt8`, held for the run */

/* Failure model follows bolero (lib/bolero-libfuzzer): the Lean closure prints the counterexample,
   returns code 1, and we abort(). libFuzzer's signal handler then saves the crashing input as an
   artifact (reproduce with `basalt-fuzz replay`) and exits with its error code. This is the proven
   in-process libFuzzer contract; the campaign result is the exit code + artifact, not a value
   returned to Lean (see FUZZING-DESIGN.md for the subprocess model that would return one). */
int LLVMFuzzerTestOneInput(const uint8_t *Data, size_t Size) {
  lean_object *arr = lean_alloc_sarray(1, Size, Size);
  memcpy(lean_sarray_cptr(arr), Data, Size);

  lean_inc(g_run);                                    /* apply consumes the function object   */
  lean_object *act = lean_apply_1(g_run, arr);        /* : IO UInt8   (consumes arr)          */
  lean_object *res = lean_apply_1(act, lean_io_mk_world());

  uint8_t code = 2;                                   /* default: discard                     */
  if (lean_io_result_is_ok(res)) code = lean_unbox(lean_io_result_get_value(res));
  else lean_io_result_show_error(res);
  lean_dec(res);

  if (code == 1) abort();                             /* property failed → libFuzzer saves it */
  return (code == 2) ? -1 : 0;                        /* discard → not added to corpus        */
}

/* Called from Lean's `main` via @[extern]. Stores the closure and hands control to libFuzzer.
   Returns only if the campaign completes without a failure (a failure aborts the process). */
LEAN_EXPORT lean_object *basalt_fuzz_go(lean_object *run, lean_object *argv, lean_object *w) {
  (void)w;
  g_run = run;

  size_t n = lean_array_size(argv);
  char **av = (char **)malloc((n + 2) * sizeof(char *));
  av[0] = strdup("basalt-fuzz");
  for (size_t i = 0; i < n; i++)
    av[i + 1] = strdup(lean_string_cstr(lean_array_get_core(argv, i)));
  av[n + 1] = NULL;
  int argc = (int)n + 1;

  _ZN6fuzzer12FuzzerDriverEPiPPPcPFiPKhmE(&argc, &av, LLVMFuzzerTestOneInput);

  lean_dec(g_run);
  lean_dec(argv);
  return lean_io_result_mk_ok(lean_box(0));
}
