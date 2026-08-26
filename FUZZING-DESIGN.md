# Coverage-Guided (Parametric) Fuzzing for Basalt

This document describes `FuzzGen`, an executable interpretation of Basalt's `Gen` that drives generators from a coverage-guided fuzzer (libFuzzer) instead of from a PRNG, together with the C bridge, build, and worked example that make it run. Everything here is implemented and validated on a machine whose details are in [Appendix A](#appendix-a-running-on-this-box). Support for more platforms is future work.

## 1. Goal

Basalt generators are terms polymorphic in their monad: `def myGen [Gen G] : G α`. The executable interpretations `IO`/`Plausible.Gen` today get their randomness from `RandomChoice.choose`. `FuzzGen` is a new executable interpretation whose `choose` results are decided by a **coverage-guided fuzzer**: libFuzzer proposes a byte buffer, `choose` reads bytes from it to make each choice, and libFuzzer observes which branches of the generator and the property-under-test execute and mutates the buffer to reach new coverage. This is *parametric fuzzing* — the fuzzer explores the parameter space of choices that defines a generator's output, using coverage rather than a distribution to decide where to look.

The extension point is the usual one: supply the component instances so that `Gen FuzzGen` follows by `inferInstance` (`Basalt/Gen.lean`). The work is one `RandomChoice FuzzGen` instance plus a small C bridge to libFuzzer.

## 2. What the reference implementations teach us

Three prior systems shaped the design.

- **bolero** (Rust → libFuzzer, https://github.com/camshaft/bolero) is the closest model. It excludes libFuzzer's `main` and calls `fuzzer::FuzzerDriver(&argc,&argv, LLVMFuzzerTestOneInput)` through a one-line shim, stashing the per-input test closure in a global slot. Its byte cursor reads past the end of the buffer by **zero-filling** (never erroring, never drawing randomly) — the determinism of *bytes → execution* is what makes coverage feedback meaningful. On failure it prints the `Debug`-rendered value and `abort()`s, so libFuzzer saves the crashing input as an artifact. Instrumentation is external compiler flags consumed by the linked runtime.
- **crowbar** (OCaml → AFL, https://github.com/stedolan/crowbar). Its `choose_int n` reads the *smallest* number of bytes covering a range and reduces modulo `n` — a mutation-friendly byte→choice map we reuse. On failure it `raise`s (crashes); AFL records the input. It has no shrinker of its own.
- **FuzzChick** (Coq → its own loop, https://github.com/QuickChick/QuickChick, `FuzzChick` branch). The most direct analogue: PBT + fuzzing inside a proof assistant. Its byte model is identical to ours (`choose_int`/`read_byte` off a buffer/file). Its *own* loop reports a counterexample **in process** (returns a structured `Result` and `Show`-prints it) because it owns the loop; the moment it delegates to `afl-fuzz` it reverts to **crash → the driver saves the input** like bolero and crowbar. This split — own-the-loop ⇒ can return a value; delegate-to-a-driver ⇒ crash + saved artifact — is the key lesson, and it is why our in-process-return option is the subprocess model in §9.

Common to all: coverage comes from compiler instrumentation feeding the fuzzer; a failing property is signalled by **crashing** and reported by printing the *decoded value* (not raw bytes); the raw input is the reproduction artifact. We follow this exactly.

## 3. Architecture overview

```
 ┌────────────────────── Lean executable (owns main) ───────────────────────┐
 │ main → Fuzz.go T argv                                                    │
 │   T : G TestOutcome         -- the property, polymorphic in the Gen G    │
 │   go builds  run : ByteArray → IO UInt8  and hands it to the bridge ──┐  │
 │                                                                       ▼  │
 │ RandomChoice FuzzGen          ┌──── C bridge (Basalt/Fuzz/native.c) ────┐│
 │  choose reads bytes from      │ basalt_fuzz_go(run, argv):              ││
 │  FuzzState.buffer/cursor,     │   store run in a global slot            ││
 │  zero-fill past end-of-buffer │   fuzzer::FuzzerDriver(argc,argv,cb)    ││
 │      ▲  pure Option state     │ cb = LLVMFuzzerTestOneInput(Data,Size):◀┼┼┐
 │ FuzzGen α =                   │   arr := ByteArray copy of (Data,Size)  │││
 │  StateT FuzzState Option      │   code := run arr        (: IO UInt8)   │││
 │                               │   1 → (Lean printed it) abort()         │││
 │                               │   2 → return -1 (discard) ; else 0      │││
 │                               └─────────────────────────────────────────┘││
 └──────────────────────────────────────────────────────────────────────────┘│
                    ▲                                                        │
                    └── libFuzzer runtime (libclang_rt.fuzzer_no_main) ──────┘
                        mutation loop + corpus + coverage counters;
                        on abort() saves the crashing input as an artifact;
                        counters come from SanitizerCoverage-instrumented .o
                        of the (Mathlib-free) property/generator closure.
```

Three parts: the **`FuzzGen`** interpretation (§4), the **C bridge** (§5), and the **build + instrumentation** (§6). A worked example (§8) exercises all three.

## 4. The `FuzzGen` interpretation (`Basalt/Fuzz/Core.lean`)

### 4.1 The monad

```lean
structure FuzzState where
  buffer : ByteArray
  cursor : Nat

abbrev FuzzGen (α : Type) := StateT FuzzState Option α
```

`FuzzGen` is a pure state monad over the byte buffer — no `IO`, so one fuzzer input is a *pure* function `ByteArray → TestOutcome` (§4.5), which makes the C boundary trivial and every input exactly reproducible from its bytes.

**Why `Option`.** `partial_fixpoint` (used by recursive generators) needs `∀ α, CCPO (FuzzGen α)`, which reduces to needing a least element ("bottom") of `Option (α × FuzzState)` for every `α`. The raw product `α × FuzzState` has no least element for an arbitrary `α`, so we must *adjoin* one; `Option` does exactly that, with `none` as ⊥ (a flat order, `Basalt.PlausibleGen`/`GenStats` use the same recipe with `Except`). `none` is a **compile-time device only**: a productive generator always yields `some`, and a divergent one loops (caught by libFuzzer's `-timeout`) rather than returning `none`. So the component instances are `Inhabited (FuzzGen α) := ⟨fun _ => none⟩` plus flat-order `PartialOrder`/`CCPO`/`MonoBind` on `Option`, after which `Gen FuzzGen := inferInstance`.

There is deliberately **no fuel and no failure case**: termination is the generator's concern via `partial_fixpoint`, with libFuzzer's `-timeout`/`-rss_limit_mb` as the backstop for a genuinely divergent generator. (Contrast `GenStats.StatGen`, which is fuel-guarded because it is a distribution-sampling interpretation, not a fuzzing one.)

### 4.2 `choose`: bytes → a value in `[lo, hi]`

`choose : (lo hi : Nat) → lo ≤ hi → m (ULift {x // lo ≤ x ∧ x ≤ hi})` is the only primitive. We read the *smallest* number of bytes that covers the range (crowbar's encoding) and reduce into the range:

```lean
def bytesFor (k : Nat) : Nat := (bitsFor k + 7) / 8   -- bytes to distinguish k outcomes

def readByte (s : FuzzState) : UInt8 × FuzzState :=    -- 0 past end-of-buffer (deterministic)
  let b := if s.cursor < s.buffer.size then s.buffer.get! s.cursor else 0
  (b, { s with cursor := s.cursor + 1 })

instance : RandomChoice FuzzGen where
  choose lo hi h := do
    let s ← get
    let range := hi - lo + 1
    let (raw, s') := readNat s (bytesFor range)        -- big-endian over readByte
    set s'
    let v := lo + raw % range
    pure (ULift.up ⟨min hi (max lo v), by omega⟩)
```

`choose` is **total** and **deterministic**: reading the fewest bytes per range keeps a tight, mutation-friendly map from corpus bytes to structural choices, and zero-filling past the end (rather than drawing from a PRNG) keeps *bytes → execution* deterministic, which is what coverage-guided mutation relies on. A saved input therefore reproduces a failure from its bytes alone.

### 4.3 Properties are `G TestOutcome`; composition is monadic `do`

```lean
inductive TestOutcome where
  | pass
  | fail (render : Unit → String)   -- lazily rendered counterexample
  | discard                         -- a precondition rejected this input
```

A *property* is any `G TestOutcome`. The leaves and single-input sugar:

```lean
def check     [Gen G] (b : Bool)                        : G TestOutcome  -- pass iff b
def checkWith [Gen G] (b : Bool) (render : Unit → String) : G TestOutcome  -- + counterexample text
def assume    [Gen G] (c : Bool)                        : G TestOutcome  -- discard unless c
def forAll [Repr α] [Gen G] (gen : G α) (p : α → Bool)  : G TestOutcome  -- = do a←gen; checkWith (p a) …
```

Because a property is monadic, **multiple/dependent inputs compose with ordinary `do`** (no special combinator), preconditions are a plain early `return .discard`, and one `check`/`checkWith` at the end yields the outcome, rendering a counterexample built from the drawn values:

```lean
def prop [Gen G] : G TestOutcome := do
  let t  ← genBST 1 15
  let k1 ← chooseNat 1 15
  let k2 ← chooseNat 1 15
  if k1 == k2 then return .discard          -- precondition, short-circuits
  let t' := (t.insertBuggy k1).insertBuggy k2
  checkWith t'.isBST (fun () => s!"t={reprStr t}, k1={k1}, k2={k2}")
```

These combinators are Basalt-new: Basalt proves *laws* about generators (`IsSoundAndComplete`, …) but has no runtime harness. Because the property is polymorphic in `G`, the *same* term runs at `Plausible.Gen` and `FuzzGen` — only the runner differs (Plausible's loop vs `Fuzz.go`).

### 4.4 Running one input (pure)

```lean
def runOne (T : FuzzGen TestOutcome) (bytes : ByteArray) : TestOutcome :=
  match T.run { buffer := bytes, cursor := 0 } with
  | some (outcome, _) => outcome
  | none              => .discard   -- the partial_fixpoint bottom; unreachable at runtime
```

This pure core is what the C bridge calls per input, and what `BasaltTest/Fuzz.lean` pins with `#guard_msgs` (deterministic byte→outcome tests that need no fuzzer and run in the default `lake build`).

## 5. The C bridge (`Basalt/Fuzz/native.c`, `Basalt/Fuzz/Runner.lean`)

Lean owns `main`; it calls `Fuzz.go`, which drives libFuzzer via `fuzzer::FuzzerDriver`. Because `go` runs from Lean `main`, the Lean runtime is already initialized when libFuzzer calls back — no init dance is needed.

### 5.1 Symbols and the per-input path

```c
extern int _ZN6fuzzer12FuzzerDriverEPiPPPcPFiPKhmE(          // fuzzer::FuzzerDriver, mangled
    int *argc, char ***argv, int (*cb)(const uint8_t *, size_t));
static lean_object *g_run = NULL;                            // Lean closure ByteArray -> IO UInt8

int LLVMFuzzerTestOneInput(const uint8_t *Data, size_t Size) {
  lean_object *arr = lean_alloc_sarray(1, Size, Size);       // marshal input into a Lean ByteArray
  memcpy(lean_sarray_cptr(arr), Data, Size);
  lean_inc(g_run);                                           // apply consumes the function object
  lean_object *act = lean_apply_1(g_run, arr);               // : IO UInt8 (consumes arr)
  lean_object *res = lean_apply_1(act, lean_io_mk_world());
  uint8_t code = 2;
  if (lean_io_result_is_ok(res)) code = lean_unbox(lean_io_result_get_value(res));
  lean_dec(res);
  if (code == 1) abort();                                    // failure → libFuzzer saves artifact
  return (code == 2) ? -1 : 0;                               // discard → not added to corpus
}
```

`basalt_fuzz_go(run, argv, world)` stores `run` in `g_run`, synthesizes an `argv` (`argv[0]` + forwarded flags), and calls `FuzzerDriver`. On the Lean side:

```lean
@[extern "basalt_fuzz_go"]
opaque goImpl (run : ByteArray → IO UInt8) (argv : Array String) : IO Unit

def go (T : FuzzGen TestOutcome) (argv : Array String := #[]) : IO Unit :=
  goImpl (fun bytes => runOneIO T bytes) argv
```

The bridge uses the mangled `fuzzer::FuzzerDriver` because clang 11 predates the stable C entry `LLVMFuzzerRunDriver` (§9, Appendix A). Written in C (not C++) to avoid the toolchain's C++ header issues; the mangled name is declared `extern`.

### 5.2 Failure handling (bolero model) and reporting

On a failing input, the Lean closure `runOneIO` prints the counterexample — the generated value rendered via `Repr`, plus the raw input bytes — flushes stdout/stderr (since the C side then `abort()`s, which skips flushing), and returns `1`. The bridge `abort()`s; libFuzzer's signal handler saves the crashing input under `-artifact_prefix` and exits with its error code (77).

This matches bolero/crowbar/FuzzChick-afl: **the human-readable report is the `Repr`-printed value; the raw-bytes artifact is the reproduction seed.** A developer consumes the artifact by *replaying* it — `basalt-fuzz replay <property> <file>` re-runs `runOne` on those bytes (no fuzzer), re-deriving and re-printing the same counterexample. Because `choose` zero-fills, the bytes alone reproduce the failure, so a `crash-<sha1>` file is a self-contained regression fixture.

Consequence: `go : IO Unit` — the campaign result is the exit code (nonzero ⇒ counterexample found and saved) plus the printed report, **not** a value returned to the Lean caller. Returning a value in-process is the subprocess model in §9. Call `go` once per process: libFuzzer's driver is not re-entrant.

### 5.3 Memory-management contract

From Lean's C ABI (`lean.h`): `lean_apply_*` consume both the function object and their arguments; boxed scalars (`lean_box`/`lean_unbox`) need no refcounting. Thus each iteration allocates a fresh `ByteArray` (consumed by the apply), `lean_inc`s the persistent `g_run` before applying it (so the apply doesn't free it), reads a boxed `UInt8`, and `lean_dec`s the `IO` result. No Lean object crosses a `fork` (default libFuzzer is single-process). `abort()` while Lean frames are live is fine — libFuzzer wants the crash, and the iteration is allocation-only with our print already flushed.

## 6. Build and instrumentation (`fuzz-run/build.sh`, `lakefile.toml`)

**Instrumentation.** Lean's default backend emits one C file per module (`.lake/build/ir/**.c`). SanitizerCoverage is a compile-time flag on that C. We instrument the modules whose branching the fuzzer should explore — the property and the generator/combinator code — by compiling their emitted C with `-fsanitize=fuzzer-no-link`. This closure is **Mathlib-free** (`RandomChoice`, `Gen`, `IO`, `Combinators`, `Fuzz.Core`, `Fuzz.Runner`, `BasaltFuzz.BST`, `BasaltFuzzMain` — none import Mathlib), which matters for two reasons: it is exactly the "property + generators" instrumentation scope, and it keeps the executable's link closure small (see below). The Lean runtime, Mathlib, and the rest of stdlib stay uninstrumented; partial coverage still guides libFuzzer.

**Why the closure must avoid Mathlib.** A `#eval` runs generators in the interpreter, but a *compiled executable* must link the native code of its entire import closure. Importing the `Basalt` umbrella would drag all of Mathlib's C into the link (impractical). The generator *definitions* need only `Gen`/`Combinators`; only their *proofs* need Mathlib/`SPMF`. So the executable imports the generator defs directly and never the umbrella, keeping Mathlib out of the link.

**Linking.** `fuzz-run/build.sh` compiles the closure's `.c` with the sancov flag, compiles `native.c`, and links them with the libFuzzer runtime:

```
leanc <objs> native.o -fsanitize=fuzzer-no-link \
  -l:libclang_rt.fuzzer_no_main-x86_64.a -lstdc++
```

We link `fuzzer_no_main` (we provide `LLVMFuzzerTestOneInput` and call the driver ourselves) plus the C++ runtime it needs. `lakefile.toml` gains one **non-default** `lean_lib` target (`BasaltFuzzMain`, globbing `BasaltFuzz.+`) so Lake elaborates and emits the C; the default `lake build` never touches it, so the test suite stays hermetic. This is the repo's first FFI and first native/link config, isolated to these targets.

## 7. Fuzzer configuration, corpus, reproduction

libFuzzer parses its own flags from the `argv` `go` forwards, so all controls are available: `-runs=N` / `-max_total_time=SECS` (bounded campaign), `-max_len=N` (input size), a positional directory for a seed/growing corpus, and `-artifact_prefix=DIR/` for where crashing inputs are written. Reproduction is `basalt-fuzz replay <property> <file>` on a saved `crash-<sha1>` (§5.2).

## 8. Worked example: a buggy BST (`BasaltFuzz/BST.lean`)

A self-contained, Mathlib-free demonstration: generate binary search trees, run insert operations, and check the BST invariant (`isBST` = the in-order traversal is strictly increasing).

- `genBST [Gen G] (lo hi) : G Tree` — pick a pivot, recurse on the disjoint subintervals; keys start at `1` so `Nat`'s truncating `x - 1` never wraps and every generated tree is strictly sorted.
- `Tree.insert` — correct (equal key is a no-op).
- `Tree.insertBuggy` — a subtle bug: a missing equal-key guard sends `k == x` into the right subtree, duplicating an existing key and breaking strict-sortedness.

Properties (registered in `BasaltFuzzMain.lean`): `bst-gen` and `bst-insert` (and the composed `bst-insert2`) must never fail; `bst-buggy-insert` and the composed `bst-buggy-insert2` do. libFuzzer finds a valid BST plus an already-present key (e.g. `(node leaf 1 leaf, 1)`) in tens of runs, prints it, and saves the artifact; the correct insert survives millions of runs with no false positive.

**A finding that shapes such demos:** coverage guidance is driven by **branch/structure** coverage, not by guessing wide scalars. Comparisons on Lean `Nat` compile to runtime calls in the uninstrumented `libleanshared` (`lean_nat_dec_eq`/`_lt`), so they emit **no** `-trace-cmp` signal — a magic-value equality on a `Nat` is not found faster than blind search. `UInt8`/`UInt32` comparisons in instrumented code *do* fire. So design bugs to be reachable via new *branches* (like the equal-key arm of `insertBuggy`), which the fuzzer explores well.

## 9. Alternatives and future work

- **In-process campaign result via a subprocess model.** Today a failure `abort()`s, so `go` can't return a `TestOutcome`. FuzzChick shows the trade-off: you can return a value only if you own the loop. The clean way to get both the proven per-process behavior *and* an in-process value is a subprocess model — a Lean parent spawns a libFuzzer child that aborts like bolero, and the parent reads the child's exit code / artifact / stderr to reconstruct a `TestOutcome`. Cost: a process boundary. (We prototyped an in-process `setjmp`/`longjmp` return path; it worked but left no artifact and had to `_exit` past libFuzzer's `atexit` handler, so it was dropped in favor of matching bolero.)
- **Support a more recent Clang/LLVM (≥ 12).** This is the most impactful cleanup. On LLVM ≥ 12 the bridge can call the stable C entry `LLVMFuzzerRunDriver` instead of the mangled `fuzzer::FuzzerDriver`, dropping the mangled-symbol declaration (and any C-vs-C++ concern). More importantly, a toolchain whose bundled `clang` actually runs here (the vendored LLVM-22 `clang` is glibc-broken on this box — Appendix A) would remove the `LEAN_CC` system-clang-11 wrapper and the hand-supplied `libstdc++` path entirely, making `fuzz-run/build.sh` portable. Worth also evaluating Lean's own LLVM backend as an instrumentation path.
- **Value-level shrinking.** v1 relies on libFuzzer's byte-level minimization (`-minimize_crash=1`) and reports the first counterexample. A Basalt value-level shrinker would give smaller, more readable counterexamples but is net-new (Basalt has no shrinker today).
- **Stop-on-first vs. run-to-completion mode.** A `--all`/`StopMode` flag could keep going past the first failure to collect multiple counterexamples or pass/fail statistics — either in-process (print + `return -1` to continue, accumulating) or libFuzzer-native (`-fork=N -ignore_crashes=1`, parent records every crash).
- **`trace-cmp`-friendly choice encoding.** Swap modulo reduction for a comparison-exposing encoding (bolero's Lemire scaling) so libFuzzer's comparison tracing helps on the choices it *can* see; note the `Nat`-comparison limitation in §8.
- **Broader instrumentation.** Instrument more of Basalt, or dependencies, when a target's coverage of interest lives outside the current closure.
- **Other engines.** The `RandomChoice FuzzGen` core is engine-agnostic (crowbar proves the same cursor drives AFL); an AFL or honggfuzz backend changes only the C bridge.

## Appendix A — Running on this box

Findings on the current machine (`clang 11.1.0`, Lean `4.33.0-rc2`, Amazon Linux 2):

- **libFuzzer runtime present:** `libclang_rt.fuzzer_no_main-x86_64.a` under `/usr/lib64/clang/11.1.0/lib/linux/`. System clang accepts `-fsanitize=fuzzer-no-link` and the `-fsanitize-coverage=*` flags.
- **No `LLVMFuzzerRunDriver` in clang 11** — only the mangled `fuzzer::FuzzerDriver` (`_ZN6fuzzer12FuzzerDriverEPiPPPcPFiPKhmE`), which the bridge declares and calls directly (as bolero does). The stable C entry arrived in LLVM 12 (§9).
- **The Lean-vendored clang (LLVM 22) does not run here** — it needs `GLIBC_2.27`/`2.29` this host lacks, so `leanc`'s default C compiler is broken. Builds set `LEAN_CC` to a wrapper around the system clang 11 that injects the vendored `libc++`/`gmp`/`uv` and rpath:
  ```bash
  #!/bin/bash
  exec /usr/bin/clang "$@" -L$TC/lib -Wl,-rpath,$TC/lib -Wl,-rpath,$TC/lib/lean
  ```
  where `$TC` is the toolchain root. The same wrapper is needed to build the Mathlib olean cache (`lake exe cache get`), which compiles C.
- **`libstdc++`** (needed by the libFuzzer C++ runtime) is not on the default link path; supply it with `-L/usr/lib/gcc/x86_64-redhat-linux/7`.

## Appendix B — Key source references

- Basalt: `Basalt/RandomChoice.lean` (`choose`), `Basalt/Gen.lean` (the `Gen` bundle + auto-instance), `Basalt/IO.lean` (`bitsFor`), `Basalt/PlausibleGen.lean`/`Basalt/GenStats.lean` (the flat-order `CCPO`/`MonoBind` recipe).
- This feature: `Basalt/Fuzz/Core.lean`, `Basalt/Fuzz/Runner.lean`, `Basalt/Fuzz/native.c`, `BasaltFuzz/BST.lean`, `BasaltFuzzMain.lean`, `BasaltTest/Fuzz.lean`, `fuzz-run/`.
- Prior art: bolero `lib/bolero-libfuzzer/src/{lib.rs,FuzzerAPI.cpp}`, `lib/bolero-generator/src/driver/bytes.rs`; crowbar `src/crowbar.ml` (`choose_int`, the AFL bridge); FuzzChick `src/Test.v` (`fuzzLoop`), `Fuzz/`, `src/quickChickLib.ml` (`choose_int`).
