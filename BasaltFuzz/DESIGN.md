<!--
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Michael Hicks
-->

# Coverage-Guided (Parametric) Fuzzing for Basalt

This document describes `FuzzGen`, an executable interpretation of Basalt's `Gen` that drives generators from a coverage-guided fuzzer (libFuzzer) instead of from a PRNG, together with the C bridge, build, and worked example that make it run. Everything here is implemented and validated on three platforms — macOS (arm64), Amazon Linux 2 (x86_64, the legacy clang-11 box), and Amazon Linux 2023 (x86_64, the modern clang-22 case) — spanning both a very old and a current Linux; [Appendix A](#appendix-a--platforms) covers what differs between them and how the build detects each difference.

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

These combinators are Basalt-new: Basalt proves *laws* about generators (`IsSoundAndComplete`, …) but has no runtime harness. Because the property is polymorphic in `G`, the *same* term runs at `Plausible.Gen` and `FuzzGen` — only the runner differs (a plain loop vs `Fuzz.go`). §5.4 makes that concrete: the executable ships all three backends.

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
extern int LLVMFuzzerRunDriver(                              // LLVM >= 12; the legacy spelling is
    int *argc, char ***argv, int (*cb)(const uint8_t *, size_t));   // fuzzer::FuzzerDriver, mangled
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

`basalt_fuzz_go(run, argv, world)` stores `run` in `g_run`, synthesizes an `argv` (`argv[0]` + forwarded flags), and calls the driver. On the Lean side:

```lean
@[extern "basalt_fuzz_go"]
opaque goImpl (run : ByteArray → IO UInt8) (argv : Array String) : IO Unit

def go (T : FuzzGen TestOutcome) (argv : Array String := #[]) : IO Unit :=
  goImpl (fun bytes => runOneIO T bytes) argv
```

The snippet shows the stable C entry `LLVMFuzzerRunDriver`, which the bridge calls wherever the runtime exposes it (LLVM ≥ 12 — the macOS path). Under `-DBASALT_FUZZ_LEGACY_DRIVER` it instead calls the mangled `fuzzer::FuzzerDriver`, for clang 11 and earlier, which predate the C entry; `fuzz-run/build.sh` picks between them by `nm`-probing the runtime archive (Appendix A). The file is C, not C++, so no C++ headers are involved either way — the mangled name is simply declared `extern`.

### 5.2 Failure handling (bolero model) and reporting

On a failing input, the Lean closure `runOneIO` prints the counterexample — the generated value rendered via `Repr`, plus the raw input bytes — flushes stdout/stderr (since the C side then `abort()`s, which skips flushing), and returns `1`. The bridge `abort()`s; libFuzzer's signal handler saves the crashing input under `-artifact_prefix` and exits with its error code (77).

This matches bolero/crowbar/FuzzChick-afl: **the human-readable report is the `Repr`-printed value; the raw-bytes artifact is the reproduction seed.** A developer consumes the artifact by *replaying* it — `basalt-fuzz replay <property> <file>` re-runs `runOne` on those bytes (no fuzzer), re-deriving and re-printing the same counterexample. Because `choose` zero-fills, the bytes alone reproduce the failure, so a `crash-<sha1>` file is a self-contained regression fixture.

Consequence: `go : IO Unit` — the campaign result is the exit code (nonzero ⇒ counterexample found and saved) plus the printed report, **not** a value returned to the Lean caller. Returning a value in-process is the subprocess model in §9. Call `go` once per process: libFuzzer's driver is not re-entrant.

### 5.3 Memory-management contract

From Lean's C ABI (`lean.h`): `lean_apply_*` consume both the function object and their arguments; boxed scalars (`lean_box`/`lean_unbox`) need no refcounting. Thus each iteration allocates a fresh `ByteArray` (consumed by the apply), `lean_inc`s the persistent `g_run` before applying it (so the apply doesn't free it), reads a boxed `UInt8`, and `lean_dec`s the `IO` result. No Lean object crosses a `fork` (default libFuzzer is single-process). `abort()` while Lean frames are live is fine — libFuzzer wants the crash, and the iteration is allocation-only with our print already flushed.

### 5.4 The non-fuzzing backends, and what the polymorphism buys

The property is polymorphic in `G` (§4.3), so the fuzzer is one interpretation among several rather than the harness's premise. `--backend=io` / `--backend=plausible` instantiate the *same* registry entry at `IO` or `Plausible.Gen` and run it in a plain loop. The measure of how load-bearing the polymorphism is: adding both backends needed **no new instance and no change to any property or generator** — `Gen IO` and `Gen Plausible.Gen` already followed by `inferInstance`. What it took was giving the registry a type that keeps the monad open,

```lean
def Property := (G : Type → Type) → [Gen G] → G TestOutcome   -- was: FuzzGen TestOutcome
```

plus a ~12-line `randomCampaign` loop and a flag. `Property`'s explicit `G` binder is the crux: the old registry type had already committed to `FuzzGen`, and a list of monomorphic properties cannot be re-instantiated after the fact.

All three backends share the failure contract of §5.2 (counterexample on stderr, a `runs : N (M discarded)` tally, exit 77), which is what makes their campaigns comparable. Two asymmetries are real and worth stating: `replay` is fuzz-only, because a saved artifact *is* a `FuzzGen` byte buffer and has no meaning as a PRNG state; and the run tally for the fuzz backend is kept in `runOneIO` rather than printed after `goImpl`, because libFuzzer's driver `exit()`s when `-runs` is exhausted and nothing after the call runs.

`fuzz-run/compare-backends.sh` measures time-to-first-counterexample across backends; `fuzz-run/README.md` records the numbers. The finding is that neither dominates, and which wins is a property of the *bug*: on the shallow BST bugs random search needs fewer runs and is 3–5× faster per run, while `BasaltFuzz/Staged.lean`'s `chain-n` — a bug behind `n` nested guards, so `256ⁿ` for a blind sampler but `≈ n·256` for one that banks each newly reached stage — is found by the fuzzer in ~1.2k runs at `n=4` and not at all by either random backend in 20M runs × 9 trials. This is the concrete argument for the interpretation-polymorphic design: the choice is per-bug, and it costs a flag rather than a rewrite.

## 6. Build and instrumentation (`fuzz-run/build.sh`, `lakefile.toml`)

**Instrumentation.** Lean's default backend emits one C file per module (`.lake/build/ir/**.c`). SanitizerCoverage is a compile-time flag on that C. We instrument the modules whose branching the fuzzer should explore — the property and the generator/combinator code — by compiling their emitted C with `-fsanitize=fuzzer-no-link`; `fuzz-run/build.sh`'s `MODULES` is the authoritative list, and none of it imports Mathlib. That matters for two reasons: it is exactly the "property + generators" instrumentation scope, and it keeps the executable's link closure small (see below). The Lean runtime, Mathlib, and the rest of stdlib stay uninstrumented; partial coverage still guides libFuzzer.

Plausible's `Gen`/`Random` are linked but deliberately **not** instrumented (`DEP_MODULES`): they are the `--backend=plausible` PRNG rather than code under test, and coverage over a PRNG's mixing steps is noise in libFuzzer's feedback.

**Why the closure must avoid Mathlib.** A `#eval` runs generators in the interpreter, but a *compiled executable* must link the native code of its entire import closure. Importing the `Basalt` umbrella would drag all of Mathlib's C into the link (impractical). The generator *definitions* need only `Gen`/`Combinators`; only their *proofs* need Mathlib/`SPMF`. So the executable imports the generator defs directly and never the umbrella, keeping Mathlib out of the link.

The same constraint governs how the Plausible backend is imported. `Basalt/PlausibleGen.lean` imports `Plausible.Gen`, not the `Plausible` umbrella: the umbrella pulls in the tactic frontend and deriving handlers, which the executable would then have to link. Plausible itself is a separate Lake package that does not depend on Mathlib, so the backend costs two extra object files and nothing more.

**Linking.** `fuzz-run/build.sh` compiles the closure's `.c` with the sancov flag, compiles `native.c`, and links them with the libFuzzer runtime:

```
leanc <objs> native.o <libFuzzer runtime> -lc++      # or -lstdc++ with a GNU toolchain
```

Both steps use `leanc` as the C driver, which supplies Lean's include path, clang resource headers, sysroot, and rpaths — the reason the script carries no hardcoded toolchain paths (Appendix A). We link `fuzzer_no_main`, not `fuzzer` (we provide `LLVMFuzzerTestOneInput` and call the driver ourselves), plus the C++ runtime libFuzzer needs. Note that the sancov flag appears only on the *compile* lines: it is compile-time instrumentation, and on the link line it additionally requests a ubsan dylib Lean's vendored clang does not ship.

`lakefile.toml` gains one **non-default** `lean_lib` target (`BasaltFuzzMain`, globbing `BasaltFuzz.+`) so Lake elaborates and emits the C. What is opt-in is the *executable*: the C emission, the sancov compile, and the native link happen only in `fuzz-run/build.sh`, so the default `lake build` needs no C toolchain and no libFuzzer runtime. Elaboration is a different matter — `BasaltTest/Fuzz.lean` imports `BasaltFuzz.BuggyBST` to pin its `genBST` against the proved one (§8), so that module *is* type-checked by `lake build`, which is deliberate: it is how a drift is caught. `BasaltFuzz.Staged` and `BasaltFuzzMain` are reached by neither, and only the `basalt-fuzz` CI workflow builds them. This is the repo's first FFI and first native/link config, isolated to these targets.

## 7. Fuzzer configuration, corpus, reproduction

libFuzzer parses its own flags from the `argv` `go` forwards, so all controls are available: `-runs=N` / `-max_total_time=SECS` (bounded campaign), `-max_len=N` (input size), a positional directory for a seed/growing corpus, and `-artifact_prefix=DIR/` for where crashing inputs are written. Reproduction is `basalt-fuzz replay <property> <file>` on a saved `crash-<sha1>` (§5.2).

## 8. Worked example: a buggy BST (`BasaltFuzz/BuggyBST.lean`)

A self-contained, Mathlib-free demonstration: generate binary search trees, run insert operations, and check the BST invariant (`isBST` = the in-order traversal is strictly increasing).

**Why this restates `BasaltExamples/BST` instead of importing and extending it.** The obvious factoring — import the proved example, add `insertBuggy`, done — is not available, and the reason is §6's link closure, not taste. `BasaltExamples/BST.lean` imports the `Basalt` umbrella (it needs `SPMF`, the laws, and `ennreal_to_real` for its three theorems), and `Basalt` → `Basalt.Basic` → `Basalt.SPMF` → `Basalt/SPMF/Core.lean` imports Mathlib. An executable links its whole import closure, so importing the example drags 1440 Mathlib modules (measured) into a binary whose instrumentation scope is supposed to be *the generator and the property* — against the ten first-party modules `build.sh`'s `MODULES` compiles today. Two smaller mismatches point the same way: the example's `Tree` is polymorphic in `α` where a fuzz target wants one monomorphic type, and its `isBST` is a `Prop` (what `sound_complete` is stated against) where a property needs a decidable `Bool`.

The real alternative is to factor the shared, Mathlib-free part — `Tree`, `genBST` — into a third module that both the example and this target import. That is a genuine improvement and is listed in §9; it is deferred because it edits a proof-carrying cookbook file to serve an opt-in executable. Until then the duplication is deliberate and fenced at `genBST`'s docstring: the copy is term-for-term the proved generator, and nothing but that comment says so.

- `genBST [Gen G] (lo hi) : G Tree` — pick a pivot, recurse on the disjoint subintervals; keys start at `1` so `Nat`'s truncating `x - 1` never wraps and every generated tree is strictly sorted.
- `Tree.insert` — correct (equal key is a no-op).
- `Tree.insertBuggy` — a subtle bug: a missing equal-key guard sends `k == x` into the right subtree, duplicating an existing key and breaking strict-sortedness.
- `Tree.delete` / `Tree.deleteBuggy` — the buggy `deleteMin` drops a subtree, so keys silently vanish while the output stays a *valid* BST. `isBST` cannot see this; the postcondition is a model comparison against `toList.erase`, which is the general lesson (an invariant check is weaker than a model).

Properties are registered in `BasaltFuzzMain.lean` and tabulated in `fuzz-run/README.md`; the `-buggy-` ones fail and the rest must not. libFuzzer finds a valid BST plus an already-present key (e.g. `(node leaf 1 leaf, 1)`) in tens of runs, prints it, and saves the artifact; the correct operations survive millions of runs with no false positive.

These bugs are all *shallow* — one unlucky draw exposes them — which is why `BasaltFuzz/Staged.lean` exists as a separate, synthetic target: a comparison between backends (§5.4) needs a bug where the search strategy actually matters.

**A finding that shapes such demos:** coverage guidance is driven by **branch/structure** coverage, not by guessing wide scalars. Do not write a demo bug behind a magic-value `Nat` equality: a 32-bit needle (`x == 0xDEADBEEF` over `chooseNat 0 4294967295`) is not found in 5M runs, with or without `-use_cmp`. Design bugs to be reachable via new *branches* instead (like the equal-key arm of `insertBuggy`), which the fuzzer explores well.

The reason is worth stating precisely, because the obvious explanation is wrong. `lean_nat_eq`/`_le` are `LEAN_ALWAYS_INLINE` with a small-scalar fast path, so they *do* inline into instrumented code and *do* emit `-trace-cmp` hooks (`__sanitizer_cov_trace_const_cmp8` is present in the BST object file). But the value the hook observes is a **tagged** Lean scalar, `2*n+1` — comparing `0x1BD5B7DDF`, not `0xDEADBEEF` — so the literal libFuzzer harvests into its table of recent compares never matches the bytes `choose` reads out of the input buffer. The signal fires and is useless. (Only boxed `Nat`s above the scalar range reach the genuinely uninstrumented `lean_nat_big_*` in `libleanshared`.) Fixing this is the `trace-cmp`-friendly-encoding item in §9.

## 9. Alternatives and future work

- **In-process campaign result via a subprocess model.** Today a failure `abort()`s, so `go` can't return a `TestOutcome`. FuzzChick shows the trade-off: you can return a value only if you own the loop. The clean way to get both the proven per-process behavior *and* an in-process value is a subprocess model — a Lean parent spawns a libFuzzer child that aborts like bolero, and the parent reads the child's exit code / artifact / stderr to reconstruct a `TestOutcome`. Cost: a process boundary. (We prototyped an in-process `setjmp`/`longjmp` return path; it worked but left no artifact and had to `_exit` past libFuzzer's `atexit` handler, so it was dropped in favor of matching bolero.)
- **~~Support a more recent Clang/LLVM (≥ 12)~~ — done (macOS and Amazon Linux 2023).** On both the vendored LLVM-22 `clang` runs natively, so the bridge calls the stable C entry `LLVMFuzzerRunDriver` and the build needs no `LEAN_CC` wrapper; `fuzz-run/build.sh` detects driver, runtime, and C++ library per platform (Appendix A). The `LEAN_CC` wrapper is now confirmed to be a property of *Amazon Linux 2's* old glibc, not of the design: AL2023 (glibc 2.34, clang 22) needs no wrapper, as predicted. Lean's own LLVM backend is still unevaluated as an instrumentation path.
- **A runtime built from source, and the skew it avoids.** macOS has no shipped `libclang_rt.fuzzer_no_main`, so `fuzz-run/get-libfuzzer.sh` builds one from compiler-rt (pinned by `LLVM_TAG`); the same path serves any Linux whose *only* system runtime is a different clang major than the one instrumenting (`ubuntu-latest`, clang 16 vs Lean's clang 22). This is where runtime/instrumentation skew would bite, so `fuzz-run/build.sh` treats a version-matched runtime as the goal: it prefers a system archive whose clang major equals the instrumenting clang's (from `$CC`'s `__clang_major__`, so it honors `LEAN_CC`), and otherwise builds from source pinned to that same major — matched by construction. `get-libfuzzer.sh` warns if its `LLVM_TAG` ever drifts from the instrumenting major. A mismatched system archive is used only as a last resort, with a warning, since `chain-4` is what would ultimately expose a skew that silently killed coverage feedback.
- **Value-level shrinking.** v1 relies on libFuzzer's byte-level minimization (`-minimize_crash=1`) and reports the first counterexample. A Basalt value-level shrinker would give smaller, more readable counterexamples but is net-new (Basalt has no shrinker today).
- **Stop-on-first vs. run-to-completion mode.** A `--all`/`StopMode` flag could keep going past the first failure to collect multiple counterexamples or pass/fail statistics — either in-process (print + `return -1` to continue, accumulating) or libFuzzer-native (`-fork=N -ignore_crashes=1`, parent records every crash).
- **`trace-cmp`-friendly choice encoding.** Swap modulo reduction for a comparison-exposing encoding (bolero's Lemire scaling) so libFuzzer's comparison tracing helps on the choices it *can* see. Note that the binding constraint measured in §8 is *tagging*, not instrumentation scope: the hooks fire but report `2*n+1`, so the harvested literals never match input bytes. An encoding change alone will not fix that — it needs the compared value and the buffered bytes to agree, e.g. by comparing on `UInt32`/`UInt8` (untagged in instrumented code) before widening to `Nat`.
- **Share one `Tree`/`genBST` between the example and the fuzz target.** §8's duplication would go away if the Mathlib-free part of `BasaltExamples/BST.lean` (the datatype and the generator) moved to a module both it and `BasaltFuzz/BuggyBST.lean` import, leaving only the proofs behind the `Basalt` umbrella. Then `BuggyBST` genuinely *extends* the proved generator: the term it fuzzes would be the same term, by construction rather than by a comment. Two things to settle first — the shared `Tree` must be monomorphic or the fuzz side must instantiate it, and `isBST` has to exist in both a `Prop` form for the proofs and a `Bool` form for the property (a `decide`-bridging lemma is the tidy version). Cost is an edit to a proof-carrying cookbook file, which is why it is not v1.
- **Broader instrumentation.** Instrument more of Basalt, or dependencies, when a target's coverage of interest lives outside the current closure.
- **Other engines.** The `RandomChoice FuzzGen` core is engine-agnostic (crowbar proves the same cursor drives AFL); an AFL or honggfuzz backend changes only the C bridge.

## Appendix A — Platforms

`fuzz-run/build.sh` builds with no arguments on the three platforms below. Five things vary between
platforms, and the script detects each one; every probe can be overridden from `fuzz-run/env.sh`
(git-ignored, sourced first), which `fuzz-run/env.example.sh` documents. Because the probes are
generic, a platform not listed here is *likely* to work — but only these three have been run.

| what varies | how it is resolved |
|---|---|
| C compile/link driver | `leanc`, which already knows Lean's include path, clang resource headers, sysroot, and rpaths (`CC`) |
| libFuzzer runtime | a toolchain `libclang_rt.fuzzer_no_main*.a` (any `.../lib/linux` legacy or `.../lib/<triple>` clang-≥14 dir, host-arch only) *whose clang major matches the instrumenting clang*, else the compiler-rt build in `fuzz-run/vendor/`, which is pinned to that major, else a mismatched system archive with a warning (`FUZZER_LIB_FLAGS`) |
| driver entry point | `nm` on the runtime archive: `LLVMFuzzerRunDriver` if present, else the mangled `fuzzer::FuzzerDriver` (`DRIVER_DEFINE`) |
| libc headers for `native.c` | the platform SDK's include dir on macOS, `/usr/include` on Linux, because `leanc`'s vendored clang has no libc in its sysroot (`BRIDGE_INCLUDES`) |
| C++ runtime | `-lc++` on macOS; on Linux the newest installed `libstdc++.so` named by full path, since a bare `-lstdc++` is dropped alongside `leanc`'s own `-lc++` (`CXXLIB_FLAGS`) |

Using `leanc` as the driver is what makes the script portable: the hand-supplied toolchain include
path and system-clang wrapper the Amazon Linux 2 box needed are now either detected or unnecessary.
The one thing `leanc` does *not* solve on Linux is the C++ runtime — it appends its own `-lc++`, so
the GNU libstdc++ that a toolchain-provided libFuzzer runtime needs has to be named by full path.

### macOS (arm64, macOS 15, Lean `4.33.0-rc2`)

- **Instrumentation works out of the box.** Lean's vendored clang (LLVM 22) is a native arm64 binary
  here and accepts `-fsanitize=fuzzer-no-link` on Lean's emitted C.
- **No libFuzzer runtime ships anywhere.** Apple's clang has only the `fuzzer` *header* directory
  (no `libclang_rt.fuzzer*`), and Lean's vendored clang ships only `libclang_rt.osx.a`. So a full
  `-fsanitize=fuzzer` link fails, and `get-libfuzzer.sh` builds `libFuzzerNoMain.a` from
  compiler-rt's standalone `lib/fuzzer` source instead — it is plain C++17 with its own `build.sh`,
  so this needs no LLVM checkout or CMake.
- **LLVM 22 has the stable C entry**, so the bridge calls `LLVMFuzzerRunDriver` and the mangled-name
  declaration is unused (the §9 cleanup, realized on this platform).
- **`native.c` needs libc headers explicitly.** `leanc` points `-isysroot` at the Lean toolchain
  (which has no libc) and suppresses the platform default, so Lean's own emitted C compiles but the
  bridge's `<string.h>` is not found; the build adds `-isystem $(xcrun --show-sdk-path)/usr/include`.
- **`-fsanitize=fuzzer-no-link` must not appear on the link line.** It is a compile-time flag, and
  at link time it also requests a ubsan dylib Lean's vendored clang does not ship.

### Amazon Linux 2 (x86_64, `clang 11.1.0`, Lean `4.33.0-rc2`)

- **libFuzzer runtime present:** `libclang_rt.fuzzer_no_main-x86_64.a` under `/usr/lib64/clang/11.1.0/lib/linux/` (on the script's search path). System clang accepts `-fsanitize=fuzzer-no-link` and the `-fsanitize-coverage=*` flags.
- **No `LLVMFuzzerRunDriver` in clang 11** — only the mangled `fuzzer::FuzzerDriver` (`_ZN6fuzzer12FuzzerDriverEPiPPPcPFiPKhmE`), which the bridge declares and calls directly (as bolero does) under `-DBASALT_FUZZ_LEGACY_DRIVER`. The archive probe selects this automatically; the stable C entry arrived in LLVM 12.
- **The Lean-vendored clang (LLVM 22) does not run here** — it needs `GLIBC_2.27`/`2.29` this host lacks, so `leanc`'s default C compiler is broken. Set `LEAN_CC` to a wrapper around the system clang 11 that injects the vendored `libc++`/`gmp`/`uv` and rpath:
  ```bash
  #!/bin/bash
  exec /usr/bin/clang "$@" -L$TC/lib -Wl,-rpath,$TC/lib -Wl,-rpath,$TC/lib/lean
  ```
  where `$TC` is `lean --print-prefix`. The same wrapper is needed to build the Mathlib olean cache (`lake exe cache get`), which compiles C.
- **`libstdc++`** (needed by the libFuzzer C++ runtime) is not on the default link path; set `CXXLIB_FLAGS="-L/usr/lib/gcc/x86_64-redhat-linux/7 -lstdc++"`.

### Amazon Linux 2023 (x86_64, `clang 22` / `compiler-rt22`, Lean `4.33.0-rc2`)

The "current Linux distribution" case, now built and validated. Toolchain: `dnf install clang22
compiler-rt22` for the system runtime, Lean via `elan`. It builds with **no `env.sh`** — every
difference from Amazon Linux 2 is handled by the script's detection — but three of those detections
had to be generalized past what the two original platforms exercised (all in `fuzz-run/build.sh`;
no source changed):

- **No `LEAN_CC` wrapper.** glibc 2.34 is new enough for Lean's vendored clang 22, so `leanc` runs
  unmodified. This is the AL2 hazard removed rather than replaced, as predicted.
- **Modern driver.** System clang 22 ships `LLVMFuzzerRunDriver`, so the archive probe takes the
  macOS branch (no `-DBASALT_FUZZ_LEGACY_DRIVER`), and instrumentation and runtime are the *same*
  clang 22 — the skew a mixed system-clang/Lean-clang box would have is absent here.
- **Runtime lives in a per-target-triple dir.** `libclang_rt.fuzzer_no_main.a` is at
  `/usr/lib/clang/22/lib/x86_64-amazon-linux-gnu/` (clang ≥ 14's layout, and note the name has *no*
  `-x86_64` suffix), not the legacy `.../lib/linux/`. The search now globs `.../lib/*` under each
  prefix, not just `.../lib/linux`.
- **`native.c` needs libc headers explicitly**, exactly as on macOS: `leanc`'s vendored clang points
  `-isysroot` at the Lean toolchain (no libc there), so `<string.h>` is not found without
  `-isystem /usr/include`. AL2 dodged this only because its `LEAN_CC` wrapper drove the *system*
  clang, whose default sysroot has `/usr/include`.
- **`libstdc++` must be named by full path, and be recent.** Two link-time surprises correct the
  Appendix-A guess that `CXXLIB_FLAGS` would need no override: a bare `-lstdc++` is silently dropped
  (leanc already appends `-lc++`, so lld never links a second C++ runtime by `-l`, leaving the
  runtime archive's `__cxx11` symbols undefined), and gcc 11's libstdc++ is too old for the
  clang-22-built runtime (it lacks `std::__glibcxx_assert_fail`, added in gcc 12). The script now
  links the *newest* installed `libstdc++.so` by full path — here gcc 14's, the same one system
  clang 22 selects.

- **The from-source fallback also works here.** With `compiler-rt22` installed the build links the
  system archive, but forcing the `get-libfuzzer.sh` path (as on a Linux box with clang but no
  runtime package — e.g. a bare CI runner) also links and runs, once its objects are built `-fPIC`:
  `leanc` links the executable as a PIE, and a non-PIC runtime object fails with
  `relocation R_X86_64_32 cannot be used against local symbol`. This is why `get-libfuzzer.sh`
  compiles with `-fPIC` unconditionally (a no-op on macOS).

Coverage feedback is confirmed live, not merely linked: `chain-4` (a bug behind four nested guards)
is found by the fuzz backend in ~1.3k runs and by neither random backend in millions — the exact
canary below.

The failure mode to watch for on an *untested* Linux, where instrumentation (Lean's clang 22) and a
system runtime may skew, is not a link error but a *silent* one: an instrumented binary whose
coverage feedback never reaches the runtime still links and still runs, and every property with a
shallow bug still fails. The workflow's `chain-4` assertion distinguishes that case, because only
coverage guidance can reach a bug behind four nested guards.

## Appendix B — Key source references

- Basalt: `Basalt/RandomChoice.lean` (`choose`), `Basalt/Gen.lean` (the `Gen` bundle + auto-instance), `Basalt/IO.lean` (`bitsFor`), `Basalt/PlausibleGen.lean`/`Basalt/GenStats.lean` (the flat-order `CCPO`/`MonoBind` recipe).
- This feature: `Basalt/Fuzz/Core.lean`, `Basalt/Fuzz/Runner.lean`, `Basalt/Fuzz/native.c`, `BasaltFuzz/BuggyBST.lean`, `BasaltFuzzMain.lean`, `BasaltTest/Fuzz.lean`, `fuzz-run/`.
- Prior art: bolero `lib/bolero-libfuzzer/src/{lib.rs,FuzzerAPI.cpp}`, `lib/bolero-generator/src/driver/bytes.rs`; crowbar `src/crowbar.ml` (`choose_int`, the AFL bridge); FuzzChick `src/Test.v` (`fuzzLoop`), `Fuzz/`, `src/quickChickLib.ml` (`choose_int`).
