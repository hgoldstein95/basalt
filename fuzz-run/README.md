<!--
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Michael Hicks
-->

# `basalt-fuzz`: coverage-guided property testing

`FuzzGen` is an executable interpretation of Basalt's `Gen` whose choices are decided by a
**coverage-guided fuzzer** rather than by a PRNG: libFuzzer proposes a byte buffer, `choose` reads
bytes from it to make each choice, and libFuzzer observes which branches of the generator and of the
property execute and mutates the buffer to reach new ones. This is *parametric fuzzing* — the fuzzer
explores the space of choices that defines a generator's output, using coverage rather than a
distribution to decide where to look.

`basalt-fuzz` is the opt-in executable that runs it. It links native code, so it is **not** built by
`lake build`; `fuzz-run/build.sh` builds it. This file is the whole story: design, build contract,
supported platforms, and limitations.

## Design

### The interpretation (`Basalt/Fuzz/Core.lean`)

`FuzzGen` is `StateT FuzzState Option` over the byte buffer and a read cursor — a *pure* state monad,
so one fuzzer input is a pure function `ByteArray → TestOutcome` (`runOne`). That makes the C
boundary trivial and every input exactly reproducible from its bytes.

The extension point is the usual one: supply the component instances and `Gen FuzzGen` follows by
`inferInstance` (`Basalt/Gen.lean`). The whole interpretation is one `RandomChoice` instance plus the
flat order on `Option`, whose `none` is the bottom that `partial_fixpoint` needs for recursive
generators (`Basalt.PlausibleGen`/`GenStats` use the same recipe with `Except`). There is
deliberately no fuel and no failure case: termination is the generator's own concern, with
libFuzzer's `-timeout`/`-rss_limit_mb` as the backstop for a genuinely divergent one.

`choose` reads the *smallest* number of bytes covering the range and reduces modulo it (crowbar's
encoding), which keeps a tight, mutation-friendly map from corpus bytes to structural choices. Past
the end of the buffer it reads `0`. Both properties matter: `choose` is total, and *bytes → execution*
is deterministic, which is what coverage-guided mutation relies on. See "Limitations" for what
zero-extension costs.

### The C bridge (`Basalt/Fuzz/native.c`, `Basalt/Fuzz/Runner.lean`)

```
 ┌────────────────────── Lean executable (owns main) ───────────────────────┐
 │ main → PBT.dispatch → Fuzz.go T argv                                     │
 │   T : G TestOutcome         -- the property, polymorphic in the Gen G     │
 │   go builds  run : ByteArray → IO UInt8  and hands it to the bridge ──┐   │
 │                                                                      ▼   │
 │ RandomChoice FuzzGen          ┌──── C bridge (Basalt/Fuzz/native.c) ────┐ │
 │  choose reads bytes from      │ basalt_fuzz_go(run, argv):              │ │
 │  FuzzState.buffer/cursor,     │   store run in a global slot            │ │
 │  zero-fill past end-of-buffer │   LLVMFuzzerRunDriver(argc, argv, cb)   │ │
 │      ▲  pure Option state     │ cb = LLVMFuzzerTestOneInput(Data,Size):◀┼─┼┐
 │ FuzzGen α =                   │   arr := ByteArray copy of (Data,Size)  │ ││
 │  StateT FuzzState Option      │   code := run arr        (: IO UInt8)   │ ││
 │                               │   1 → (Lean printed it) abort()         │ ││
 │                               │   2 → return -1 (discard) ; else 0      │ ││
 │                               └─────────────────────────────────────────┘ ││
 └──────────────────────────────────────────────────────────────────────────┘│
                    ▲                                                        │
                    └── libFuzzer runtime (libclang_rt.fuzzer_no_main) ───────┘
                        mutation loop + corpus + coverage counters;
                        on abort() saves the crashing input as an artifact;
                        counters come from SanitizerCoverage-instrumented .o
                        of the (Mathlib-free) property/generator closure.
```

Lean owns `main`, so the Lean runtime is already initialized when libFuzzer calls back — no init
dance. Two spellings of the driver entry exist: the stable C `LLVMFuzzerRunDriver` (LLVM ≥ 12) and
the mangled `fuzzer::FuzzerDriver` for clang 11 and earlier. `build.sh` picks by `nm`-probing the
runtime archive; `native.c` is C either way, since the mangled name is simply declared `extern`.

Failure handling follows **bolero**: the Lean callback prints the counterexample and returns `1`, and
the bridge `abort()`s, so libFuzzer's signal handler saves the crashing input under
`-artifact_prefix` and exits with its error code (77). Consequences worth knowing: `go : IO Unit` —
the campaign's result is the exit code plus the printed report, not a value returned to the Lean
caller (see "Limitations"); and `go` must be called once per process, because libFuzzer's driver is
not re-entrant.

### Build and instrumentation (`fuzz-run/build.sh`)

Lean's default backend emits one C file per module under `.lake/build/ir/`, and SanitizerCoverage is
a compile-time flag on that C. `build.sh` compiles the modules whose branching the fuzzer should
explore — the properties and the generator/combinator code, listed in its `MODULES` — with
`-fsanitize=fuzzer-no-link`, and links them against the libFuzzer runtime with `leanc` as the C
driver. The Lean runtime and the rest of stdlib stay uninstrumented; partial coverage still guides
libFuzzer. Plausible's `Gen`/`Random` are linked but not instrumented: they are the
`--backend=plausible` PRNG rather than code under test, and coverage over a PRNG's mixing steps is
noise in the feedback.

**The link closure must stay Mathlib-free.** A `#eval` runs generators in the interpreter, but a
compiled executable links the native code of its entire import closure, and importing the `Basalt`
umbrella reaches Mathlib through `Basalt.SPMF` — 1440 modules, against the ten first-party ones
`MODULES` compiles. Generator *definitions* need only `Gen`/`Combinators`; only their *proofs* need
Mathlib. So every module the executable imports imports the narrowest thing it can — which is also
why `Basalt/PlausibleGen.lean` imports `Plausible.Gen` and not the `Plausible` umbrella, whose tactic
frontend and deriving handlers would join the link.

Elaboration is a separate matter from linking. `BasaltTest/Fuzz.lean` is built by the default `lake
build` and imports `BasaltFuzz.BuggyBST`, so that target is type-checked and its `genBST` is pinned
against the proved one — that is how a drift becomes a build failure. Only the `basalt-fuzz` CI
workflow builds `BasaltFuzz.Staged` and `BasaltFuzzMain`, and only `build.sh` does the C emission,
the sancov compile, and the native link, so the default `lake build` needs no C toolchain and no
libFuzzer runtime.

## Build

```bash
fuzz-run/build.sh          # elaborates the Mathlib-free closure, instruments it, links libFuzzer
```

Runs with no arguments on the platforms in [Platforms](#platforms) below. The script detects the C
driver, the libFuzzer runtime (in both the legacy and the clang-≥14 per-triple layouts), the libc
headers the C bridge needs, the C++ runtime, and which driver entry point to call, so an unlisted
platform is likely to need nothing. Where a machine's toolchain defeats detection, put overrides in
`fuzz-run/env.sh` (git-ignored, sourced first) — `env.example.sh` documents every knob.

If no toolchain-provided runtime is found — the macOS case, since neither Apple's clang nor Lean's
vendored clang ships one — the build calls `get-libfuzzer.sh`, which builds the archive from
compiler-rt's standalone `lib/fuzzer` source into `fuzz-run/vendor/` (a sparse ~1MB checkout, a few
seconds, once). Instrumentation itself needs nothing extra.

## Run

```bash
fuzz-run/basalt-fuzz [--backend=fuzz|io|plausible] <property> [-runs=N] [libFuzzer args...]
fuzz-run/basalt-fuzz replay <property> <file>      # reproduce a saved input, no fuzzer
```

Properties (see `BasaltFuzzMain.lean`, `BasaltFuzz/BuggyBST.lean`, `BasaltFuzz/Staged.lean`):

| property | expectation |
|---|---|
| `threshold` | infra self-test; a false property any backend quickly falsifies |
| `bst-gen` | `genBST` only makes valid BSTs — never fails |
| `bst-insert` | the correct `insert` preserves the BST invariant — never fails |
| `bst-buggy-insert` | the buggy `insert` does **not** preserve it — a counterexample is found |
| `bst-insert2` | correct `insert` of two *distinct* keys (composed, multi-input) — never fails |
| `bst-buggy-insert2` | the buggy `insert` of two distinct keys — counterexample reports `(t, k1, k2)` |
| `bst-delete` | `delete` agrees with the list model `toList.erase` — never fails |
| `bst-buggy-delete` | a `delete` that silently drops keys; the output is still a valid BST, so only the model comparison catches it |
| `chain-2`/`-3`/`-4` | the staged microbenchmark — a bug behind `n` nested guards |

Useful libFuzzer flags: `-runs=N` (bounded campaign), `-max_len=N` (input size),
`-artifact_prefix=./` (where crashing inputs are written), a positional dir for a seed/growing
corpus. The random backends read `-runs=N` from the same spelling, and ignore the rest.

## Backends

A Basalt property is polymorphic in its monad, so the *same* property term runs under a coverage-
guided fuzzer or under a plain random sampler; `--backend=` picks the interpretation:

| backend | interpretation | choices come from |
|---|---|---|
| `fuzz` (default) | `Fuzz.FuzzGen` | libFuzzer's mutated byte buffer, guided by coverage |
| `io` | `IO` | `IO.rand` |
| `plausible` | `Plausible.Gen` | Plausible's `StdGen` |

All three come from one registry of `Basalt.PBT.Property` and share `Basalt.PBT`'s failure contract,
so their campaigns are directly comparable. Adding the two random backends needed no new instance and
no change to any property or generator: `Gen IO` and `Gen Plausible.Gen` already followed by
`inferInstance`, and what it took was a registry type that keeps the monad open. `replay` is
fuzz-only, because a saved artifact *is* a `FuzzGen` byte buffer and has no meaning as a PRNG state.

### How fast each backend finds a bug

`fuzz-run/compare-backends.sh` measures time-to-first-counterexample, median over 9 trials from a
cold start (fresh process, so libFuzzer begins with an empty corpus). Measured on macOS arm64
(M-series), `MAXRUNS=20000000`, per-trial cap 120s:

| property | fuzz | io | plausible |
|---|---|---|---|
| `threshold` | 28 runs | 3 | 3 |
| `bst-buggy-insert` | 12 runs | 3 | 6 |
| `bst-buggy-insert2` | 94 runs | 3 | 4 |
| `bst-buggy-delete` | 500 runs | 46 | 65 |
| `chain-2` | 200 runs | 87,745 | 19,789 |
| `chain-3` | 556 runs | 3,839,993 (8/9 trials) | 1,725,902 (3/9) |
| `chain-4` | 1,246 runs | **not found** (0/9) | **not found** (0/9) |

Read the two halves separately, because they say opposite things:

- **Shallow bugs: random wins.** Where one unlucky draw exposes the bug, coverage guidance is pure
  overhead — libFuzzer spends its first inputs mapping coverage, and its per-run cost is higher
  (~100k runs/s vs `io`'s ~555k and `plausible`'s ~317k on `bst-gen`). All four BST bugs are of this
  kind: every backend finds them in well under a millisecond, and `io` gets there in the fewest runs.
- **Staged bugs: only the fuzzer arrives.** `chain-n` puts the bug behind `n` nested guards, so a
  blind sampler needs all `n` to hit at once (`256⁻ⁿ`) while the fuzzer banks one stage at a time and
  pays roughly `n·256`. The cost of a stage is therefore multiplicative for random search and
  additive for the fuzzer: at `n=4` that is ~1.2k runs versus 4.3 billion expected, and the random
  backends found nothing in 20M runs × 9 trials.

The honest summary is that the backends are complementary, and which wins is a property of the *bug*,
not of the tool: reach for random testing by default because it is simpler and faster per run, and
for the fuzzer when a bug hides behind structure a uniform sampler cannot stumble into. `io` and
`plausible` are both uniform (verified per-draw and pairwise), so the spread between them across
trials is variance in a geometric distribution, not a distributional difference. This is the concrete
argument for the interpretation-polymorphic design: the choice is per-bug, and it costs a flag rather
than a rewrite.

## What a run looks like

Exit `0` = campaign passed; nonzero = a counterexample was found (and, for the fuzz backend, saved).
The random backends report the same way and exit 77 too, with no artifact — their input is a PRNG
state, not a buffer.

```
$ fuzz-run/basalt-fuzz bst-buggy-insert -runs=2000000 -artifact_prefix=./
[basalt] starting libFuzzer campaign ([-runs=2000000, -artifact_prefix=./])
...
*** BASALT PROPERTY FAILED ***
counterexample : (BasaltFuzz.BuggyBST.Tree.node (...leaf) 1 (...leaf), 1)
input bytes    : [255, 255, 42]
runs           : 22 (0 discarded)
==...== ERROR: libFuzzer: deadly signal
artifact_prefix='./'; Test unit written to ./crash-<sha1>
```

The counterexample (`Repr`-rendered, hence fully qualified) is a *valid* BST plus a key it already
contains; `insertBuggy` lacks the equal-key guard, so it duplicates the key and breaks the invariant.

### Consuming the artifact

The `crash-<sha1>` file is the raw input bytes — the reproduction seed. Consume it by **replaying**:

```
fuzz-run/basalt-fuzz replay bst-buggy-insert crash-<sha1>
```

This re-runs the property on those bytes (no fuzzer), re-deriving and re-printing the same
counterexample. Because `choose` zero-fills past the end of the buffer, the bytes alone reproduce the
failure — drop the `crash-<sha1>` file into a regression directory as a fixture.

## Writing a fuzz target: what coverage guidance can and cannot see

Coverage guidance is driven by **branch/structure** coverage, not by guessing wide scalars. Do not
put a demo bug behind a magic-value `Nat` equality: a 32-bit needle (`x == 0xDEADBEEF` over
`chooseNat 0 4294967295`) is not found in 5M runs, with or without `-use_cmp`. Design bugs to be
reachable via new *branches* instead — like the equal-key arm of `insertBuggy`, or `chain-n`'s
nesting — which the fuzzer explores well.

The reason is worth stating precisely, because the obvious explanation is wrong. `lean_nat_eq`/`_le`
are `LEAN_ALWAYS_INLINE` with a small-scalar fast path, so they *do* inline into instrumented code
and *do* emit `-trace-cmp` hooks (`__sanitizer_cov_trace_const_cmp8` is present in the BST object
file). But the value the hook observes is a **tagged** Lean scalar, `2*n+1` — comparing
`0x1BD5B7DDF`, not `0xDEADBEEF` — so the literals libFuzzer harvests into its table of recent
compares never match the bytes `choose` reads out of the input buffer. The signal fires and is
useless. (Only boxed `Nat`s above the scalar range reach the genuinely uninstrumented
`lean_nat_big_*` in `libleanshared`.)

## Platforms

`fuzz-run/build.sh` builds with no arguments on the three platforms below, spanning a very old and a
current Linux. Five things vary between platforms and the script detects each one; every probe can be
overridden from `fuzz-run/env.sh`, which `env.example.sh` documents. Because the probes are generic,
an unlisted platform is *likely* to work — but only these three have been run.

| what varies | how it is resolved |
|---|---|
| C compile/link driver | `leanc`, which already knows Lean's include path, clang resource headers, sysroot, and rpaths (`CC`) |
| libFuzzer runtime | a toolchain `libclang_rt.fuzzer_no_main*.a` (legacy `.../lib/linux` or clang-≥14 `.../lib/<triple>`, host-arch only) *whose clang major matches the instrumenting clang*, else the compiler-rt build in `fuzz-run/vendor/`, which is pinned to that major, else a mismatched system archive with a warning (`FUZZER_LIB_FLAGS`) |
| driver entry point | `nm` on the runtime archive: `LLVMFuzzerRunDriver` if present, else the mangled `fuzzer::FuzzerDriver` (`DRIVER_DEFINE`) |
| libc headers for `native.c` | the platform SDK's include dir on macOS, `/usr/include` (plus the Debian/Ubuntu multiarch dir) on Linux, because `leanc`'s vendored clang has no libc in its sysroot (`BRIDGE_INCLUDES`) |
| C++ runtime | `-lc++` on macOS; on Linux the newest installed `libstdc++.so` named by full path, since a bare `-lstdc++` is dropped alongside `leanc`'s own `-lc++` (`CXXLIB_FLAGS`) |

Two cross-platform rules behind that table. **The runtime's clang major must match the instrumenting
clang's**, because the runtime implements the SanitizerCoverage ABI the instrumented code calls
against; a large skew still links and still fails on shallow bugs, but coverage never reaches the
runtime. And **`-fsanitize=fuzzer-no-link` must not appear on the link line** — it is a compile-time
flag, and at link time it also requests a ubsan dylib Lean's vendored clang does not ship.

**macOS (arm64, macOS 15).** Lean's vendored clang (LLVM 22) is a native arm64 binary and instruments
Lean's emitted C out of the box, and has the stable driver entry. No libFuzzer runtime ships
anywhere — Apple's clang has only the `fuzzer` headers and Lean's vendored clang only
`libclang_rt.osx.a` — so `get-libfuzzer.sh` builds one. `native.c` needs `-isystem $(xcrun
--show-sdk-path)/usr/include`.

**Amazon Linux 2 (x86_64, clang 11.1.0).** The legacy case, and the only platform needing an
`env.sh`. Its runtime is at `/usr/lib64/clang/11.1.0/lib/linux/` and predates
`LLVMFuzzerRunDriver`, so the bridge takes the mangled-name path. Lean's vendored clang does not run
here (it needs `GLIBC_2.27`/`2.29`), so `LEAN_CC` must point at a wrapper around the system clang 11
that injects the vendored `libc++`/`gmp`/`uv` and rpaths — the same wrapper `lake exe cache get`
needs. `libstdc++` is not on the default link path either. `env.example.sh` carries both settings.

**Amazon Linux 2023 (x86_64, clang 22 / `compiler-rt22`).** The current-Linux case: `dnf install
clang22 compiler-rt22`, Lean via `elan`, and no `env.sh` at all. glibc 2.34 is new enough for Lean's
vendored clang, so no `LEAN_CC` wrapper; instrumentation and runtime are the same clang 22, so no
skew; the runtime lives in the per-triple dir. The from-source fallback also works here, which is why
`get-libfuzzer.sh` compiles `-fPIC` unconditionally (`leanc` links a PIE, and a non-PIC runtime
object fails with `relocation R_X86_64_32 cannot be used against local symbol`).

**A newer-glibc caveat**, hit on Ubuntu 24.04 (glibc 2.39) rather than on AL2023: glibc ≥ 2.38
redirects `strtol`/`strtoul` to the ISO C23 symbols `__isoc23_strtol`/`_strtoul`, which the runtime
then references but `leanc`'s older-baseline libc does not export, so the link fails on those two
symbols while every classic libc symbol resolves. `fuzz-run/isoc23_compat.c` supplies them as weak
aliases and is inert on glibc < 2.38.

The failure mode to watch for on an untested Linux is not a link error but a *silent* one: an
instrumented binary whose coverage feedback never reaches the runtime still links, still runs, and
still fails every property with a shallow bug. `chain-4` distinguishes that case — only coverage
guidance reaches a bug behind four nested guards — which is why the `basalt-fuzz` CI workflow asserts
it.

## Limitations and future work

- **The fuzzer is not told the buffer is zero-extended.** Running off the end silently yields `0`s,
  which are likely (not guaranteed) to steer a generator toward a terminating choice, but the fuzzer
  neither knows to supply more bytes nor sees them during mutation. Two fixes, both future work:
  store a seed in `FuzzState` and draw from it past the end (saving the seed keeps replay
  deterministic), or use a [custom
  mutator](https://github.com/google/fuzzing/blob/master/docs/structure-aware-fuzzing.md), which can
  be made to extend the underlying buffer. Zero-extension is what bolero and (as far as we know) JQF
  do today.
- **`bytesFor` is computed per `choose` call, at runtime.** Determining it statically would be
  nicer. Reading a fixed word instead is *not* the fix: with a whole word per choice, many word
  values map to the same value (2²⁴ words per outcome over `chooseNat 0 255`), so most mutations of
  that word change nothing the property can see. Whatever replaces it must keep the tight
  bytes → choice map.
- **A `trace-cmp`-friendly choice encoding.** Modulo reduction could give way to a comparison-exposing
  encoding (bolero's Lemire scaling), but note the binding constraint measured above is *tagging*,
  not instrumentation scope: an encoding change alone will not help unless the compared value and the
  buffered bytes agree, e.g. by comparing on `UInt32`/`UInt8` before widening to `Nat`.
- **No in-process campaign result.** A failure `abort()`s, so `go` cannot return a `TestOutcome`;
  FuzzChick shows the trade-off, which is that you can return a value only if you own the loop. The
  clean way to have both is a subprocess model: a Lean parent spawns a libFuzzer child that aborts
  like bolero, and reconstructs a `TestOutcome` from the child's exit code, artifact, and stderr.
  Cost is a process boundary. (An in-process `setjmp`/`longjmp` return path works but leaves no
  artifact and must `_exit` past libFuzzer's `atexit` handlers.)
- **No value-level shrinking.** Today this relies on libFuzzer's byte-level minimization
  (`-minimize_crash=1`) and reports the first counterexample. A Basalt value-level shrinker would
  give smaller counterexamples but is net-new — Basalt has no shrinker.
- **Stop-on-first only.** A flag could keep going past the first failure to collect several
  counterexamples, either in-process (`return -1` and accumulate) or libFuzzer-native
  (`-fork=N -ignore_crashes=1`).
- **`Tree`/`genBST` is duplicated** between `BasaltExamples/BST.lean` and `BasaltFuzz/BuggyBST.lean`,
  because the example imports the `Basalt` umbrella for its proofs and so cannot be linked. Moving
  the Mathlib-free part (the datatype and the generator) into a module both import would make the
  fuzzed term the proved term by construction rather than by a pinned test. Two things to settle
  first: the shared `Tree` must be monomorphic or the fuzz side must instantiate it, and `isBST` has
  to exist in both a `Prop` form for the proofs and a `Bool` form for the property (a `decide`
  bridging lemma is the tidy version).
- **Broader instrumentation, other engines.** More of Basalt can be instrumented when a target's
  coverage of interest lives outside the current closure. The `RandomChoice FuzzGen` core is
  engine-agnostic — crowbar shows the same cursor drives AFL — so an AFL or honggfuzz backend changes
  only the C bridge.

## Prior art

- **bolero** (Rust → libFuzzer, <https://github.com/camshaft/bolero>) is the closest model: it
  excludes libFuzzer's `main`, calls the driver through a shim with the per-input closure in a global
  slot, zero-fills past the end of its byte cursor, and on failure prints the rendered value and
  `abort()`s so the driver saves the input.
- **crowbar** (OCaml → AFL, <https://github.com/stedolan/crowbar>): its `choose_int n` reads the
  smallest number of bytes covering a range and reduces modulo `n` — the encoding reused here.
- **FuzzChick** (Coq, <https://github.com/QuickChick/QuickChick>, `FuzzChick` branch) is the most
  direct analogue, PBT plus fuzzing inside a proof assistant, with the same byte model. Its own loop
  returns a structured result, but the moment it delegates to `afl-fuzz` it reverts to crash → the
  driver saves the input. That split — own the loop and you can return a value; delegate to a driver
  and you crash — is the lesson behind the subprocess item above.

Basalt-side reading: `Basalt/RandomChoice.lean` (`choose`), `Basalt/Gen.lean` (the bundle and its
auto-instance), `Basalt/PBT/` (the interpretation-agnostic property and campaign API),
`Basalt/PlausibleGen.lean` and `Basalt/GenStats.lean` (the flat-order `CCPO`/`MonoBind` recipe).
