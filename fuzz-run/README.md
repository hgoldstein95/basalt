<!--
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
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
is deterministic, which is what coverage-guided mutation relies on.

The buffer is finite and a generator's appetite is not, so a run can outrun its bytes. The cursor is
not clamped, so how far it overshot survives as the `FuzzResult.deficit` — the one thing the fuzzer
can be told about the zeros it did not supply; see [Extending the buffer](#extending-the-buffer).

### The C bridge (`Basalt/Fuzz/native.c`, `Basalt/Fuzz/Runner.lean`)

```
 ┌────────────────────── Lean executable (owns main) ───────────────────────┐
 │ main → PBT.dispatch → Fuzz.go T argv                                     │
 │   T : PropM G Unit          -- the property, polymorphic in the Gen G     │
 │   go builds  run : ByteArray → IO UInt8  and hands it to the bridge ──┐   │
 │                                                                      ▼   │
 │ RandomChoice FuzzGen          ┌──── C bridge (Basalt/Fuzz/native.c) ────┐ │
 │  choose reads bytes from      │ basalt_fuzz_go(run, argv, grow):        │ │
 │  FuzzState.buffer/cursor,     │   store run in a global slot            │ │
 │  reading 0 past end-of-buf    │   LLVMFuzzerRunDriver(argc, argv, cb)   │ │
 │      ▲  pure Option state     │ cb = LLVMFuzzerTestOneInput(Data,Size):◀┼─┼┐
 │ FuzzGen α =                   │   arr := ByteArray copy of (Data,Size)  │ ││
 │  StateT FuzzState Option      │   code := run arr        (: IO UInt8)   │ ││
 │      │                        │   1 → (Lean printed it) abort()         │ ││
 │      └─ deficit ──────────────┼─▶ basalt_fuzz_note_deficit(deficit)     │ ││
 │                               │   2 → return -1 (discard) ; else 0      │ ││
 │                               │ LLVMFuzzerCustomMutator(Data,Size,Max): │ ││
 │                               │   if `grow` and Data ran short: append  │ ││
 │                               │   `deficit` zeros, then LLVMFuzzerMutate│ ││
 │                               │   (the default suite, which it replaces)│ ││
 │                               └─────────────────────────────────────────┘ ││
 └──────────────────────────────────────────────────────────────────────────┘│
                    ▲                                                        │
                    └── libFuzzer runtime (libclang_rt.fuzzer_no_main) ───────┘
                        mutation loop + corpus + coverage counters;
                        on abort() saves the crashing input as an artifact;
                        counters come from SanitizerCoverage-instrumented .o
                        of `BasaltFuzz` + the executable root, nothing else.
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
a compile-time flag on that C. **Lake owns the closure and the scope.** `basalt-fuzz` is an ordinary
`lean_exe`, so Lake derives the link closure from imports; the instrumentation scope is
`-fsanitize=fuzzer-no-link` in the `moreLeancArgs` of the `BasaltFuzz` library and of the executable
root (`lakefile.toml`), and nowhere else. That confines coverage feedback to the code under test —
the generators, the properties, and the buggy operations — leaving Basalt's plumbing, the Lean
runtime, and stdlib linked but uninstrumented; partial coverage still guides libFuzzer. Plausible's
`Gen`/`Random` are in the same position for a second reason: they are the `--backend=plausible` PRNG
rather than code under test, and coverage over a PRNG's mixing steps is noise in the feedback.

Two modules and one executable root are a narrow scope for something as central as generator
branching, and it works because Lean *specializes*. A generator is polymorphic in its monad, so the
copy that actually runs is a specialization emitted into the module that instantiates it — for every
property here, the one holding the registry, `BasaltFuzzMain`. The generic copies left behind in
`Basalt/Combinators.lean` are dead. Instrumenting `BasaltFuzz.+` and the root therefore captures the
live generator code by construction, and extending the flag to the `Basalt` library would add tens of
thousands of edges the campaign never reaches. Measured on this repo: 4.5k counters here against
17.9k when the whole first-party closure carried the flag, with no loss in the properties found.

`build.sh` supplies what Lake's declarative config cannot — this platform's libFuzzer runtime, its C++
runtime, the compiled C bridge, and three post-link assertions. Each assertion guards a property
whose violation leaves a *working* fuzzer that searches badly rather than a build error: no Mathlib in
Lake's link response file, the instrumentation scope in both directions (every `BasaltFuzz` object and
the root carry `__sancov_cntrs`; no `Basalt` object does), and `LLVMFuzzerCustomMutator` still
exported past `-Wl,-dead_strip`.

**The link closure must stay Mathlib-free.** A `#eval` runs generators in the interpreter, but a
compiled executable links the native code of its entire import closure, and importing the `Basalt`
umbrella reaches Mathlib through `Basalt.SPMF` — 1440 modules, against the dozen-odd first-party ones
the fuzzer needs. Generator *definitions* need only `Gen`/`Combinators`; only their *proofs* need
Mathlib. So every module the executable imports imports the narrowest thing it can — which is also
why `Basalt/PlausibleGen.lean` imports `Plausible.Gen` and not the `Plausible` umbrella, whose tactic
frontend and deriving handlers would join the link. This used to fence itself, since Mathlib's native
code was not built; now that Lake derives the closure it would simply be built into the fuzzer, which
is why `build.sh` greps for it instead.

Elaboration is a separate matter from linking. `BasaltFuzz` is a default target, so `lake build`
type-checks both fuzz targets, and `BasaltTest/Fuzz.lean` additionally pins `BuggyBST`'s `genBST`
against the proved one, which is how a drift becomes a build failure. Only `BasaltFuzzMain` is left
out. A `lean_lib` target stops at `.olean`s, so the default build emits no C for these modules at
all: the sancov compile and the native link happen only when `basalt-fuzz` is requested, and
`lake build` needs no C toolchain and no libFuzzer runtime.

## Build

```bash
fuzz-run/build.sh          # lake build basalt-fuzz, plus the bridge, the runtime, and the assertions
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
fuzz-run/basalt-fuzz [--backend=fuzz|io|plausible] <property> [-runs=N] [-discard_ratio=N] [libFuzzer args...]
fuzz-run/basalt-fuzz <property> [--grow]           # fuzz backend only, see below
fuzz-run/basalt-fuzz replay <property> <file>      # reproduce a saved input, no fuzzer
```

Properties (see `BasaltFuzzMain.lean` and `BasaltFuzz/`):

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
| `long-16`/`-32`/`-64` | the mirror image: a run of `n` elements where each position accepts half the byte values, so what binds is the buffer's *length* — the benchmark for [Extending the buffer](#extending-the-buffer) |

Useful libFuzzer flags: `-runs=N` (bounded campaign), `-max_len=N` (input size),
`-artifact_prefix=./` (where crashing inputs are written), a positional dir for a seed/growing
corpus. The random backends read `-runs=N` from the same spelling, plus `-discard_ratio=N` for the
discard budget (`Basalt/PBT/Driver.lean`), and ignore the rest — under `fuzz`, libFuzzer owns the
loop, so a discarded input is a `-1` return and neither budget applies.

`--grow` is Basalt's own and is consumed before libFuzzer sees the command line; everything else is
forwarded verbatim, and libFuzzer rejects a flag it does not know. It is off by default and measurement
does not support turning it on ([Extending the buffer](#extending-the-buffer)).

## Backends

A Basalt property is polymorphic in its monad, so the *same* property term runs under a coverage-
guided fuzzer or under a plain random sampler; `--backend=` picks the interpretation:

| backend | interpretation | choices come from |
|---|---|---|
| `fuzz` (default) | `Fuzz.FuzzGen` | libFuzzer's mutated byte buffer, guided by coverage |
| `io` | `IO` | SplitMix (`ioGen`) |
| `plausible` | `Plausible.Gen` | Plausible's `StdGen` |

All three come from one registry of `Basalt.PBT.Property` and share `Basalt.PBT`'s failure contract,
so their campaigns are directly comparable. `fuzzBackend` is a `@[basalt_backend]`, so `dispatch`
offers it alongside Basalt's own two without `BasaltFuzzMain` listing them. Adding the two random backends needed no new instance and
no change to any property or generator: `Gen IO` and `Gen Plausible.Gen` already followed by
`inferInstance`, and what it took was a registry type that keeps the monad open. `replay` is
fuzz-only, because a saved artifact *is* a `FuzzGen` byte buffer and has no meaning as a PRNG state.

### How fast each backend finds a bug

`fuzz-run/compare-backends.sh` measures time-to-first-counterexample, median over 9 trials from a
cold start (fresh process, so libFuzzer begins with an empty corpus). Measured on macOS arm64
(M-series), `MAXRUNS=20000000`, per-trial cap 120s:

| property | fuzz | io | plausible |
|---|---|---|---|
| `threshold` | 27 runs | 2 | 2 |
| `bst-buggy-insert` | 4 runs | 7 | 5 |
| `bst-buggy-insert2` | 232 runs | 2 | 2 |
| `bst-buggy-delete` | 667 runs | 14 | 10 |
| `chain-2` | 587 runs | 100,364 | 24,824 |
| `chain-3` | 561 runs | 5,902,188 (5/9 trials) | 14,718,791 (7/9) |
| `chain-4` | 684 runs | **not found** (0/9) | **not found** (0/9) |

Two things to know before reading it. A median is over the trials that *found* the bug, so it goes
with the `found` count: where those differ, the backend that found it less often has the more
favourably conditioned median (which is why `chain-3`'s `io` column looks better than `plausible`'s).
And a run is a *tested* input — a discarded one is budgeted separately and does not count — which
matters for `bst-buggy-delete`, whose precondition rejects most draws.

Read the two halves separately, because they say opposite things:

- **Shallow bugs: random usually wins, and the margin is noise.** Where one unlucky draw exposes the
  bug, coverage guidance is pure overhead — libFuzzer spends its first inputs mapping coverage, and
  its per-run cost is higher (~54k runs/s vs `io`'s ~360k and `plausible`'s ~205k on `bst-gen`). All
  four BST bugs are of this kind, and every backend finds them in well under a millisecond. Do not
  read the ordering within a row: at a median of single-digit runs the trial-to-trial spread of a
  geometric distribution swamps it, which is why `bst-buggy-insert` here has the fuzzer ahead while
  the other three have it behind by one to two orders of magnitude.
- **Staged bugs: only the fuzzer arrives.** `chain-n` puts the bug behind `n` nested guards, so a
  blind sampler needs all `n` to hit at once (`256⁻ⁿ`) while the fuzzer banks one stage at a time and
  pays roughly `n·256`. The cost of a stage is therefore multiplicative for random search and
  additive for the fuzzer: at `n=4` that is a few hundred runs versus 4.3 billion expected, and the
  random backends found nothing in 20M runs × 9 trials. This is the only half of the table where the
  gap is far larger than the noise.

The honest summary is that the backends are complementary, and which wins is a property of the *bug*,
not of the tool: reach for random testing by default because it is simpler and faster per run, and
for the fuzzer when a bug hides behind structure a uniform sampler cannot stumble into. `io` and
`plausible` are both uniform (verified per-draw and pairwise), so the spread between them across
trials is variance in a geometric distribution, not a distributional difference. This is the concrete
argument for the interpretation-polymorphic design: the choice is per-bug, and it costs a flag rather
than a rewrite.

## Extending the buffer

A generator can ask for more bytes than the input has, and `readByte` gives it `0`. That keeps
`choose` total, but it leaves the fuzzer with a blind spot: **the zeros are not in the input**, so no
byte mutator can reach the positions that produced them. They become reachable only if some
length-extending mutation happens to lengthen the input, and then they arrive random rather than `0`,
discontinuously.

`--grow` attempts to close the gap by materializing the zeros *before* mutating. It is **off by
default**, because measurement does not support it helping — read
[How much growth helps](#how-much-growth-helps) before building on this. The run reports
how far it overshot (`FuzzResult.deficit`), `basalt_fuzz_note_deficit` hands the count to the C side, and the
next time `LLVMFuzzerCustomMutator` is called on those same bytes it appends that many zeros and then
mutates the extended buffer. Zeros are what make the extension free of meaning — reading past the end
yields `0`, and reading a stored `0` yields `0` — so the buffer that gets mutated decodes to exactly
the value the short one did, with the tail now a real region libFuzzer's suite can reach. Four things
about it are worth knowing:

- **It is necessarily run → observe → grow-and-mutate.** The mutator cannot be asked for bytes
  mid-run: `Data` is immutable while the callback is on the stack, and by the time libFuzzer calls the
  mutator no generator is in flight.
- **Growth requires an exact match on the bytes that ran short**, which is why `native.c` keeps a
  *copy* of the starved input rather than a deficit counter. `Fuzzer::MutateAndTestOne` (verified against
  llvmorg-22.1.8) mutates one buffer in place for up to `-mutate_depth` (5) iterations, so a mid-round
  mutator call is on exactly the bytes that just ran — but iteration 0 of every round follows
  `ChooseUnitToMutate` and a `memcpy` of an arbitrary corpus unit, where the previous run's deficit
  belongs to a buffer that is already gone. Extending *that* one would be harmful rather than merely
  wasteful: its tail is a region its own generator never asked for, so a mutation landing there dilutes
  the input for nothing. The size test rejects almost all of those on one integer compare, and the
  `memcmp` runs only when the sizes agree. Measured on `long-16`, growth fires on ~94% of starved runs,
  so the round-boundary case it declines is the small one.
- **The append is end-anchored, and nothing holds it afterwards.** libFuzzer's own `Mutate_CopyPart`
  also extends a buffer, but it inserts at a random offset, which re-aligns every subsequent `choose`
  and scrambles the whole generated value. Appending leaves every existing draw meaning exactly what it
  meant, so a run that reached stage `k` still reaches stage `k`. The mutation that follows may erase
  the tail it was just handed; that is intended — one growth makes the position exist, it does not
  legislate the result.
- **`-max_len` is the ceiling on how large a structure can be built**, so `--grow` raises it when you
  pass none (libFuzzer's own default derives it from the seed corpus, which is 4096 at a cold start;
  `splitFlags` in `Basalt/Fuzz/Runner.lean` sets the replacement). A run that wants more bytes at the
  cap is counted and reported as `at the -max_len cap`.

What growth cannot do is make the extended form *the* corpus entry. `Fuzzer::RunOne` admits an input
only on new features and `Corpus::AddFeature` counts a feature new only if unseen or carried by a
*smaller* input, so an equivalent-but-longer input is unreachable by construction — and writing one
into the corpus directory does not help either, since `RereadOutputCorpus` runs it through the same
admission rule. A starved input that was interesting on its own therefore stays in the corpus in its
short form, ghost zeros and all, and growth only biases the mutations made of it while it is the buffer
in hand. This is the setting's real limit, not an implementation gap; see
[Limitations](#limitations).

Defining a custom mutator has two consequences libFuzzer imposes: it *replaces* the default mutation
suite for the whole campaign (hence the `LLVMFuzzerMutate` delegation on every other path), and it
makes libFuzzer drop its `-len_control` length ramp. With `--grow` off there is no length decision for
the mutator to make, so `splitFlags` puts libFuzzer's own default ramp back, leaving the default
campaign the one measured in the backend table above. An explicit `-len_control=N` always wins, which
is how the two settings below are compared under one length regime.

### How much growth helps

Not measurably, which is why it is off by default. The data below is the reason, and it is worth
reading before trying to improve the mechanism, because the obvious explanations are not the ones that
survived a measurement.

**Runs-to-first-counterexample cannot settle this, and that is a result in itself.** It is the natural
metric and `MODE=median fuzz-run/compare-grow.sh` still reports it, but the distribution is heavy-tailed
enough that repeated passes over *the same binary* disagree in sign:

| property | 15 trials (off / grow) | 61 trials (off / grow) |
|---|---|---|
| `long-16` | 3,432 / **2,998** | **2,840** / 3,187 |
| `long-32` | **30,085** / 56,867 | 37,923 / **30,611** |
| `long-64` | **61,704** / 121,990 | 151,136 / **93,615** |

Every property reverses. The 15-trial pass says growth loses 2x at 32 and 64; the 61-trial pass says it
wins 1.2x and 1.6x. Any conclusion drawn from a table of this shape is a coin flip, including the ones
earlier revisions of this file drew.

**So `compare-grow.sh` measures a success rate at a fixed run budget instead.** That is a binomial:
its error bar is `sqrt(p(1-p)/n)`, and two cells are directly comparable. Budgets sit near each
property's own median, where a shift in either direction moves the rate the most. 300 trials per cell,
macOS arm64 (M-series), `-len_control=0 -max_len=65536` for both:

| property | budget | `--grow` off | `--grow` | repeat pass (off / grow) |
|---|---|---|---|---|
| `long-16` | 3,000 runs | **53.7%** ±2.9 | 41.7% ±2.8 | — |
| `long-32` | 30,000 | **46.3%** ±2.9 | 45.3% ±2.9 | 50.0% / 44.3% |
| `long-64` | 120,000 | 57.3% ±2.9 | 57.3% ±2.9 | 55.3% / 50.3% |

**Pooled over all 3,000 trials: 52.5% without growth against 47.8% with it — 4.7 points worse,
z = 2.6, p ≈ 0.01.** No individual cell is decisive and two are dead heats, but all five
property-passes fall on the same side, so the best available reading is "no benefit, and a small
penalty".

**The penalty is attributable to the zeros, not to the appending.** Filling the extension with
mutator-chosen bytes instead of zeros erases it: in that build, `long-32` at 30,000 runs scored 50.3%
without growth against 50.0% with — a dead heat, against the 1.0–5.7 point deficit the zero-filling
build shows. Two things follow, and together they are the answer to "can the buffer be extended in a
way libFuzzer benefits from":

- **Zero is neutral to the fuzzer but not to the decoder.** For `propLong`, `0` *is* a terminator, so
  materializing the deficit plants a guaranteed-stopping byte at exactly the frontier position — the
  one place where libFuzzer's own `InsertByte` would have put a random byte with a 50% chance of
  *extending* the run. This generalizes badly: in most generators `0` is the stopping or smallest
  choice (the first branch of a `frequency`, the empty structure from a size draw), so zero-extension
  systematically installs the value the generator least wants at the position that matters most.
  Semantics-preserving for the run that already happened is not the same as informative for the
  mutation that follows.
- **The deficit carries no information libFuzzer lacks.** Its length mutators already extend inputs,
  and they choose the byte value at least as well. Knowing the exact demanded length would buy
  something only if extending to it *stuck* — and that is precisely what the corpus admission rule
  forbids (see [Limitations](#limitations)). Absent that, growth is a worse-informed version of a
  mutation libFuzzer already makes, which is why the neutral-fill variant lands exactly on the
  baseline.

`long-n` is built so that *length* is the binding constraint: each position accepts half the byte
values, so the value of any single byte is cheap to find and what is expensive is having a byte there
at all (`BasaltFuzz/Staged.lean`). That is the only shape this setting can separate — a property
whose generator always fits inside its buffer reads nothing past the end, reports no deficit, and runs
the identical campaign either way. `--grow` therefore costs nothing to leave on for a property that
never runs short, and the `starved` count in the run report is how you tell which case you are in.

None of this proves the idea cannot work, and the setting is kept so it can be re-measured: run
`fuzz-run/compare-grow.sh` in both modes after any change to the mechanism, and read a median table
only against the reversal above.

## What a run looks like

Exit `0` = campaign passed; nonzero = a counterexample was found (and, for the fuzz backend, saved).
The random backends report the same way and exit 77 too, with no artifact — their input is a PRNG
state, not a buffer.

```
$ fuzz-run/basalt-fuzz bst-buggy-insert -runs=2000000 -artifact_prefix=./
[basalt] starting libFuzzer campaign (grow=false, [-runs=2000000, …, -len_control=100])
...
*** BASALT PROPERTY FAILED ***
counterexample : (BuggyBST.Tree.node (...leaf) 1 (...leaf), 1)
input bytes    : [239]
runs           : 18 (0 discarded)
buffer         : 1 bytes, 3 short
[basalt] runs 18, starved 10 (max deficit 3 B) [--grow off]
==...== ERROR: libFuzzer: deadly signal
artifact_prefix='./'; Test unit written to ./crash-<sha1>
```

The counterexample (`Repr`-rendered, hence fully qualified) is a *valid* BST plus a key it already
contains; `insertBuggy` lacks the equal-key guard, so it duplicates the key and breaks the invariant.

The `buffer` row and the `[basalt] runs …` line are the [Extending the buffer](#extending-the-buffer)
report: this input asked for 4 bytes and got 1, and 10 of the 18 runs went short — a property whose
generator outruns the buffer this often is one `--grow` can help. The `[basalt]` line comes from C, on
stderr, and is printed at both exits (here past `abort()`; on the `-runs`-exhausted path from an
`atexit` handler). libFuzzer's own `MS:` lines end in `Custom-` in every campaign, `--grow` or not,
because the mutator is linked unconditionally and delegates.

### Consuming the artifact

The `crash-<sha1>` file is the raw input bytes — the reproduction seed. Consume it by **replaying**:

```
$ fuzz-run/basalt-fuzz replay bst-buggy-insert crash-<sha1>
[basalt] replaying crash-<sha1> (1 bytes)

*** BASALT PROPERTY FAILED ***
counterexample : (BuggyBST.Tree.node (BuggyBST.Tree.leaf) 1 (BuggyBST.Tree.leaf), 1)
```

This re-runs the property on those bytes (no fuzzer), re-deriving and re-printing the same
counterexample — drop the `crash-<sha1>` file into a regression directory as a fixture.

The bytes alone are the whole reproduction, and replay takes no flag: zero-extension is a property of
`readByte`, not a campaign setting, so an artifact means the same thing however it was produced —
including one grown by `--grow`, which is already whatever length the failing run read.

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

- **Growth attributes the deficit by input size, not by identity.** `LLVMFuzzerCustomMutator` is handed
  a buffer, not a run, so it appends only when the size it is given matches the size of the run that
  reported the deficit — the common case, since libFuzzer mutates the input it just executed, but a
  same-size buffer from elsewhere in the queue would inherit the deficit and a differently-sized one
  would drop it. The fix is to key the deficit on the buffer's content (a hash) rather than its length.
- **One deficit, appended at the end.** The signal is a single count of unmet demand, so a generator
  that went short *in the middle* of a structure gets its bytes at the end anyway, where a later draw
  reads them. Anchoring at the end is what keeps every earlier draw's meaning fixed
  ([Extending the buffer](#extending-the-buffer)), so a per-draw record would have to buy its
  precision back some other way — most likely a length-prefixed encoding, which is a different
  interpretation, not a tweak to this one.
- **Growth is not measured to help, and cannot be undone.** It is off by default because 3,000 trials
  put it 4.7 points *behind* leaving it off, an effect traced to zeros being stopping values for most
  decoders rather than to the appending itself ([How much growth helps](#how-much-growth-helps)). It is
  also one-way: growth is capped at `-max_len`, a run blocked by the cap is only counted, and nothing
  shrinks a buffer that grew past what the property needs — that is libFuzzer's corpus minimization,
  which never runs on a growth path it found no features for.
- **A starved corpus entry cannot be canonicalized.** `Fuzzer::RunOne` admits an input only on new
  features; `Corpus::AddFeature` counts a feature new only if unseen or carried by a *smaller* input;
  `Corpus.Replace` requires the replacement to be smaller; and `RereadOutputCorpus` applies the same
  rule to files dropped into the corpus directory. An equivalent-but-longer input is therefore
  unreachable by every route libFuzzer offers, so an interesting-but-starved entry keeps its ghost zeros
  for the life of the campaign and `--grow` can only bias mutations of it while it is in hand. Doing
  better needs a hook libFuzzer does not have — AFL++'s `afl_custom_queue_new_entry` rewrites a saved
  queue entry, and JQF/Zest grows the input mid-run and saves the grown form, both because they own the
  scheduling loop. Inside libFuzzer the way out is not a better mutator but a different encoding: a
  self-delimiting choice sequence, where "ran out of bytes" is not a state that exists.
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
- **`Tree`/`genBST` is duplicated** between `BasaltExamples/BST.lean` and
  `BasaltFuzz/BuggyBST.lean`, because the example imports the `Basalt` umbrella for its proofs and so cannot be linked. Moving
  the Mathlib-free part (the datatype and the generator) into a module both import would make the
  fuzzed term the proved term by construction rather than by a pinned test. Two things to settle
  first: the shared `Tree` must be monomorphic or the fuzz side must instantiate it, and `isBST` has
  to exist in both a `Prop` form for the proofs and a `Bool` form for the property (a `decide`
  bridging lemma is the tidy version).
- **Broader instrumentation, other engines.** A target whose coverage of interest lies outside
  `BasaltFuzz` needs the flag on another library — adding `moreLeancArgs` to that `lean_lib`, which
  then also instruments it for every other executable. Per-target instrumentation scope would want a
  Lean-side `lakefile.lean` and a facet override. The `RandomChoice FuzzGen` core is engine-agnostic —
  crowbar shows the same cursor drives AFL — so an AFL or honggfuzz backend changes only the C bridge.

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
- **Mutagen** (Haskell/QuickCheck, [Mista and Russo, ICSTW 2023](https://www.mista.me/assets/pdf/icst23-preprint.pdf))
  is coverage-guided PBT that drives search by *exhaustively* mutating a pool of saved inputs rather
  than by handing an external fuzzer a byte buffer — so it keeps QuickCheck's typed generators and
  needs no byte encoding, at the cost of a bespoke mutation engine per type. It reports beating
  FuzzChick on mutant quality.

Basalt-side reading: `Basalt/RandomChoice.lean` (`choose`), `Basalt/Gen.lean` (the bundle and its
auto-instance), `Basalt/PBT/` (the interpretation-agnostic property and campaign API),
`Basalt/PlausibleGen.lean` and `Basalt/GenStats.lean` (the flat-order `CCPO`/`MonoBind` recipe).
