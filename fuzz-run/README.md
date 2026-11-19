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

### The interpretation (`Basalt/Fuzz/Basic.lean`, `Basalt/Fuzz/Encoding.lean`)

`FuzzGen` is `StateT FuzzState Option` over the byte buffer and a read cursor — a *pure* state monad,
so one fuzzer input is a pure function `ByteArray → TestOutcome` (`runOne`). That makes the C
boundary trivial and every input exactly reproducible from its bytes.

The extension point is the usual one: supply the component instances and `Gen FuzzGen` follows by
`inferInstance` (`Basalt/Gen.lean`). The whole interpretation is one `RandomChoice` instance plus the
flat order on `Option`, whose `none` is the bottom that `partial_fixpoint` needs for recursive
generators (`Basalt.PlausibleGen`/`GenStats` use the same recipe with `Except`). There is
deliberately no fuel and no failure case: termination is the generator's own concern, with
libFuzzer's `-timeout`/`-rss_limit_mb` as the backstop for a genuinely divergent one.

Each `choose` call is a *draw*: a range `[lo, hi]`, the bytes it reads, and the *value* they decode
to. `choose` reads the *smallest* number of bytes covering the range and reduces modulo it
(crowbar's encoding), which keeps a tight, mutation-friendly map from corpus bytes to structural
choices. Past the end of the buffer it reads `0`. Both properties matter: `choose` is total, and
*bytes → execution* is deterministic, which is what coverage-guided mutation relies on.

The buffer is finite and a generator's appetite is not, so a run can outrun its bytes. The cursor is
not clamped, so a run reports how many bytes it read (`FuzzResult.cursor`, past the end included) and
how many of those it was not given (`FuzzResult.deficit`, the cursor past the input's length);
[`--truncate`](#truncation) cuts an input
to its cursor before mutating it.

### The C bridge (`Basalt/Fuzz/native.c`, `Basalt/Fuzz/Runner.lean`)

```
 ┌────────────────────── Lean executable (owns main) ───────────────────────┐
 │ main → PBT.dispatch → Fuzz.goFuzz T argv                                 │
 │   T : PropM G Unit          -- the property, polymorphic in the Gen G     │
 │   goFuzz builds run : ByteArray → IO UInt8 for the bridge ────────────┐   │
 │                                                                      ▼   │
 │ RandomChoice FuzzGen          ┌──── C bridge (Basalt/Fuzz/native.c) ────┐ │
 │  choose reads bytes from      │ basalt_fuzz_go(run, argv, truncate):    │ │
 │  FuzzState.buffer/cursor,     │   store run in a global slot            │ │
 │  reading 0 past end-of-buf    │   LLVMFuzzerRunDriver(argc, argv, cb)   │ │
 │      ▲  pure Option state     │ cb = LLVMFuzzerTestOneInput(Data,Size):◀┼─┼┐
 │ FuzzGen α =                   │   arr := ByteArray copy of (Data,Size)  │ ││
 │  StateT FuzzState Option      │   code := run arr        (: IO UInt8)   │ ││
 │      │                        │   1 → (Lean printed it) abort()         │ ││
 │      └─ cursor ───────────────┼─▶ basalt_fuzz_note_cursor(cursor)       │ ││
 │                               │   2 → return -1 (discard) ; else 0      │ ││
 │                               │ LLVMFuzzerCustomMutator(Data,Size,Max): │ ││
 │                               │   --truncate: cut Data to the cursor    │ ││
 │                               │   its run read; then LLVMFuzzerMutate   │ ││
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

Failure handling follows **bolero**: the Lean callback prints the counterexample and returns `1`,
and the bridge `abort()`s, so libFuzzer's signal handler saves the crashing input under
`-artifact_prefix` and exits with its error code (77). Consequences worth knowing: `goFuzz` returns
only `IO Unit` — the campaign's result is the exit code plus the printed report, not a value
returned to the Lean caller (see "Limitations"); and `goFuzz` must be called once per process,
because libFuzzer's driver is not re-entrant.

### Build and instrumentation (`fuzz-run/build.sh`)

Lean's default backend emits one C file per module under `.lake/build/ir/`, and SanitizerCoverage is
a compile-time flag on that C. **Lake owns the closure and the scope.** `basalt-fuzz` is an ordinary
`lean_exe`, so Lake derives the link closure from imports; the instrumentation scope is
`-fsanitize=fuzzer-no-link` in the `moreLeancArgs` of the `Basalt` and `BasaltFuzz` libraries and of
the executable root (`fuzzLeancArgs` in `lakefile.lean`). It is on only under `lake -R -Kfuzz=1`,
which `build.sh` passes, or in a dependent that requires Basalt with the `fuzz` option: Lake
compiles a library's C with that library's flags for any executable that links it, so an
always-instrumented `Basalt` would break the link of every downstream executable (none of them
supplies the libFuzzer runtime). That is every first-party object in the closure and nothing else:
the Lean runtime and stdlib are linked uninstrumented, and so are Plausible's `Gen`/`Random` and
SplitMix, which are the `--backend=plausible`/`io` PRNGs rather than code under test (coverage over a
PRNG's mixing steps is noise in the feedback). Partial coverage still guides libFuzzer. A fuzz build
of Basalt lives in `.lake/build-fuzz`, so it and an ordinary build never overwrite each other's
objects.

The live generator code is not in the module a reader would look in, which is why the scope is a
*library* setting rather than a per-module one. A generator is polymorphic in its monad, so the copy
that actually runs is a specialization emitted into the module that instantiates it — for every
property here, the one holding the registry, `BasaltFuzzMain`. The generic copies left behind in
`Basalt/Combinators.lean` are dead. Instrumenting `BasaltFuzz.+` and the root therefore already
captures the live per-property code; what the `Basalt` library adds is the plumbing those
specializations *call into* — `Basalt/Fuzz/`'s buffer reads, `Combinators.lean`'s loop bodies — which
is what tells libFuzzer that a generator got one iteration further.

`build.sh` supplies what Lake's declarative config cannot — this platform's libFuzzer runtime, its C++
runtime, the compiled C bridge, and three post-link assertions. Each assertion guards a property
whose violation leaves a *working* fuzzer that searches badly rather than a build error: no Mathlib in
Lake's link response file, the instrumentation scope in both directions (every first-party object in
that response file references `__sanitizer_cov_8bit_counters_init`; no dependency object does), and
`LLVMFuzzerCustomMutator` still exported past `-Wl,-dead_strip`. The response file read is Lake's own,
so the scope check covers exactly what was linked: `.lake/build-fuzz/ir/` additionally holds objects
left behind by renamed modules, which enter no link and whose flags say nothing.

### What the instrumentation scope buys

Instrumenting the `Basalt` library costs 25% throughput (137k runs/s against 181k on `bst-gen`) and is
kept because two of the three length benchmarks lose decisively without it. Both binaries built from
one source tree, trials interleaved between the arms so drift cannot land on one of them,
`-len_control=0 -max_len=65536`, macOS arm64 (M-series):

| cell | budget | full scope | `Basalt` uninstrumented | |
|---|---|---|---|---|
| `long-16` | 3,000 runs | **39.7%** ±2.0 | 25.8% ±1.8 | z = +5.1, p = 3e-7 |
| `long-32` | 30,000 | 17.3% ±1.5 | 18.5% ±1.6 | z = −0.5, p = 0.60 |
| `long-32` | 100,000 | 34.0% ±2.4 | 36.0% ±2.4 | z = −0.6, p = 0.55 |
| `long-64` | 120,000 | **25.0%** ±2.5 | 9.3% ±1.7 | z = +5.1, p = 4e-7 |
| `chain-2`/`-3`/`-4` pooled | 1,000 | 51.0% ±2.0 | 53.8% ±2.0 | z = −1.0, p = 0.33 |

600 trials per arm, except 300 for `long-64` and 400 for `long-32` at 100,000. Counters: 11,860 with
the full scope against 4,493 without.

`chain-n` comes out even, as its construction predicts — its guards are in `BasaltFuzz/Staged.lean`,
instrumented either way — and that is also the control that says the `long-16`/`long-64` gaps are the
scope rather than some other difference between the two builds. `long-32` is a dead heat at two
budgets, so the effect is not monotone in the required length. Read the decisive rows, not a pattern
across them: a *null* control (the same binary under two paths, `long-32` at 30,000 runs: 18.3%
against 16.0%, z = +1.1) puts one cell's pass-to-pass spread near 1 SE, which is enough for a single
pass at a single budget to invent a 2-SE effect.

**The link closure must stay Mathlib-free.** A `#eval` runs generators in the interpreter, but a
compiled executable links the native code of its entire import closure, and importing the `Basalt`
umbrella reaches Mathlib through `Basalt.SPMF.Basic` — 1440 modules, against the dozen-odd
first-party ones the fuzzer needs. Generator *definitions* need only `Gen`/`Combinators`; only their
*proofs* need Mathlib. So every module the executable imports imports the narrowest thing it can.
This is also why `Basalt/PlausibleGen.lean` imports `Plausible.Gen` and not the `Plausible` umbrella,
whose tactic frontend and deriving handlers would join the link. `build.sh` asserts that no Mathlib
object is linked.

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

The same script builds another package's fuzz executable — one that requires Basalt and links
`@fuzz-run/obj/link.rsp` as `basalt-fuzz` does — from that package's root; the variables it takes are
documented at its head.

If no toolchain-provided runtime is found — the macOS case, since neither Apple's clang nor Lean's
vendored clang ships one — the build calls `get-libfuzzer.sh`, which builds the archive from
compiler-rt's standalone `lib/fuzzer` source into `fuzz-run/vendor/` (a sparse ~1MB checkout, a few
seconds, once). Instrumentation itself needs nothing extra.

## Run

```bash
fuzz-run/basalt-fuzz [--backend=fuzz|io|plausible|io-cov] <property> [-runs=N] [-discard_ratio=N] [libFuzzer args...]
fuzz-run/basalt-fuzz <property> --truncate                 # fuzz backend only, see below
fuzz-run/basalt-fuzz <property> --hybrid[=N]               # fuzz backend only: random first, see below
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
| `long-16`/`-32`/`-64` | the mirror image: a run of `n` elements where each position accepts half the byte values, so what binds is the buffer's *length* |

Useful libFuzzer flags: `-runs=N` (bounded campaign), `-max_len=N` (input size),
`-artifact_prefix=./` (where crashing inputs are written), a positional dir for a seed/growing
corpus. The random backends read `-runs=N` from the same spelling, plus `-discard_ratio=N` for the
discard budget (`Basalt/PBT/Driver.lean`), and ignore the rest — under `fuzz`, libFuzzer owns the
loop, so a discarded input is a `-1` return and neither budget applies.

`--backend=`, `--truncate` and the [hybrid](#hybrid-campaigns) flags are Basalt's own and are consumed
before libFuzzer sees the command line; everything else is forwarded verbatim, and libFuzzer rejects
a flag it does not know. A `--` flag the chosen backend does not take is a usage error
(`--backend=io --truncate` does not run as a plain random campaign); single-dash flags pass to every
backend, which ignores those it does not read.

## Backends

A Basalt property is polymorphic in its monad, so the *same* property term runs under a coverage-
guided fuzzer or under a plain random sampler; `--backend=` picks the interpretation:

| backend | interpretation | choices come from |
|---|---|---|
| `fuzz` (default) | `Fuzz.FuzzGen` | libFuzzer's mutated byte buffer, guided by coverage |
| `io` | `IO` | SplitMix (`ioGen`) |
| `plausible` | `Plausible.Gen` | Plausible's `StdGen` |
| `io-cov` | `IO` | SplitMix, as `io`, with each test's coverage counted as `fuzz` counts it: the control arm of a coverage comparison |

All of them come from one registry of `Basalt.PBT.Property` and share `Basalt.PBT`'s failure contract,
so their campaigns are directly comparable. Each backend is a `@[basalt_backend]` defined beside its
interpretation, so `dispatch` offers every one `BasaltFuzzMain` imports without listing them. Every
backend reads the same registry: a `Property` keeps its monad open, so no property or generator names
a backend, and each backend's `Gen` instance follows by `inferInstance`. `replay` is fuzz-only,
because a saved artifact *is* a `FuzzGen` byte buffer and has no meaning as a PRNG state.

**Coverage over a campaign.** libFuzzer reports one campaign-wide edge count, which includes
Basalt's own plumbing, and that differs between backends. With `BASALT_COV_OUT=<file>`, `fuzz` and
`io-cov` write every edge of the instrumented code as `<offset> <first run>` at exit (`0`: never hit;
the offset is from the executable base, so `nm` attributes it to a function), and `<file>.time` the
elapsed milliseconds at every 1000th run: coverage as a function of tests and of time, restricted to
whichever functions the comparison is about. Both read the same SanitizerCoverage counters of the same
binary, cleared before each test: libFuzzer clears them for `fuzz`, and `io-cov` itself, in place of
libFuzzer's loop, which a random campaign has no use for and would pay for in time.

### How fast each backend finds a bug

`fuzz-run/compare-backends.sh` measures time-to-first-counterexample, median over 9 trials from a
cold start (fresh process, so libFuzzer begins with an empty corpus). Measured on macOS arm64
(M-series), `MAXRUNS=20000000`, per-trial cap 120s:

| property | fuzz | io | plausible |
|---|---|---|---|
| `threshold` | 13 runs | 3 | 3 |
| `bst-buggy-insert` | 9 runs | 9 | 7 |
| `bst-buggy-insert2` | 36 runs | 2 | 5 |
| `bst-buggy-delete` | 260 runs | 4 | 10 |
| `chain-2` | 497 runs | 48,235 | 70,956 |
| `chain-3` | 1,000 runs | 6,012,768 (8/9 trials) | 12,480,941 (5/9) |
| `chain-4` | 1,109 runs | **not found** (0/9) | **not found** (0/9) |

Two things to know before reading it. A median is over the trials that *found* the bug, so it goes
with the `found` count: where those differ, the backend that found it less often has the more
favourably conditioned median — `chain-3`'s `plausible` column is the conditioned one (5/9 against
8/9) and still the worse of the two. And a run is a *tested* input — a discarded one is budgeted
separately and does not count — which matters for `bst-buggy-delete`, whose precondition rejects most
draws.

Read the two halves separately, because they say opposite things:

- **Shallow bugs: random usually wins, and the margin is noise.** Where one unlucky draw exposes the
  bug, coverage guidance is pure overhead — libFuzzer spends its first inputs mapping coverage, and
  its per-run cost is higher (~137k runs/s vs `io`'s ~820k and `plausible`'s ~300k on `bst-gen`). All
  four BST bugs are of this kind, and every backend finds them in well under a millisecond. Do not
  read the ordering within a row: at a median of single-digit runs the trial-to-trial spread of a
  geometric distribution swamps it, which is why `bst-buggy-insert` here is a three-way tie while the
  other three have the fuzzer behind by 4x to 65x.
- **Staged bugs: only the fuzzer arrives.** `chain-n` puts the bug behind `n` nested guards, so a
  blind sampler needs all `n` to hit at once (`256⁻ⁿ`) while the fuzzer banks one stage at a time and
  pays roughly `n·256`. The cost of a stage is therefore multiplicative for random search and
  additive for the fuzzer: at `n=4` that is about a thousand runs versus 4.3 billion expected, and the
  random backends found nothing in 20M runs × 9 trials. This is the only half of the table where the
  gap is far larger than the noise.

The honest summary is that the backends are complementary, and which wins is a property of the *bug*,
not of the tool: reach for random testing by default because it is simpler and faster per run, and
for the fuzzer when a bug hides behind structure a uniform sampler cannot stumble into. `io` and
`plausible` are both uniform (verified per-draw and pairwise), so the spread between them across
trials is variance in a geometric distribution, not a distributional difference. This is the concrete
argument for the interpretation-polymorphic design: the choice is per-bug, and it costs a flag rather
than a rewrite.

## Truncation

`--truncate` cuts an input to the bytes its run read before libFuzzer mutates it, so that the
mutation lands on bytes the run used (`basalt_truncate`, in `native.c`'s custom mutator). The cut
input runs exactly as the uncut one did, since `byteAt` reads `0` past the end; the same idea is
Zest's `gc()`. Only the input just run is cut: `Fuzzer::MutateAndTestOne` mutates one buffer in
place for up to `-mutate_depth` (5) steps, running each, so a mid-chain input is the run that just
happened, while the input a chain starts from comes from the corpus with no run at hand. The run
report counts the inputs cut and the bytes each lost on average.

It is off by default because it cuts both ways. Where progress means getting the frontier byte's
*value* right (`chain-n`: the run stops at the first wrong byte), a dead tail only dilutes the
mutations. But the tail is dead only for the run that happened: once a mutation changes an earlier
byte the run reads on into it, and where progress means a *longer* run (`long-n`: it ends at a
terminator), the tail is the material the next run needs. `fuzz-run/compare-settings.sh`, 300 campaigns
per cell, `-len_control=0 -max_len=65536`, Amazon Linux 2023 x86_64:

| property | budget | off | `--truncate` |
|---|---|---|---|
| `chain-2` | 500 runs | 27.7% ±2.6 | **40.0%** ±2.8 |
| `chain-3` | 1,000 | 42.7% ±2.9 | **61.7%** ±2.8 |
| `chain-4` | 1,200 | 47.3% ±2.9 | **61.3%** ±2.8 |
| `long-16` | 3,000 | **68.3%** ±2.7 | 53.7% ±2.9 |

On three real targets (Cedar, lean-mc and Strata; the BasaltBench repository) it made no significant
difference to coverage or to injected faults found.

**Why the buffer is not extended instead.** A run that reads past the end gets zeros that are not in
the input, so no byte mutation reaches the positions that produced them. Materializing them before
mutating was measured not to help — on `long-16`/`-32`/`-64`, 31.4% found against
28.2% with it, 1,800 trials — because a zero is a stopping value for most decoders (the first branch of
a `frequency`, an empty structure), so growth plants the value the generator least wants at the
frontier, where libFuzzer's own insertion would have put a random byte; and libFuzzer cannot keep the
extended form as the corpus entry ([Limitations](#limitations-and-future-work)).

Defining a custom mutator has two consequences libFuzzer imposes: it *replaces* the default mutation
suite for the whole campaign (hence the `LLVMFuzzerMutate` delegation), and it makes libFuzzer drop its
`-len_control` length ramp. Basalt keeps the ramp off and raises `-max_len` to 64 KB (`withDefaults`,
`Basalt/Fuzz/Runner.lean`), so an input can grow as long as its generator reads; an explicit flag
always wins. The ramp holds mutations to a few bytes until short inputs stop finding anything, which
costs a generator whose progress is length and buys some search on `chain-n`; at the budgets of the
table above, 300 campaigns per cell:

| property | budget | no ramp (the default) | `-len_control=100` |
|---|---|---|---|
| `chain-3` | 1,000 runs | 41.7% ±2.8 | 50.0% ±2.9 |
| `chain-4` | 1,200 | 53.3% ±2.9 | 66.3% ±2.7 |
| `long-16` | 3,000 | **62.3%** ±2.8 | 24.3% ±2.5 |

**Bound a recursive generator's depth.** Without a ramp nothing holds inputs short, and coverage
rewards a bigger term — it reaches more hit-count features — so a generator whose recursion only the
bytes end (a `frequency` with a recursive branch and no fuel) builds terms as large as `-max_len`
allows, and its tests slow by an order of magnitude. A fuel that bounds the depth, drawn or fixed,
keeps what a run reads bounded however long the input grows; past that, extra bytes are a tail no
run reads, which costs nothing.

## Hybrid campaigns

Random generation and coverage-guided mutation win at different budgets and on different bugs: random
covers breadth cheaply and finds shallow bugs first, and the fuzzer gets behind guards random cannot
stumble through. A *hybrid* campaign runs both in one libFuzzer loop: random first, then fuzzing seeded
with the random tests that reached new coverage, and, under `--hybrid`, back and forth.

| flag | meaning |
|---|---|
| `--hybrid` | switch in both directions by stale effort (below) |
| `--hybrid=N` | switch once, to fuzzing, after `N` random tests: a fixed warm-up, for comparison |

Every round's tests count against the one `-runs` budget, so a campaign is the same length either way.
When a random round's finds are handed to libFuzzer they keep their full recorded length, since no
campaign ramps the length ([Truncation](#truncation)). A ramp asked for with `-len_control`
also cuts a seed longer than its limit as it is handed over; on the real targets the BasaltBench
repository measures (Cedar, lean-mc, Strata), it made no significant difference to a hybrid
campaign.

**A random find has to become a libFuzzer input.** A random round samples each choice from SplitMix,
as `IO` does, at `RecordGen` (`Basalt/Fuzz/Record.lean`), which also writes bytes that `FuzzGen`'s
`choose` decodes back to that choice, picked at random among those that do, so that a seed's bytes
look random to libFuzzer's mutations (`recordDraw`). The buffer is exactly as long as the run read.
Running `FuzzGen` on random bytes instead would bias the choices (one byte modulo 200 makes `0..55`
twice as likely as `56..199`), and it needs a length fixed in advance: a buffer too short reads as
zeros, one too long carries a dead tail. `readNat_recordDraw` proves the decoding per draw; that a
whole run replays is a free theorem of the generator's polymorphism, which `BasaltTest/Fuzz.lean`
pins.

**One loop, two modes.** In a random round the callback (`runOneRandom`, `Runner.lean`) ignores
libFuzzer's buffer, runs the property at `RecordGen`, and returns `-1`, so libFuzzer neither keeps
the input nor records its features (`basalt_hy_random_test`, `native.c`). The bridge checks the test
for new coverage itself (`basalt_hybrid_judge`), by libFuzzer's notion of a feature: an edge and its
hit-count bucket. A *find* is a test that reached a feature no earlier test of either mode did. On
the switch to fuzzing (`basalt_hy_switch`) the round's finds are reduced by greedy set cover over
the features that round discovered (`Basalt/Fuzz/Cover.lean`, which proves the cover reaches all of
them; admission one test at a time cannot drop a seed a later one subsumes), and the custom mutator
hands them to libFuzzer one per call (`basalt_hy_mutate`), so each enters the corpus by libFuzzer's
own rule. When fuzzing hands back to random, libFuzzer's corpus stays in memory, and the next
fuzzing round resumes from it with the new finds added (libFuzzer has no call to empty it).

**The stale rule** (`basalt_hy_step`) ends a round, in either mode, once it has gone `E` tests
without a find, and never before 256 tests (`BASALT_STALE_FLOOR`). `E = L̄ · ln L̄`
(`basalt_stale_effort`), `L̄` the finds' mean length in bytes: libFuzzer's mutations land at random
positions, so touching each of an input's `L̄` bytes once takes about `L̄ · ln L̄` of them (the
coupon collector's bound). Fuzzing spends that on every corpus input, so its `E` is multiplied by
the number of finds, which stands in for the corpus's size (libFuzzer exposes no corpus API; finds
somewhat overstate it, which only makes fuzzing judged a little more patiently). Each mode is judged
by its own effort since its round began, never by its rate against the other's, since each inherits
most of its coverage from the other. Nothing in the rule depends on the budget, so it works the same
without `-runs`. Its cost is the floor: on a target where random finds nothing, every random round
still runs its 256 tests.

**Measured.** `fuzz-run/compare-settings.sh`, 300 campaigns per cell, Amazon Linux 2023 x86_64,
`-len_control=0 -max_len=65536` throughout:

| property | budget | fuzzing only | `--hybrid` | `--hybrid=100` |
|---|---|---|---|---|
| `chain-3` | 1,000 runs | 46.3% ±2.9 | **83.3%** ±2.2 | 58.3% ±2.8 |
| `chain-4` | 1,200 | 50.0% ±2.9 | **73.0%** ±2.6 | 63.3% ±2.8 |
| `long-16` | 3,000 | 71.7% ±2.6 | 49.7% ±2.9 | **75.0%** ±2.5 |

`chain-n`'s first guard is a uniform 1-in-256 byte, which random hits at exactly that rate while
libFuzzer, starting from an empty input, must first insert a byte and get its value right: random banks
the first stage and hands over a seed already past it. `long-16` is the cost of the floor: random never
reaches a long run, and every random round still takes 256 tests, so the modes alternate and random
takes a large share of a small budget. These benchmarks put one bug behind nested guards, so they
measure depth, not the breadth a hybrid is for; the BasaltBench repository measures that, on proved
generators driving Cedar, lean-mc and Strata.

Three consequences. A counterexample found in a random round is written as `crash-random-<n>` under
`-artifact_prefix` and replays like any other artifact, because it *is* a `FuzzGen` buffer; the
bridge exits past libFuzzer's exit hook, which would otherwise save the buffer in hand — not that
test's input — as the crash. Whether a random test reached new coverage is checked on the code that
runs then, which includes the generator's `RecordGen` specialization rather than its `FuzzGen` one;
libFuzzer checks each seed again when it is handed over, so the cost is keeping seeds a `FuzzGen`
run would not have, never losing one it would, though those finds also count toward the stale rule's
`E`. And the budget is in tests, not time: a random test is cheaper than a fuzzing one, which
`-max_total_time` does not see.

## What a run looks like

Exit `0` = campaign passed; nonzero = a counterexample was found (and, for the fuzz backend, saved).
The random backends report the same way and exit 77 too, with no artifact — their input is a PRNG
state, not a buffer.

```
$ fuzz-run/basalt-fuzz bst-buggy-insert -runs=2000000 -artifact_prefix=./
[basalt] starting libFuzzer campaign ([-runs=2000000, …, -len_control=0, -max_len=65536])
...
*** BASALT PROPERTY FAILED ***
counterexample : (BuggyBST.Tree.node (...leaf) 1 (...leaf), 1)
input bytes    : [239]
runs           : 18 (0 discarded)
buffer         : 1 bytes, 3 short
[basalt] runs 18, starved 10 (max deficit 3 B)
==...== ERROR: libFuzzer: deadly signal
artifact_prefix='./'; Test unit written to ./crash-<sha1>
```

The counterexample (`Repr`-rendered, hence fully qualified) is a *valid* BST plus a key it already
contains; `insertBuggy` lacks the equal-key guard, so it duplicates the key and breaks the invariant.

The `buffer` row says this input asked for 4 bytes and got 1, and the `[basalt] runs …` line that 10
of the 18 runs went short (under `--truncate` it also counts the inputs cut). The `[basalt]` line comes
from C, on stderr, and is printed at both exits (here past `abort()`; on the `-runs`-exhausted path
from an `atexit` handler). libFuzzer's own `MS:` lines end in `Custom-`, because the mutator is linked
unconditionally and delegates.

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
`byteAt`, not a campaign setting, so an artifact means the same thing however it was produced.

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
vendored clang, so no `LEAN_CC` wrapper; its runtime, in the per-triple dir, is used when its major
matches Lean's clang, and otherwise the from-source fallback builds one with the versioned
`clang++-22`. That fallback is why `get-libfuzzer.sh` compiles `-fPIC` unconditionally (`leanc` links
a PIE, and a non-PIC runtime object fails with `relocation R_X86_64_32 cannot be used against local
symbol`).

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

- **A starved corpus entry cannot be canonicalized.** `Fuzzer::RunOne` admits an input only on new
  features; `Corpus::AddFeature` counts a feature new only if unseen or carried by a *smaller* input;
  `Corpus.Replace` requires the replacement to be smaller; and `RereadOutputCorpus` applies the same
  rule to files dropped into the corpus directory. An equivalent-but-longer input is therefore
  unreachable by every route libFuzzer offers, so an interesting-but-starved entry keeps its ghost zeros
  for the life of the campaign, and extending it can only bias mutations of it while it is in hand. Doing
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
- **No in-process campaign result.** A failure `abort()`s, so `goFuzz` cannot return a `TestOutcome`;
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
  `BasaltFuzz/BuggyBST.lean`; `BasaltTest/Fuzz.lean` says why and pins the copies. Moving the
  Mathlib-free part (the datatype and the generator) into a module both import would make the
  fuzzed term the proved term by construction rather than by a pinned test. Two things to settle
  first: the shared `Tree` must be monomorphic or the fuzz side must instantiate it, and `isBST` has
  to exist in both a `Prop` form for the proofs and a `Bool` form for the property (a `decide`
  bridging lemma is the tidy version).
- **Narrower instrumentation, other engines.** The scope is per *library*, so the choice above is
  all-or-nothing for `Basalt`: a target that wanted its plumbing uninstrumented (for the 25% of
  throughput) while keeping it for a length-bound generator cannot have both from one `-Kfuzz`
  build. Per-target instrumentation scope would want a facet override in `lakefile.lean`. The
  `RandomChoice FuzzGen` core is engine-agnostic — crowbar shows the same cursor drives AFL — so an
  AFL or honggfuzz backend changes only the C bridge.

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
`Basalt/PlausibleGen.lean` and `Basalt/GenStats/Basic.lean` (the flat-order `CCPO`/`MonoBind` recipe).
