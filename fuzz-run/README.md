<!--
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Michael Hicks
-->

# `basalt-fuzz`: coverage-guided property testing

The opt-in executable that drives Basalt generators from libFuzzer (parametric fuzzing). It is
**not** built by `lake build`; see [`../BasaltFuzz/DESIGN.md`](../BasaltFuzz/DESIGN.md) for the
design and Appendix A for the supported platforms.

## Build

```bash
fuzz-run/build.sh          # elaborates the Mathlib-free closure, instruments it, links libFuzzer
```

Runs with no arguments on the platforms in `BasaltFuzz/DESIGN.md`'s Appendix A — macOS (arm64),
Amazon Linux 2 (x86_64, the legacy clang-11 box), and Amazon Linux 2023 (x86_64, clang 22 via
`dnf install clang22 compiler-rt22`). The script detects the C driver, the libFuzzer runtime (in
both the legacy and clang-≥14 per-triple layouts), the libc headers the C bridge needs, the C++
runtime, and which driver entry point the bridge should call, so an unlisted platform is likely to
need nothing. Where a machine's toolchain defeats detection, put overrides in `fuzz-run/env.sh`
(git-ignored, sourced first) — `env.example.sh` documents every knob and carries the settings the
Amazon Linux 2 box needs.

If no toolchain-provided libFuzzer runtime is found — the macOS case, since neither Apple's clang
nor Lean's vendored clang ships one — the build calls `get-libfuzzer.sh`, which builds the archive
from compiler-rt's standalone `lib/fuzzer` source into `fuzz-run/vendor/` (a sparse ~1MB checkout,
a few seconds, once). Instrumentation itself needs nothing extra: Lean's vendored clang accepts
`-fsanitize=fuzzer-no-link` on both platforms.

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

All three share one registry and one failure contract — counterexample on stderr, `runs : N (M
discarded)`, exit 77 — so their campaigns are directly comparable. `replay` is fuzz-only: a saved
artifact *is* a `FuzzGen` byte buffer.

### Backend comparison: how fast each finds a bug

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
trials is variance in a geometric distribution, not a distributional difference.

## Failure model and what a run looks like

Failure handling follows **bolero**: on a failing input the counterexample (the generated value,
rendered via `Repr`) is printed and the process `abort()`s, so libFuzzer saves the crashing input as
an artifact and exits nonzero (77). Exit `0` = campaign passed; nonzero = a counterexample was found
and saved. The random backends report the same way and exit 77 too (with no artifact — their input is
a PRNG state, not a buffer).

```
$ fuzz-run/basalt-fuzz bst-buggy-insert -runs=2000000 -max_len=64 -artifact_prefix=./
[basalt-fuzz] starting libFuzzer campaign ([-runs=2000000, -max_len=64, -artifact_prefix=./])
...
*** BASALT PROPERTY FAILED ***
counterexample : (node leaf 1 leaf, 1)          -- insert 1 into a tree that already contains 1
input bytes    : [59, 0, 3]
runs           : 12 (0 discarded)
==...== ERROR: libFuzzer: deadly signal
artifact_prefix='./'; Test unit written to ./crash-<sha1>
```

The counterexample is a *valid* BST plus a key it already contains; `insertBuggy` lacks the
equal-key guard, so it duplicates the key and breaks the invariant.

## Consuming the artifact (reproduction)

The `crash-<sha1>` file is the raw input bytes — the reproduction seed. Consume it by **replaying**:

```
fuzz-run/basalt-fuzz replay bst-buggy-insert crash-<sha1>
```

This re-runs the property on those bytes (no fuzzer), re-deriving and re-printing the same
counterexample. Because `choose` zero-fills past the end of the buffer, the bytes alone reproduce
the failure — drop the `crash-<sha1>` file into a regression directory as a fixture.
