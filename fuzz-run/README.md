# `basalt-fuzz`: coverage-guided property testing

The opt-in executable that drives Basalt generators from libFuzzer (parametric fuzzing). It is
**not** built by `lake build`; see [`../FUZZING-DESIGN.md`](../FUZZING-DESIGN.md) for the design and
Appendix A for the toolchain this box needs.

## Build

```bash
fuzz-run/build.sh          # elaborates the Mathlib-free closure, instruments it, links libFuzzer
```

## Run

```bash
fuzz-run/basalt-fuzz <property> [libFuzzer args...]
fuzz-run/basalt-fuzz replay <property> <file>      # reproduce a saved input, no fuzzer
```

Properties (see `BasaltFuzzMain.lean` and `BasaltFuzz/BST.lean`):

| property | expectation |
|---|---|
| `threshold` | infra self-test; a false property libFuzzer quickly falsifies |
| `bst-gen` | `genBST` only makes valid BSTs — never fails |
| `bst-insert` | the correct `insert` preserves the BST invariant — never fails |
| `bst-buggy-insert` | the buggy `insert` does **not** preserve it — libFuzzer finds a counterexample |
| `bst-insert2` | correct `insert` of two *distinct* keys (composed, multi-input) — never fails |
| `bst-buggy-insert2` | the buggy `insert` of two distinct keys — counterexample reports `(t, k1, k2)` |

Useful libFuzzer flags: `-runs=N` (bounded campaign), `-max_len=N` (input size),
`-artifact_prefix=./` (where crashing inputs are written), a positional dir for a seed/growing
corpus.

## Failure model and what a run looks like

Failure handling follows **bolero**: on a failing input the counterexample (the generated value,
rendered via `Repr`) is printed and the process `abort()`s, so libFuzzer saves the crashing input as
an artifact and exits nonzero (77). Exit `0` = campaign passed; nonzero = a counterexample was found
and saved.

```
$ fuzz-run/basalt-fuzz bst-buggy-insert -runs=2000000 -max_len=64 -artifact_prefix=./
[basalt-fuzz] starting campaign ([-runs=2000000, -max_len=64, -artifact_prefix=./])
...
*** BASALT PROPERTY FAILED ***
counterexample : (node leaf 1 leaf, 1)          -- insert 1 into a tree that already contains 1
input bytes    : [59, 0, 3]
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
