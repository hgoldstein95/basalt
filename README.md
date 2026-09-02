# Basalt

Basalt is a foundational representation of random data generators for property-based testing (PBT),
together with machine-checked proofs about them, in Lean 4. A single generator term is given a
precise semantics you can both run and reason about, so a generator can be proved sound, complete,
almost-surely terminating, and cost-bounded.

> This is research code. APIs are unstable and may change without notice.

## Generator Representation

A generator is a term polymorphic in its monad, not a value of a fixed generator type:

```lean
def myGen [Gen G] : G α := ...
```

`Gen` bundles the operations a generator needs (`Monad`, `RandomChoice`, `CCPO`, `MonoBind`,
`Inhabited`). The *same* term is then interpreted at whichever monad the task calls for:

| Interpretation | What it gives you |
|---|---|
| `Plausible.Gen` / `IO` | run it and get values |
| `SPMF` | a sub-probability mass function — reason about the distribution and its `support` |
| `SPMF.Cost` | the same, plus a count of random choices |
| `GenStats.StatGen` | seeded, fuel-guarded execution that counts choices (drives `#genstats`) |
| `Fuzz.FuzzGen` | choices read from a byte buffer, so a coverage-guided fuzzer drives generation |

`RandomChoice.choose` is the only source of randomness; every combinator (`pick`, `elements`,
`oneOf`, `frequency`, `listOf`, …) is built on it. Recursive generators are defined by
`partial_fixpoint` over the `CCPO`.

## Correctness Properties

`Basalt/Laws.lean` states the properties a generator may have as plain predicates; which apply
depends on the generator, and you prove the ones that do:

- `IsSoundAndComplete g P` — the support of `g` is exactly `P` (nothing invalid, nothing missed).
- `IsAlmostSurelyTerminating g` — `g` terminates with probability 1.
- `IsCostBounded g c` — producing `v` takes at most `c v` random choices.
- `IsFilterFree g` / `IsProductive g` — for filtering (`Option`-valued) generators.

`BasaltExamples/` is a cookbook of worked generators, each carrying proofs of the properties that
apply to it. `WORKFLOW.md` walks through writing a generator and proving it correct, with a recipe
for each obligation.

## Running Properties

Generators are the inputs of property-based tests; `Basalt/PBT/` is the other half. A property is a
generator of `TestOutcome`, so it is polymorphic in its monad too, and its inputs are drawn with
ordinary monadic `do` — several of them, or dependent ones, need no special combinator:

```lean
def prop_takeDrop [Gen G] : G TestOutcome := do
  let xs ← listOf (chooseNat 0 99)
  let k ← chooseNat 0 99
  if xs.isEmpty then return .discard
  checkWith (xs.take k ++ xs.drop k == xs) (fun () => s!"xs={xs}, k={k}")
```

A campaign runs a property at a chosen interpretation, stopping at the first counterexample:

```lean
#eval ioCampaign (fun _ => prop_takeDrop) 1000
```

Because the property never named an interpretation, the same term is testable at each of them: a
`Property` is the property held polymorphically, and `Backend` / `dispatch` wrap a registry of named
properties in a command line (`--backend=io|plausible`, `-runs=N`). Every backend shares one failure
contract — counterexample on stderr, exit `77` — so campaigns are comparable across them.

## Build

Lean and Mathlib are pinned in `lean-toolchain` / `lakefile.toml` / `lake-manifest.json`.

```sh
lake build                # library + examples + tests
lake build Basalt         # library only
lake build BasaltExamples # the cookbook
lake build BasaltTest     # regression tests
```

### Coverage-guided fuzzing (opt-in)

`basalt-fuzz` drives generators from libFuzzer instead of a PRNG. It links native code, so building
the *executable* is deliberately outside `lake build` and has its own script — which needs no
arguments on the platforms `fuzz-run/README.md` lists, detecting the toolchain's fuzzing runtime and
driver entry point itself:

```sh
fuzz-run/build.sh                                   # build the executable
fuzz-run/basalt-fuzz <property> [libFuzzer args...]  # run a campaign
fuzz-run/basalt-fuzz replay <property> <file>        # reproduce a saved crash input
```

Where no libFuzzer runtime ships with the toolchain (macOS), the build vendors one from
compiler-rt source on first use. Per-machine toolchain overrides go in `fuzz-run/env.sh`
(see `fuzz-run/env.example.sh`). `fuzz-run/README.md` is the whole story: the design, the demo
properties, the failure model, and the supported platforms.

Because a property is polymorphic in its monad, the same executable also runs it under the random
interpretations — `--backend=io` or `--backend=plausible` instead of the default coverage-guided
`fuzz` — from one shared property registry. Which backend finds a bug faster is a property of the
bug: random testing wins on shallow bugs (fewer runs, ~3–5× the throughput), while a bug behind
several nested guards is reachable only by the fuzzer. `fuzz-run/compare-backends.sh` measures it and
`fuzz-run/README.md` records the numbers.

## Repository layout

- `Basalt/` — the library.
- `BasaltExamples/` — worked generators with correctness proofs. Because each file proves its
  generator's laws, this directory is also most of the effective regression suite for the library's
  lemma sets and tactics.
- `BasaltTest/` — regression tests, named for the library module they guard when one exists;
  `LawLine.lean` has no library counterpart (it pins the `#genstats` law-reporting contract).
- `BasaltExperiments/` — spikes; the only place with `sorry`s, and not built by default.
- `BasaltFuzz/` — the Mathlib-free fuzzing targets (generators and properties the `basalt-fuzz`
  executable links). The interpretation itself is `Basalt/Fuzz/`.
- `fuzz-run/` — the `basalt-fuzz` build script, its backend benchmark, and `README.md`, which owns
  the fuzzing design and the per-platform build contract.

## License

Released under the MIT license; see `LICENSE`.

If you are interested in this work, please get in touch with Harry Goldstein.
