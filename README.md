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
| `WordModel σ` / `IOModel` | `IO`'s draws with the PRNG state threaded purely — what `IsFaithful` (below) relates `IO` and `SPMF` through |
| `SPMF` | a sub-probability mass function — reason about the distribution and its `support` |
| `SPMF.Cost` | the same, plus a count of random choices |
| `GenStats.StatGen` | seeded, fuel-guarded execution that counts choices (drives `#genstats`) |
| `Fuzz.FuzzGen` | choices read from a byte buffer, so a coverage-guided fuzzer drives generation |

`RandomChoice.choose`, a uniform draw, and `RandomChoice.pick`, a weighted choice of an index, are the
only sources of randomness. `frequency` is built on `pick`, and every other combinator (`elements`,
`oneOf`, `listOf`, …) on `choose`. An interpretation that reads weights as more than a draw, such as
an enumeration, sees each weighted choice whole. Every interpretation a proof reads is
`RandomChoice.LawfulPick`: its `pick` is its `choose` below the total weight. Recursive generators are defined by
`partial_fixpoint` over the `CCPO`. A choice between literal branches is written `oneOf! [g₀, g₁, …]`
or `frequency! [(w₀, g₀), …]`: it runs as a chain of tests on the drawn index, allocating no list of
branches or weights, while every proof sees the plain `oneOf` / `frequency` (`Basalt/Combinators.lean`).

A generator that branches on a size adds a `[Sized G]` constraint and reads it with `getSize` or
`Sized.sized`, shrinking it for recursive calls with `Sized.resize` (plus `[MonoSized G]` when the
generator is a `partial_fixpoint`). `WithSize G` supplies the size to any interpretation `G`: run
the generator at `WithSize G` and close it with `.run n`. See `Basalt/Sized.lean`.

## Correctness Properties

`Basalt/Laws.lean` states the properties a generator may have as plain predicates; which apply
depends on the generator, and you prove the ones that do:

- `IsSoundAndComplete g P` — the support of `g` is exactly `P` (nothing invalid, nothing missed).
  Its halves are laws of their own: `IsSoundFor g P` (nothing invalid) and `IsCompleteFor g P`
  (nothing missed), for a generator that has only one.
- `IsAlmostSurelyTerminating g` — `g` terminates with probability 1.
- `IsCostBounded g c` — producing `v` takes at most `c v` random choices.
- `IsExpectedCostBounded g B` — producing a value takes at most `B` random choices on average, so a
  generator that sometimes retries is allowed. With `IsAlmostSurelyTerminating` and a finite `B`,
  it says that `g` terminates positively almost surely.

A proof restates a law on an observation with its `iff_obs` lemma and runs `walk`
(`Basalt/Laws.lean`, `WORKFLOW.md`).

Two more relate two interpretations rather than constraining one, so they take the polymorphic
generator:

- `IsFaithful gen` (`Basalt/IO/Laws.lean`) — on any ideal source of words, `gen` has its `SPMF`
  distribution, and at `IO` it runs as `IOModel` does wherever that terminates. This connects the
  proofs about `SPMF` to what `IO` runs; what it leaves out is `idealized_faithful`'s
  (`Basalt/IO/Faithful.lean`).
- `IsCostFaithful gen` — `gen` at `SPMF.Cost`, its costs dropped, has its `SPMF` distribution, so
  a law at one interpretation can be read at the other: termination gives the cost interpretation
  mass `1`, which a lower bound on an expected cost needs.

`BasaltExamples/` is a cookbook of worked generators, each carrying proofs of the properties that
apply to it. `WORKFLOW.md` walks through writing a generator and proving it correct, with a recipe
for each law, and one for bounding an expected value (`SPMF.expect`, such as the expected
size of what is generated).

## Running Properties

Generators are the inputs of property-based tests; `Basalt/PBT/` is the other half. A property lives
in `PropM G`, a generator monad that can *reject* the input it drew, so it is polymorphic in its
monad too. Its inputs are drawn with `generate` in an ordinary monadic `do` — several of them, or
dependent ones, need no special combinator:

```lean
def prop_takeDrop [Gen G] : PropM G Unit := do
  let xs ← generate (listOf (chooseNat 0 99))
  let k ← generate (chooseNat 0 99)
  assume !xs.isEmpty                              -- a precondition; discards this input
  check (xs.take k ++ xs.drop k == xs) s!"xs={xs}, k={k}"
```

Rejecting short-circuits, so `assume` is a statement rather than a nesting, and it holds through a
*function call* — a helper the property calls can reject the input on its behalf. `forAll gen p` is
the alternative to `generate`: it names the drawn value in the counterexample, and nests, with `p`
returning a property, a `Bool`, or a decidable `Prop`.

A campaign runs a property at a chosen interpretation, stopping at the first counterexample:

```lean
#eval ioCampaign (fun _ => prop_takeDrop) 1000
```

Because the property never named an interpretation, the same term is testable at each of them: a
`Property` is the property held polymorphically, and `dispatch` wraps a list of named properties in a
command line (`--backend=io|plausible`, `-runs=N`, `-discard_ratio=N`) over every `Backend` tagged
`@[basalt_backend]` that the caller imports. `Basalt/PBT/` names no interpretation: each backend
lives with its own (`Basalt/IO/Backend.lean`, `Basalt/PlausibleGen/Backend.lean`), so an
interpretation defined outside Basalt is offered the same way. Every backend shares one failure
contract — counterexample on stderr, exit `77` — so campaigns are comparable across them.

## Build

Lean and Mathlib are pinned in `lean-toolchain` / `lakefile.toml` / `lake-manifest.json`.

```sh
lake build                # library + examples + tests
lake build Basalt         # library only
lake build BasaltExamples # the cookbook
lake build BasaltTest     # regression tests
lake check                # CI's axiom check (macOS: --inadvisably-no-sandbox)
```

### Using Basalt from a module

Basalt is written in Lean's module system; a file that is not a `module` imports it as before. In a
`module`:

- A generator proved about from another module must be exposed (`@[expose]`).
- Running a generator at elaboration time (`#eval`, `#genstats`) needs a `meta import` of each module
  whose code runs.

### Coverage-guided fuzzing (opt-in)

`basalt-fuzz` drives generators from libFuzzer instead of a PRNG. It links native code, so it has
its own build script, `fuzz-run/build.sh`, and `lake build` does not build it:

```sh
fuzz-run/build.sh                                   # build the executable
fuzz-run/basalt-fuzz <property> [libFuzzer args...]  # run a campaign
fuzz-run/basalt-fuzz replay <property> <file>        # reproduce a saved crash input
```

The same executable also runs a property under the random interpretations (`--backend=io` or
`--backend=plausible`). `fuzz-run/README.md` is the whole story: the design, the demo properties,
the failure model, the supported platforms, and how fast each backend finds a bug.

## Repository layout

- `Basalt/` — the library, in four tiers:
  - *the representation*: `RandomChoice.lean`, `Gen.lean`, `Sized.lean`, `Combinators.lean`, and
    `Laws.lean`, the properties a generator may be proved to have;
  - *the interpretations*: `SPMF/` (the distribution semantics and its theory — support, mass,
    expectations, cost, almost-sure termination), `IO.lean` and `IO/` (with `IsFaithful`),
    `PlausibleGen.lean` and `PlausibleGen/`, `OptionT.lean`, `GenStats/`, and the opt-in `Fuzz/`,
    with `Random.lean` holding `stdChoose`, the exactly uniform draw from core's `StdGen` that
    `GenStats/` makes;
  - *the proof machinery*:
    - `Obs/`, the layer every per-combinator lemma is derived from. A judgment about a generator
      (its support, an expectation, a cost bound) is an *observation*: a `choose`-preserving monad
      morphism into a specification monad. Each combinator has one lemma saying that every
      observation commutes with it.
    - `Walk/`, the walk over observations that discharges every proof obligation: its `walk`
      tactic, and one file per judgment of what the walk knows about it.
    - `GenRel/Basic.lean`, the structure of a relation between two interpretations that the walk
      relates construct by construct, and `GenRel.lean`, each combinator related to itself under
      every such relation.
    - `Order.lean`, the definition of admissibility that fixpoint-induction proofs unfold;
  - *what a proof calls*: `walk`, and `Tactic/`, the tactics that do more than walk
    (`mass_fixpoint`, `faithful_fixpoint`) plus `support_simp` and `cost_support_simp`; and `PBT/`
    and `Tuning/`, the front ends above.

  `Basalt.lean` is the only module that imports the library wholesale; every other module, inside
  the library and out, imports the narrowest thing it needs.
- `BasaltExamples/` — worked generators with correctness proofs. Because each file proves its
  generator's laws, this directory is also most of the effective regression suite for the library's
  lemma sets and tactics.
- `BasaltTest/` — regression tests, named for the library module they guard when one exists.
- `BasaltFuzz/` — the generators, properties, and buggy operations the `basalt-fuzz` executable
  fuzzes. It is linked into a native executable; `fuzz-run/README.md` owns what that requires.
- `BasaltFuzzMain.lean` — the root of the opt-in `basalt-fuzz` executable: the property registry.
  Not a default build target, since only `fuzz-run/build.sh` links it.
- `fuzz-run/` — the `basalt-fuzz` build script, its backend benchmark, and `README.md`, which owns
  the fuzzing design and the per-platform build contract.
- `docs/` — the project's web page (`index.html`) and `representation.md`, the background on
  generator representations and how Basalt's relates to them.

## License

Released under the MIT license; see `LICENSE`.

If you are interested in this work, please get in touch with Harry Goldstein.
