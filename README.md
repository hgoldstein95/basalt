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

## Build

Lean and Mathlib are pinned in `lean-toolchain` / `lakefile.toml` / `lake-manifest.json`.

```sh
lake build                # library + examples + tests
lake build Basalt         # library only
lake build BasaltExamples # the cookbook
lake build BasaltTest     # regression tests
```

## Repository layout

- `Basalt/` — the library.
- `BasaltExamples/` — worked generators with correctness proofs. Because each file proves its
  generator's laws, this directory is also most of the effective regression suite for the library's
  lemma sets and tactics.
- `BasaltTest/` — regression tests, named for the library module they guard when one exists;
  `LawLine.lean` has no library counterpart (it pins the `#genstats` law-reporting contract).
- `BasaltExperiments/` — spikes; the only place with `sorry`s, and not built by default.

## License

Released under the MIT license; see `LICENSE`.

If you are interested in this work, please get in touch with Harry Goldstein.
