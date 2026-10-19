/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
module

public import Basalt.Combinators
public import Basalt.Gen
public import Basalt.GenRel
public import Basalt.GenStats.Basic
public import Basalt.GenStats.Command
public import Basalt.IO
public import Basalt.IO.Approx
public import Basalt.IO.Choose
public import Basalt.IO.Faithful
public import Basalt.IO.Ideal
public import Basalt.IO.Laws
public import Basalt.IO.SplitMix
public import Basalt.IO.Stream
public import Basalt.Laws
public import Basalt.Obs.Basic
public import Basalt.Obs.Combinators
public import Basalt.Obs.Ordered
public import Basalt.Obs.Presentation
public import Basalt.Obs.Spec
public import Basalt.OptionT
public import Basalt.Order
public import Basalt.PBT.Backend
public import Basalt.PBT.Campaign
public import Basalt.PBT.Driver
public import Basalt.PBT.Property
public import Basalt.PlausibleGen
public import Basalt.Random
public import Basalt.RandomChoice
public import Basalt.SPMF.Basic
public import Basalt.SPMF.Cost
public import Basalt.SPMF.CostErasure
public import Basalt.SPMF.Expect.Basic
public import Basalt.SPMF.Expect.Combinators
public import Basalt.SPMF.Expect.Obs
public import Basalt.SPMF.Mass
public import Basalt.SPMF.Ranking
public import Basalt.SPMF.Support
public import Basalt.SPMF.Termination
public import Basalt.Sized
public import Basalt.Tactic.Faithful
public import Basalt.Tactic.MassFixpoint
public import Basalt.Tactic.Support
public import Basalt.Tuning.Attr
public import Basalt.Tuning.Basic
public import Basalt.Walk.Attr
public import Basalt.Walk.Average
public import Basalt.Walk.Basic
public import Basalt.Walk.Complete
public import Basalt.Walk.Cost
public import Basalt.Walk.CostErasure
public import Basalt.Walk.Entry
public import Basalt.Walk.Expect
public import Basalt.Walk.ExpectedCost
public import Basalt.Walk.IO
public import Basalt.Walk.Ideal
public import Basalt.Walk.Mass
public import Basalt.Walk.Match
public import Basalt.Walk.Names
public import Basalt.Walk.Sound

/-!
# Basalt

This library provides comprehensive infrastructure for ergonomically representing PBT generators and
proving them correct.

If you want to make sure that a generator is correct, or if you plan to automate the production of
generators (e.g., via classical program synthesis or LLM automation), this library provides a
foundation.

Generator writers should look at the `Gen` module to see the operations available in generators. For
proving generators correct, look at `Basalt.Laws` and the examples in `BasaltExamples/`.

This is the library root, and the only module that imports the library wholesale: it lists every
module except `Basalt.Fuzz.*`, the opt-in coverage-guided fuzzing bridge, whose backend is only
usable from the `basalt-fuzz` executable (`fuzz-run/README.md`).

## Main Definitions

- `SPMF` — A type of sub-probability mass functions.
- `RandomChoice` — A type class capturing random choices.
- `Gen` — A type class capturing all of the operations necessary for PBT generators.
- `Sized` / `WithSize` — An ambient size parameter for generators, and a monad that supplies one.
- `Basalt.Laws` - Correctness properties that a `Gen` may be proved to have.

For information about how Basalt's generator representation relates to QuickCheck, QuickChick, and
free generators, see `docs/representation.md`.
-/
