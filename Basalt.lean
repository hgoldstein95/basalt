/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt.Combinators
import Basalt.Gen
import Basalt.GenRel
import Basalt.GenStats.Basic
import Basalt.GenStats.Command
import Basalt.IO
import Basalt.IO.Approx
import Basalt.IO.Choose
import Basalt.IO.Faithful
import Basalt.IO.Ideal
import Basalt.IO.Laws
import Basalt.IO.SplitMix
import Basalt.IO.Stream
import Basalt.Laws
import Basalt.Obs.Basic
import Basalt.Obs.Combinators
import Basalt.Obs.Ordered
import Basalt.Obs.Presentation
import Basalt.Obs.Spec
import Basalt.OptionT
import Basalt.PBT.Backend
import Basalt.PBT.Campaign
import Basalt.PBT.Driver
import Basalt.PBT.Property
import Basalt.PlausibleGen
import Basalt.Random
import Basalt.RandomChoice
import Basalt.SPMF.Basic
import Basalt.SPMF.Cost
import Basalt.SPMF.Expect.Basic
import Basalt.SPMF.Expect.Combinators
import Basalt.SPMF.Expect.Obs
import Basalt.SPMF.Failure
import Basalt.SPMF.Mass
import Basalt.SPMF.Ranking
import Basalt.SPMF.Support
import Basalt.SPMF.Termination
import Basalt.Sized
import Basalt.Tactic.Average
import Basalt.Tactic.Complete
import Basalt.Tactic.Cost
import Basalt.Tactic.ENNReal
import Basalt.Tactic.Expect
import Basalt.Tactic.Faithful
import Basalt.Tactic.IO
import Basalt.Tactic.Ideal
import Basalt.Tactic.Mass
import Basalt.Tactic.MassFixpoint
import Basalt.Tactic.Sound
import Basalt.Tactic.Support
import Basalt.Tuning.Attr
import Basalt.Tuning.Basic
import Basalt.Walk.Attr
import Basalt.Walk.Basic
import Basalt.Walk.Entry

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
