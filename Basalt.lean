/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
module

public import Basalt.Backtrack
public import Basalt.Combinators
public import Basalt.Enum
public import Basalt.Fail
public import Basalt.Gen
public import Basalt.GenRel
public import Basalt.GenRel.Basic
public import Basalt.GenStats.Basic
public import Basalt.GenStats.Command
public import Basalt.IO
public import Basalt.IO.Approx
public import Basalt.IO.Backend
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
public import Basalt.PlausibleGen.Backend
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
public import Basalt.Walk.Entry
public import Basalt.Walk.Expect
public import Basalt.Walk.ExpectedCost
public import Basalt.Walk.Mass
public import Basalt.Walk.Match
public import Basalt.Walk.Names
public import Basalt.Walk.Sound

/-!
# Basalt

The library root, and the only module that imports the library wholesale: it lists every module
except `Basalt.Fuzz.*`, the opt-in coverage-guided fuzzing bridge, whose backend is only usable from
the `basalt-fuzz` executable (`fuzz-run/README.md`). `docs/representation.md` relates Basalt's
generator representation to QuickCheck, QuickChick, and free generators.
-/
