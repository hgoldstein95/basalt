/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Michael Hicks, Harrison Goldstein
-/
import Basalt.PBT.Driver
import Basalt.PlausibleGen

/-!
# Testing a Property at `Plausible.Gen`

The `plausible` backend: a campaign whose choices come from Plausible's `StdGen`.
-/

namespace Basalt.PBT

/-- Test `T` at `Plausible.Gen`, where choices come from Plausible's `StdGen`.

The `size` handed to `Plausible.Gen.run` is inert: Basalt generators bound their own recursion (via
`partial_fixpoint`) and no combinator reads Plausible's size parameter. -/
def plausibleCampaign (T : Property) (runs : Nat) (maxDiscardRatio : Nat := 10) : IO Unit :=
  campaign "Plausible.Gen" (Plausible.Gen.run (runProp (T Plausible.Gen)) 0) runs maxDiscardRatio

/-- Uniform random testing at `Plausible.Gen`. -/
@[basalt_backend]
def plausibleBackend : Backend where
  name := "plausible"
  campaign T argv := plausibleCampaign T (runsOf argv) (discardRatioOf argv)

end Basalt.PBT
