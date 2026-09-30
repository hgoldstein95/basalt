/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Segev Elazar Mittelman
-/
import Plausible.Arbitrary
import Plausible.ArbitraryFueled
import Basalt.Arbitrary
import Basalt.PlausibleGen

/-!
# Plausible's Lookup Classes from Basalt's

A Basalt `Arbitrary`/`ArbitraryFueled` instance is a Plausible one at `G := Plausible.Gen`, and a
`BacktrackGen` runs at `Plausible.Gen` by turning its failures into Plausible's. The instances are low
priority, so a native Plausible instance keeps winning and an existing test's distribution is unchanged.
-/

namespace BacktrackGen

/-- Run at `Plausible.Gen`, throwing `Gen.genericFailure` for `refuted` and `Gen.outOfFuel` for
`exhausted`, so a caller that classifies Plausible's errors can still tell them apart. -/
def toPlausibleGen (x : BacktrackGen Plausible.Gen α) : Plausible.Gen α := do
  match ← x.run with
  | .ok a => pure a
  | .refuted => throw Plausible.Gen.genericFailure
  | .exhausted => throw Plausible.Gen.outOfFuel

end BacktrackGen

instance (priority := low) [Basalt.Arbitrary α] : Plausible.Arbitrary α where
  arbitrary := Basalt.Arbitrary.arbitrary (G := Plausible.Gen)

/-- Plausible's own `ArbitraryFueled → Arbitrary` instance then takes the fuel from its size. -/
instance (priority := low) [Basalt.ArbitraryFueled α] : Plausible.ArbitraryFueled α where
  arbitraryFueled n := Basalt.ArbitraryFueled.arbitraryFueled (G := Plausible.Gen) n
