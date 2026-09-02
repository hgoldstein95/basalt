/-
Copyright (c) 2026 Michael Hicks. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Michael Hicks
-/
import Basalt.Gen
-- Not the `Plausible` umbrella: its tactic frontend would join the `basalt-fuzz` link closure.
import Plausible.Gen

/-!
# Plausible Gen as a Basalt Generator

This file establishes that Plausible's `Gen` monad is an instance of Basalt's `Gen` typeclass.
This allows generators written polymorphically over Basalt's `Gen` class to be instantiated at
Plausible's `Gen` for executable property-based testing.

## Main Definitions

- `Gen Plausible.Gen` — The `Gen` instance for Plausible's `Gen` monad.
-/

open Lean.Order

namespace Basalt.PlausibleGen

/-! ### PartialOrder and CCPO for `Except GenError`

We use a flat order with `Except.error default` as bottom. -/

instance instPartialOrderExceptGenError : PartialOrder (Except Plausible.GenError α) :=
  FlatOrder.instOrder (b := Except.error default)

instance instCCPOExceptGenError : CCPO (Except Plausible.GenError α) :=
  FlatOrder.instCCPO (b := Except.error default)

/-! ### MonoBind for `Except GenError` -/

instance : MonoBind (Except Plausible.GenError) where
  bind_mono_left h := by
    cases h with
    | bot => exact FlatOrder.rel.bot
    | refl => exact FlatOrder.rel.refl
  bind_mono_right h := by
    cases ‹Except Plausible.GenError _› with
    | error => exact FlatOrder.rel.refl
    | ok a => exact h a

/-! ### RandomChoice for Plausible.Gen -/

instance : RandomChoice Plausible.Gen where
  choose lo hi h := do
    let v ← Plausible.Gen.choose Nat lo hi h
    pure (ULift.up v)

/-- Plausible's `Gen` is an instance of Basalt's `Gen` typeclass. -/
instance : Gen Plausible.Gen where
  instInhabited := inferInstance
  instMonad := inferInstance
  instRandomChoice := inferInstance
  instCCPO := inferInstance
  instMonoBind := inferInstance

end Basalt.PlausibleGen
