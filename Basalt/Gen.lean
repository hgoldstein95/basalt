/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt.RandomChoice

open Lean.Order

/-!
# Generator Typeclass

This file defines `Gen`, a typeclass that collects a variety of other typeclass definitions. In
short, a generator must be a monad, it must have a random choice operator, and it must be able to
represent potentially non-terminating computations (via `partial_fixpoint`).

## Main Definitions

- `Gen` — A class that collects all of the requirements necessary for a generator monad.
-/

/-- A type constructor `g` is a `Gen` if it has all of the operations necessary for (potentially
diverging) random monadic programming. -/
class Gen (g : Type u → Type v) where
  instInhabited : ∀ α, Inhabited (g α)
  instMonad : Monad g
  instRandomChoice : RandomChoice g
  instCCPO : ∀ α, CCPO (g α)
  instMonoBind : MonoBind g

instance [m : Gen g] : ∀ α, Inhabited (g α) := m.instInhabited
instance [m : Gen g] : Monad g := m.instMonad
instance [m : Gen g] : RandomChoice g := m.instRandomChoice
instance [m : Gen g] : ∀ α, CCPO (g α) := m.instCCPO
instance [m : Gen g] : MonoBind g := m.instMonoBind

instance
    [∀ α, Inhabited (g α)]
    [Monad g]
    [RandomChoice g]
    [∀ α, CCPO (g α)]
    [MonoBind g] : Gen g where
  instInhabited := inferInstance
  instMonad := inferInstance
  instRandomChoice := inferInstance
  instCCPO := inferInstance
  instMonoBind := inferInstance
