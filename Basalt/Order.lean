/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
module

public import Init.Internal.Order.Basic
import all Init.Internal.Order.Basic

/-!
# Admissibility

Core does not expose the body of `Lean.Order.admissible`, so a module cannot unfold it.
`admissible_iff` restates the definition for the proofs that need it.
-/

public section

namespace Lean.Order

theorem admissible_iff {α : Sort u} [CCPO α] {P : α → Prop} :
    admissible P ↔ ∀ (c : α → Prop) (hc : chain c), (∀ x, c x → P x) → P (CCPO.csup hc) :=
  Iff.rfl

end Lean.Order
