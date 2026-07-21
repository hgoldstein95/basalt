/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt.Gen
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Data.Real.Basic

open RandomChoice

/-!
# Generating a Type with Structure

A small illustrative example: `genMonoid` shows that a Basalt generator can produce a *type together
with a typeclass instance*, not just first-order data. Its return type is the dependent pair
`Σ α, Monoid α`, and it picks between `ℕ` and `ℝ` (with their standard monoid instances).

Unlike the other examples, this file states no correctness laws — the property vocabulary in
`Basalt/Laws.lean` (support, termination, cost) is aimed at generators of concrete test data, and
there is no established validity predicate for "an arbitrary monoid." It is kept as a demonstration
of what the representation is capable of expressing.
-/

namespace Monoid

/-- Generates a type paired with a `Monoid` instance, choosing uniformly between `ℕ` and `ℝ`. -/
def genMonoid [Gen G] : G (Σ (α : Type), Monoid α) :=
  pick (fun () => pure ⟨ℕ, Nat.instMonoid⟩) (fun () => pure ⟨ℝ, Real.instMonoid⟩)

end Monoid
