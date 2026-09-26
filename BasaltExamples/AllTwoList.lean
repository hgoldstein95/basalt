/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt

/-!
# Lists of All Twos

The minimal recursive generator: `genAllTwos` produces lists whose every element is `2`. Because the
element is fixed, this isolates the list-shape recursion (a subcritical branching process) from any
element generation, making it the simplest place to see the support / termination / cost recipe.
-/

open RandomChoice

namespace AllTwoList

/-- The validity predicate: every element of the list is `2`. -/
def AllTwos (l : List Nat) : Prop := ∀ x ∈ l, x = 2

/-- The cost bound: one random choice per element, plus the final choice that ends the list. -/
def AllTwos.cost (l : List Nat) : Nat := l.length + 1

/-- Generates a list of all `2`s: flip a coin to stop with `[]`, or prepend a `2` and recurse. -/
def genAllTwos [Gen G] : G (List Nat) :=
  oneOf! [
    fun _ => pure [],
    fun _ => do
      let xs ← genAllTwos
      return 2 :: xs]
partial_fixpoint

theorem genAllTwos.sound_complete : IsSoundAndComplete genAllTwos AllTwos := by
  refine .intro ?sound ?complete
  case sound =>
    sound_fixpoint
    · simp [AllTwos]
    · next xs h_xs => simpa [AllTwos] using h_xs
  case complete =>
    intro xs
    induction xs with
    | nil => intro _; rw [genAllTwos]; complete_bound
    | cons x xs ih =>
      intro h
      obtain rfl : x = 2 := h x (by simp)
      rw [genAllTwos]; complete_bound
      exact ⟨xs, ih fun y hy => h y (by simp [hy]), rfl⟩

theorem genAllTwos.terminates : IsAlmostSurelyTerminating genAllTwos := by
  mass_fixpoint using SPMF.LfpIsOne.affine (m := 1 / 2) (by norm_num)
  simp [ENNReal.div_eq_inv_mul, mul_add]

theorem genAllTwos.cost_bounded : IsCostBounded genAllTwos AllTwos.cost := by
  cost_fixpoint
  all_goals simp only [AllTwos.cost, List.length_nil, List.length_cons] at *; omega

theorem genAllTwos.faithful : IsFaithful genAllTwos := by
  faithful_fixpoint [genAllTwos.terminates]

end AllTwoList
