/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt

/-!
# Non-Empty Lists by Filtering

`genNonEmpty` draws a list sized by `n` and retries until the list is not empty. Its source rejects
only a `1 / (n + 1)` share of its draws, so the retries add a constant to its expected cost
(`genNonEmpty.cost`); compare `BST/ByFiltering.lean`, whose source is only known to accept its
leaves.
-/

open RandomChoice
open scoped ENNReal

namespace NonEmptyList

/-- A list sized by `n`, with elements in `[0, n]`: stopping with weight `1` against continuing with
weight `n`. -/
def genList [Gen G] (n : Nat) : G (List Nat) :=
  frequency! [
    (1, fun _ => pure []),
    (n, fun _ => do
      let x ← chooseNat 0 n
      let xs ← genList n
      return x :: xs)
  ] (by simp)
partial_fixpoint

/-- Draws from `genList` until the list drawn is not empty. -/
def genNonEmpty [Gen G] (n : Nat) : G (List Nat) :=
  suchThat (genList n) (!·.isEmpty)

/-! ## Support -/

theorem genList.sound (n : Nat) : IsSoundFor (genList n : SPMF (List Nat)) (∀ x ∈ ·, x ≤ n) := by
  rw [IsSoundFor.iff_obs]
  walk fixpoint
  · next y hy => simp at hy
  · next x hx xs hxs y hy =>
    rcases List.mem_cons.mp hy with rfl | hy
    · exact hx.2
    · exact hxs y hy

theorem genList.complete {n : Nat} (hn : 0 < n) :
    IsCompleteFor (genList n : SPMF (List Nat)) (∀ x ∈ ·, x ≤ n) := by
  intro xs
  induction xs with
  | nil => intro _; rw [genList, SPMF.mem_support_iff_may]; walk
  | cons x xs ih =>
    intro h
    rw [genList, SPMF.mem_support_iff_may]
    walk
    exact ⟨hn, x, ⟨Nat.zero_le _, h x (by simp)⟩, xs, ih fun y hy => h y (by simp [hy]), rfl⟩

theorem genNonEmpty.sound_complete {n : Nat} (hn : 0 < n) :
    IsSoundAndComplete (genNonEmpty n) fun xs => xs ≠ [] ∧ ∀ x ∈ xs, x ≤ n := by
  refine .intro ?sound ?complete
  case sound =>
    rw [IsSoundFor.iff_obs]
    walk [(genList.sound n).obs]
    · next xs hxs => simpa [List.isEmpty_iff] using hxs.2
    · next xs hxs x hx => exact hxs.1 x hx
  case complete =>
    intro xs hxs
    rw [SPMF.mem_support_iff_may]
    walk [(genList.complete hn).obs]
    exact ⟨hxs.2, by simpa [List.isEmpty_iff] using hxs.1⟩

/-! ## Termination -/

private theorem one_sub_div_succ (n : Nat) : 1 - (n : ℝ≥0∞) / (n + 1) = 1 / (n + 1) :=
  ENNReal.sub_eq_of_eq_add (by finiteness) (by
    rw [ENNReal.div_add_div_same, add_comm (1 : ℝ≥0∞), ENNReal.div_self (by simp) (by simp)])

theorem genList.terminates (n : Nat) : IsAlmostSurelyTerminating (genList n : SPMF (List Nat)) := by
  mass_fixpoint using SPMF.LfpIsOne.affine (m := n / (n + 1))
    (ENNReal.div_lt_of_lt_mul (by rw [one_mul]; exact_mod_cast n.lt_succ_self))
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.cast_one, one_mul,
    add_zero, Nat.cast_add, one_sub_div_succ]
  rw [ENNReal.add_div, ENNReal.mul_div_right_comm, add_comm (1 : ℝ≥0∞) n]

/-- A list is empty only when the first choice stops it. -/
theorem genList.reject_le (n : Nat) :
    SPMF.expectObs.spec (genList n : SPMF (List Nat))
      (fun xs => if (!xs.isEmpty) = true then 0 else 1) ≤ 1 / (n + 1) := by
  have hle : ∀ (p : List Nat → ℝ≥0∞),
      SPMF.expectObs.spec (genList n : SPMF (List Nat)) p ≤ ⨆ a, p a :=
    fun _ => SPMF.expect_le_iSup
  rw [genList]
  walk [hle]
  simp [add_comm]

theorem genNonEmpty.terminates {n : Nat} (hn : 0 < n) :
    IsAlmostSurelyTerminating (genNonEmpty n : SPMF (List Nat)) := by
  rw [IsAlmostSurelyTerminating.iff_obs]
  walk [(genList.terminates n).obs, genList.reject_le n]
  rw [ite_eq_left ⟨le_rfl, ENNReal.div_lt_of_lt_mul (by
    rw [one_mul]; exact_mod_cast (show 1 < n + 1 by omega))⟩, one_mul]

/-! ## Cost -/

theorem genList.cost (n : Nat) :
    IsExpectedCostBounded (genList n : SPMF.Cost (List Nat)) (2 * n + 1) := by
  rw [IsExpectedCostBounded.iff_obs]
  walk fixpoint
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  refine ENNReal.div_le_of_le_mul ?_
  exact_mod_cast (show 1 * (1 + 0) + n * (1 + 1 + (2 * n + 1)) ≤ (2 * n + 1) * (1 + (n + 0))
    from le_of_eq (by ring))

@[inherit_doc genList.reject_le]
theorem genList.reject_le_cost (n : Nat) :
    SPMF.Cost.expectObs.spec (genList n : SPMF.Cost (List Nat))
      (fun xs _ => if (!xs.isEmpty) = true then 0 else 1) ≤ 1 / (n + 1) := by
  have hle : ∀ (p : List Nat → ℕ → ℝ≥0∞),
      SPMF.Cost.expectObs.spec (genList n : SPMF.Cost (List Nat)) p ≤ ⨆ a, ⨆ k, p a k :=
    fun _ => SPMF.Cost.expect_le_iSup
  rw [genList]
  walk [hle]
  simp [add_comm]

/-- At most three choices more than its source's expected cost, whatever `n`. -/
theorem genNonEmpty.cost {n : Nat} (hn : 0 < n) :
    IsExpectedCostBounded (genNonEmpty n : SPMF.Cost (List Nat)) (2 * n + 4) := by
  rw [IsExpectedCostBounded.iff_obs]
  walk [(genList.cost n).obs, genList.reject_le_cost n]
  rw [zero_add]
  refine SPMF.Cost.div_one_sub_le (by finiteness) ?_
  have h3 : 1 / ((n : ℝ≥0∞) + 1) * (2 * n + 4) ≤ 3 := by
    rw [one_div, ← ENNReal.div_eq_inv_mul]
    exact ENNReal.div_le_of_le_mul (by exact_mod_cast (show 2 * n + 4 ≤ 3 * (n + 1) by omega))
  calc _ ≤ 2 * (n : ℝ≥0∞) + 1 + 3 := by gcongr
    _ = 2 * n + 4 := by ring

end NonEmptyList
