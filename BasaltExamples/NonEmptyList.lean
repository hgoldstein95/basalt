/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt

/-!
# Non-Empty Lists by Filtering

`genNonEmpty` draws a list sized by `n` and retries until the list is not empty. Its source rejects
only a `1 / (n + 1)` share of its draws (`genList.reject_le`); compare `BST/ByFiltering.lean`,
whose source is only known to accept its leaves.
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

end NonEmptyList
