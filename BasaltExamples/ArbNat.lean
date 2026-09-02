/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt

open RandomChoice

/-!
# Arbitrary Natural Numbers

`Nat.arbitrary` generates an arbitrary natural number by repeatedly flipping a coin to decide
whether to increment. It is the simplest recursive generator in the cookbook and a building block
for several others (`ArbList`, `SortedList`, `Heap`).
-/

namespace ArbNat

/-- Generates an arbitrary natural number: flip a coin to stop at `0` or recurse and add one. -/
def Nat.arbitrary [Gen G] : G Nat := do
  pick
    (fun () => pure 0)
    (fun () => do
      let n ← Nat.arbitrary
      pure (n + 1))
partial_fixpoint

theorem Nat.arbitrary_mem_support : n ∈ SPMF.support Nat.arbitrary := by
  induction n <;> rw [Nat.arbitrary] <;> simp [*]

theorem Nat.arbitrary.sound_complete : IsSoundAndComplete Nat.arbitrary ⊤ :=
  fun _ => iff_of_true Nat.arbitrary_mem_support trivial

theorem Nat.arbitrary.terminates : IsAlmostSurelyTerminating Nat.arbitrary := by
  -- Static seed, mean offspring 1/2: subcritical.
  refine SPMF.IsPMF_of_subcritical_mass (m := 1 / 2) (by norm_num) ?_
  conv_rhs => rw [Nat.arbitrary]
  simp

/-- Producing `n` costs `n + 1` random choices (one per increment, plus the final stop). -/
theorem Nat.arbitrary.cost_bounded :
    IsCostBounded Nat.arbitrary (fun n => n + 1) := by
  open Lean.Order in
  delta arbitrary
  apply fix_induct (motive := fun (g : SPMF.Cost Nat) => IsBounded g (fun n => n + 1)) _ ?admissible ?step
  case admissible =>
    apply admissible_IsBounded
  case step =>
    intro arbitrary_rec ih
    rw [IsBounded_iff]
    rintro ⟨n, c⟩ hmem
    cost_support_simp at hmem
    obtain ⟨m, rfl, h | h⟩ := hmem
    · obtain ⟨rfl, rfl⟩ := h
      omega
    · obtain ⟨a, n1, n2, ha, ⟨hn, hn2⟩, hm⟩ := h
      have h1 : n1 ≤ a + 1 := ih (a, n1) ha
      show 1 + m ≤ n + 1
      omega

section expected_cost
open scoped ENNReal

/-- The cost recurrence `E = ½·1 + ½·(1 + E)` solves to 2; `fix_induct` gives the upper bound. -/
theorem Nat.arbitrary.expected_cost :
    SPMF.Cost.expectedCost (Nat.arbitrary : SPMF.Cost Nat) ≤ 2 := by
  open Lean.Order in
  delta arbitrary
  apply fix_induct (motive := fun (g : SPMF.Cost Nat) =>
    SPMF.expect g (fun p => (p.2 : ℝ≥0∞)) ≤ 2) _ ?admissible ?step
  case admissible => exact SPMF.admissible_expect_le _ _
  case step =>
    intro arbitrary_rec ih
    rw [SPMF.Cost.expect_pick, SPMF.Cost.expect_pure, SPMF.Cost.expect_bind]
    simp only [SPMF.Cost.expect_pure]
    push_cast
    simp only [add_zero]
    have hrec : SPMF.expect arbitrary_rec (fun p => (1 : ℝ≥0∞) + (p.2 : ℝ≥0∞)) ≤ 3 := by
      calc SPMF.expect arbitrary_rec (fun p => (1 : ℝ≥0∞) + (p.2 : ℝ≥0∞))
          = SPMF.expect arbitrary_rec (fun _ => 1)
              + SPMF.expect arbitrary_rec (fun p => (p.2 : ℝ≥0∞)) := SPMF.expect_add _ _ _
        _ ≤ 1 + 2 := add_le_add (by rw [SPMF.expect_one]; exact SPMF.mass_le_one _) ih
        _ = 3 := by norm_num
    calc (1/2 : ℝ≥0∞) * 1
          + 1/2 * SPMF.expect arbitrary_rec (fun p => (1 : ℝ≥0∞) + (p.2 : ℝ≥0∞))
        ≤ 1/2 * 1 + 1/2 * 3 := add_le_add le_rfl (mul_le_mul_right hrec _)
      _ = 2 := by
          ennreal_to_real
          norm_num

/-- Markov: generation costs at least `k` choices with probability at most `2 / k`. -/
theorem Nat.arbitrary.cost_tail {k : Nat} (hk : k ≠ 0) :
    SPMF.prob (Nat.arbitrary : SPMF.Cost Nat) {p | k ≤ p.2} ≤ 2 / (k : ℝ≥0∞) := by
  have hset : {p : Nat × Nat | k ≤ p.2} = {p : Nat × Nat | (k : ℝ≥0∞) ≤ (p.2 : ℝ≥0∞)} := by
    ext p
    simp
  rw [hset]
  calc SPMF.prob (Nat.arbitrary : SPMF.Cost Nat) {p | (k : ℝ≥0∞) ≤ (p.2 : ℝ≥0∞)}
      ≤ SPMF.expect (Nat.arbitrary : SPMF.Cost Nat) (fun p => (p.2 : ℝ≥0∞)) / k :=
        SPMF.prob_le_expect_div _ _ (by exact_mod_cast hk) (ENNReal.natCast_ne_top k)
    _ ≤ 2 / k := by
        gcongr
        exact Nat.arbitrary.expected_cost

end expected_cost

end ArbNat
