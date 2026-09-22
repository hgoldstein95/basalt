/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt

/-!
# Arbitrary Natural Numbers

`Nat.arbitrary` generates an arbitrary natural number by repeatedly flipping a coin to decide
whether to increment. It is the simplest recursive generator in the cookbook and a building block
for several others (`ArbList`, `SortedList`, `Heap`).
-/

open RandomChoice

namespace ArbNat

/-- Generates an arbitrary natural number: flip a coin to stop at `0` or recurse and add one. -/
def Nat.arbitrary [Gen G] : G Nat := do
  pick
    (fun () => pure 0)
    (fun () => do
      let n ← Nat.arbitrary
      pure (n + 1))
partial_fixpoint

theorem Nat.arbitrary.sound_complete : IsSoundAndComplete Nat.arbitrary ⊤ := by
  refine .intro (fun _ _ => trivial) ?complete
  intro n
  induction n with
  | zero => intro _; rw [Nat.arbitrary]; complete_bound
  | succ n ih =>
    intro _
    rw [Nat.arbitrary]; complete_bound
    exact ⟨n, ih trivial, rfl⟩

theorem Nat.arbitrary.terminates : IsAlmostSurelyTerminating Nat.arbitrary := by
  mass_fixpoint using SPMF.LfpIsOne.affine (m := 1 / 2) (by norm_num)
  simp

/-- Producing `n` costs `n + 1` random choices (one per increment, plus the final stop). -/
theorem Nat.arbitrary.cost_bounded :
    IsCostBounded Nat.arbitrary (fun n => n + 1) := by
  cost_fixpoint
  all_goals omega

section expected_cost
open scoped ENNReal

/-- The cost recurrence `E = ½·1 + ½·(1 + E)` solves to 2, which the walk leaves as arithmetic. -/
theorem Nat.arbitrary.expected_cost :
    SPMF.Cost.expectedCost (Nat.arbitrary : SPMF.Cost Nat) ≤ 2 := by
  expect_fixpoint
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
