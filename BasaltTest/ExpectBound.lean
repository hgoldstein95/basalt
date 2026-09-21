/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt
import BasaltExamples.ArbNat
import BasaltExamples.BST

open RandomChoice ENNReal ArbNat BST

/-!
# The `expect_bound` and `expect_fixpoint` Contract

Pins the arithmetic goal an expectation walk leaves, at both interpretations, and that the two
expectation bounds of the cookbook are that walk followed by arithmetic.
-/

namespace ExpectBoundTest

-- The bound is computed from the postexpectation: a draw's is its continuation's bound.
/--
trace: ⊢ (∑ x ∈ Finset.Icc 0 3, [↑(x + 4), ↑(x + 5)].sum / ↑[↑(x + 4), ↑(x + 5)].length) / ↑(3 - 0 + 1) ≤ ∞
-/
#guard_msgs in
example : SPMF.expect (do let x ← chooseNat 0 3; let y ← elements [4, 5]; pure (x + y) : SPMF Nat)
    (fun n => (n : ℝ≥0∞)) ≤ ⊤ := by
  expect_bound
  trace_state
  exact le_top

-- A list combinator's bound is built from its branches' bounds, not from the branches.
/--
trace: b : Bool
⊢ [↑(Int.toNat 0), if b = true then (∑ x ∈ Finset.Icc 1 3, ↑x.toNat) / ↑(3 - 1 + 1).toNat else ↑(Int.toNat 2)].sum /
      ↑[↑(Int.toNat 0),
            if b = true then (∑ x ∈ Finset.Icc 1 3, ↑x.toNat) / ↑(3 - 1 + 1).toNat else ↑(Int.toNat 2)].length ≤
    ∞
-/
#guard_msgs in
example (b : Bool) : SPMF.expect
    (oneOf [fun () => pure 0, fun () => if b then chooseInt 1 3 else pure 2] : SPMF Int)
    (fun z => (z.toNat : ℝ≥0∞)) ≤ ⊤ := by
  expect_bound
  trace_state
  exact le_top

-- At the cost interpretation the same rules see the choices made so far: `WPC` counts them.
/--
trace: ⊢ (List.map (fun p => ↑p.1 * p.2)
          [(1, ↑(1 + 0)),
            (2,
              1 / 2 * ↑(1 + (1 + 0)) +
                1 / 2 * ([↑(1 + (1 + 1)), ↑(1 + (1 + 1))].sum / ↑[↑(1 + (1 + 1)), ↑(1 + (1 + 1))].length))]).sum /
      ↑(List.map Prod.fst
            [(1, ↑(1 + 0)),
              (2,
                1 / 2 * ↑(1 + (1 + 0)) +
                  1 / 2 * ([↑(1 + (1 + 1)), ↑(1 + (1 + 1))].sum / ↑[↑(1 + (1 + 1)), ↑(1 + (1 + 1))].length))]).sum ≤
    ∞
-/
#guard_msgs in
example : SPMF.Cost.expectedCost
    (frequency [(1, fun () => pure 0), (2, fun () => pick (fun () => pure 1) (fun () => elements [4, 5]))]
      : SPMF.Cost Nat) ≤ ⊤ := by
  expect_bound
  trace_state
  exact le_top

/-- `Nat.arbitrary.expected_cost`, by the walk: the recurrence `E = ½·1 + ½·(1 + E)`. -/
example : SPMF.Cost.expectedCost (Nat.arbitrary : SPMF.Cost Nat) ≤ 2 := by
  expect_fixpoint
  ennreal_to_real
  norm_num

-- The recursive call's fact is `ih`, used under the walk's postexpectation up to a constant.
/--
trace: arbitrary : SPMF.Cost ℕ
ih : (SPMF.expect arbitrary fun p => ↑p.2) ≤ 2
⊢ 1 / 2 * ↑(1 + 0) + 1 / 2 * (1 + 2) ≤ 2
-/
#guard_msgs in
example : SPMF.Cost.expectedCost (Nat.arbitrary : SPMF.Cost Nat) ≤ 2 := by
  expect_fixpoint
  trace_state
  ennreal_to_real
  norm_num

/-- `Tree.genBST.expect_size_le`, by the walk: what is left is the harmonic-sum arithmetic. -/
example {lo hi : Int} : SPMF.expect (Tree.genBST lo hi) (fun t => (t.size : ℝ≥0∞))
    ≤ harmonic (hi + 1 - lo).toNat / 2 := by
  expect_fixpoint
  split
  · simp [Tree.size]
  · rename_i hgt
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.cast_one, one_mul,
      add_zero, Tree.size, Nat.cast_zero, zero_add]
    rw [show ((1 + 1 : ℕ) : ℝ≥0∞) = 2 by norm_num,
      show (hi - lo + 1).toNat = (hi + 1 - lo).toNat from by omega]
    gcongr
    set n := (hi + 1 - lo).toNat with hn
    have hn0 : (n : ℝ≥0∞) ≠ 0 := by
      simp only [ne_eq, Nat.cast_eq_zero]
      omega
    have hsummand : ∀ x ∈ Finset.Icc lo hi,
        (1 + harmonic (hi + 1 - (x + 1)).toNat / 2 + harmonic (x - 1 + 1 - lo).toNat / 2 : ℝ≥0∞)
          = 1 + harmonic (x - lo).toNat / 2 + harmonic (hi - x).toNat / 2 := by
      intro x _
      rw [show hi + 1 - (x + 1) = hi - x by ring, show x - 1 + 1 - lo = x - lo by ring]
      ring
    rw [Finset.sum_congr rfl hsummand]
    calc (∑ x ∈ Finset.Icc lo hi,
            (1 + harmonic (x - lo).toNat / 2 + harmonic (hi - x).toNat / 2)) / (n : ℝ≥0∞)
        = ((∑ k ∈ Finset.range n, harmonic k) + (n : ℝ≥0∞)) / (n : ℝ≥0∞) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Int.card_Icc]
          simp only [div_eq_mul_inv, ← Finset.sum_mul]
          simp only [← div_eq_mul_inv]
          rw [sum_Icc_harmonic_left, sum_Icc_harmonic_right, ← hn, nsmul_eq_mul, mul_one,
            add_assoc, ENNReal.add_halves,
            add_comm ((n : ℝ≥0∞)) (∑ k ∈ Finset.range n, harmonic k)]
      _ = ((n : ℝ≥0∞) * harmonic n) / (n : ℝ≥0∞) := by rw [sum_harmonic]
      _ ≤ harmonic n := by
          rw [mul_comm, ENNReal.mul_div_cancel_right hn0 (by finiteness)]

end ExpectBoundTest
