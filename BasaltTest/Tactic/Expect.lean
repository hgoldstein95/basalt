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

Pins the arithmetic goal an expectation walk leaves, at both interpretations.
-/

namespace ExpectBoundTest

-- The bound is computed from the postexpectation: a draw's is its continuation's bound.
/--
trace: ⊢ (∑ x ∈ Finset.Icc 0 3, (List.map (fun y => ↑(x + y)) [4, 5]).sum / ↑[4, 5].length) / ↑(3 - 0 + 1) ≤ ∞
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
trace: ⊢ (List.map (fun p => ↑p.1 * p.2) [(1, ↑(1 + 0)), (2, 1 / 2 * ↑(1 + (1 + 0)) + 1 / 2 * ↑(1 + (1 + 1)))]).sum /
      ↑(List.map Prod.fst [(1, ↑(1 + 0)), (2, 1 / 2 * ↑(1 + (1 + 0)) + 1 / 2 * ↑(1 + (1 + 1)))]).sum ≤
    ∞
-/
#guard_msgs in
example : SPMF.Cost.expectedCost
    (frequency [(1, fun () => pure 0), (2, fun () => pick (fun () => pure 1) (fun () => elements [4, 5]))]
      : SPMF.Cost Nat) ≤ ⊤ := by
  expect_bound
  trace_state
  exact le_top

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

-- A list combinator has no shape of choice, so it is bounded by a rule. At the cost interpretation
-- `vectorOf` reads its element generator's expected cost, which the walk supplies from the fact.
/--
trace: ⊢ 0 + ↑5 * 2 ≤ 10
-/
#guard_msgs in
example : SPMF.Cost.expectedCost (vectorOf 5 Nat.arbitrary : SPMF.Cost (List Nat)) ≤ 10 := by
  expect_bound [Nat.arbitrary.expected_cost]
  trace_state
  ennreal_to_real
  norm_num

-- Elsewhere only the mass is used: a constant postexpectation exactly, and otherwise its worst case
-- over every value, dually to the `⨅` that `mass_bound` leaves.
/--
trace: ⊢ ⨆ a, ↑a.length ≤ ∞
-/
#guard_msgs in
example : SPMF.expect (vectorOf 2 Nat.arbitrary) (fun l => (l.length : ℝ≥0∞)) ≤ ⊤ := by
  expect_bound
  trace_state
  exact le_top

/--
trace: ⊢ 7 ≤ 7
-/
#guard_msgs in
example : SPMF.expect (listOf Nat.arbitrary >>= fun _ => Pure.pure 0)
    (fun _ => (7 : ℝ≥0∞)) ≤ 7 := by
  expect_bound
  trace_state
  exact le_rfl

-- The cookbook's expectation bounds are this walk followed by arithmetic:
-- `Nat.arbitrary.expected_cost` (`ArbNat.lean`) and `Tree.genBST.expect_size_le` (`BST.lean`).

end ExpectBoundTest
