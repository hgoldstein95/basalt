/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt
import BasaltExamples.ArbNat
import BasaltExamples.BST

/-!
# The Expectation Walk Contract

Pins the arithmetic goal `walk` leaves on an upper bound `SPMF.expectObs.spec g f ≤ B`.
-/

open RandomChoice ENNReal ArbNat BST

namespace ExpectBoundTest

-- The bound is computed from the postexpectation: a draw's is its continuation's bound.
/--
trace: ⊢ (∑ x ∈ Finset.Icc 0 3, (List.map (fun y => ↑(x + y)) [4, 5]).sum / ↑[4, 5].length) / ↑(3 - 0 + 1) ≤ ∞
-/
#guard_msgs in
example : SPMF.expect (do let x ← chooseNat 0 3; let y ← elements [4, 5]; pure (x + y) : SPMF Nat)
    (fun n => (n : ℝ≥0∞)) ≤ ⊤ := by
  rw [SPMF.expect_eq_obs]
  walk
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
  rw [SPMF.expect_eq_obs]
  walk
  trace_state
  exact le_top

-- The recursive call's fact is `ih`, used under the walk's postexpectation up to a constant.
/--
trace: arbitrary : SPMF ℕ
ih : (SPMF.expectObs.spec arbitrary fun n => ↑n) ≤ 1
⊢ [↑0, 1 + 1].sum / ↑[↑0, 1 + 1].length ≤ 1
-/
#guard_msgs in
example : SPMF.expect (Nat.arbitrary : SPMF Nat) (fun n => (n : ℝ≥0∞)) ≤ 1 := by
  rw [SPMF.expect_eq_obs]
  walk fixpoint
  trace_state
  norm_num

-- A list combinator has no shape of choice, so it is bounded by a rule that uses only the mass:
-- a constant postexpectation exactly, and otherwise its worst case over every value, dually to the
-- `⨅` a lower bound on the mass leaves. a constant postexpectation exactly, and otherwise its worst case
-- over every value, dually to the `⨅` a lower bound on the mass leaves.
/--
trace: ⊢ ⨆ a, ↑a.length ≤ ∞
-/
#guard_msgs in
example : SPMF.expect (vectorOf 2 Nat.arbitrary) (fun l => (l.length : ℝ≥0∞)) ≤ ⊤ := by
  rw [SPMF.expect_eq_obs]
  walk
  trace_state
  exact le_top

/--
trace: ⊢ 7 ≤ 7
-/
#guard_msgs in
example : SPMF.expect (listOf Nat.arbitrary >>= fun _ => Pure.pure 0)
    (fun _ => (7 : ℝ≥0∞)) ≤ 7 := by
  rw [SPMF.expect_eq_obs]
  walk
  trace_state
  exact le_rfl

-- A generator nothing is known about is an error, not a bound by its mass alone: that bound is a
-- list combinator's rule, and a callee whose law was not passed is no list combinator.
/--
error: no rule, `@[gen_map]` lemma, hypothesis, or fact bounds
  g
Pass a fact about it to `walk [_]`.
-/
#guard_msgs in
example (g : SPMF Nat) : SPMF.expect (g >>= fun n => Pure.pure n) (fun n => (n : ℝ≥0∞)) ≤ ⊤ := by
  rw [SPMF.expect_eq_obs]
  walk

-- The cookbook's expectation bound is this walk followed by arithmetic: `Tree.genBST.expect_size_le`
-- (`BST.lean`).

end ExpectBoundTest
