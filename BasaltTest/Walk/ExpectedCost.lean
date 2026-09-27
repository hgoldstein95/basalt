/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt
import BasaltExamples.AllTwoTree

/-!
# The Expected-Cost Walk Contract

Pins the arithmetic goal `walk` leaves on an upper bound `SPMF.Cost.expectObs.spec g f ≤ B`.
-/

open RandomChoice ENNReal AllTwoTree

namespace ExpectedCostTest

-- Each draw adds its choice to the cost the walk arrives with.
/--
trace: ⊢ ↑(1 + 1) ≤ 2
-/
#guard_msgs in
example : IsExpectedCostBounded
    (do let x ← chooseNat 0 3; let y ← elements [4, 5]; pure (x + y) : SPMF.Cost Nat) 2 := by
  rw [IsExpectedCostBounded.iff_obs]
  walk
  trace_state
  norm_num

-- The recursive call's fact is `ih`, used under the walk's postexpectation up to the choices made
-- before it.
/--
trace: genWeightedTree : SPMF.Cost AllTwoTree.Tree
ih : (SPMF.Cost.expectObs.spec genWeightedTree fun x n => ↑n) ≤ 3
⊢ (List.map (fun p => ↑p.1 * p.2) [(2, ↑(1 + 0)), (1, 1 + 3 + 3)]).sum /
      ↑(List.map Prod.fst [(2, ↑(1 + 0)), (1, 1 + 3 + 3)]).sum ≤
    3
-/
#guard_msgs in
example : IsExpectedCostBounded (genWeightedTree : SPMF.Cost Tree) 3 := by
  rw [IsExpectedCostBounded.iff_obs]
  walk fixpoint
  trace_state
  norm_num
  exact ENNReal.div_le_of_le_mul (by norm_num)

-- A list combinator has no shape of choice, so it is bounded using only its mass: at its worst
-- case over every value and cost, which for the cost itself is `⊤`.
/--
trace: ⊢ ⨆ a, ⨆ n, ↑n ≤ ∞
-/
#guard_msgs in
example : IsExpectedCostBounded (listOf (chooseNat 0 1) : SPMF.Cost (List Nat)) ⊤ := by
  rw [IsExpectedCostBounded.iff_obs]
  walk
  trace_state
  exact le_top

/--
error: no rule, `@[gen_map]` lemma, hypothesis, or fact bounds
  g
Pass a fact about it to `walk [_]`.
-/
#guard_msgs in
example (g : SPMF.Cost Nat) : IsExpectedCostBounded (g >>= fun n => Pure.pure n) ⊤ := by
  rw [IsExpectedCostBounded.iff_obs]
  walk

-- `suchThat` is bounded by its generator's expected cost `C` over its chance of acceptance,
-- `1 - r`: here `1` and the average of the rejection indicator.
/--
trace: ⊢ 0 + ↑1 / (1 - (List.map (fun a => if (a != 0) = true then 0 else 1) [0, 1]).sum / ↑[0, 1].length) ≤ ∞
-/
#guard_msgs in
example : IsExpectedCostBounded (suchThat (elements [0, 1]) (· != 0) : SPMF.Cost Nat) ⊤ := by
  rw [IsExpectedCostBounded.iff_obs]
  walk
  trace_state
  exact le_top

-- A lower bound is had by unfolding once, with the generator's own expected cost as the fact about
-- its recursive calls, stated by `le_expect_add` for use under `k + h`.
/--
trace: hm : 1 ≤ SPMF.Cost.expectObs.spec genTree fun x x_1 => 1
⊢ (1 + SPMF.Cost.expectObs.spec genTree fun x n => ↑n) ≤
    [↑(1 + 0),
          (1 + SPMF.Cost.expectObs.spec genTree fun x n => ↑n) + SPMF.Cost.expectObs.spec genTree fun x n => ↑n].sum /
      ↑[↑(1 + 0),
            (1 + SPMF.Cost.expectObs.spec genTree fun x n => ↑n) +
              SPMF.Cost.expectObs.spec genTree fun x n => ↑n].length
-/
#guard_msgs in
example (hm : 1 ≤ SPMF.Cost.expectObs.spec (genTree : SPMF.Cost Tree) fun _ _ => 1) :
    1 + SPMF.Cost.expectObs.spec (genTree : SPMF.Cost Tree) (fun _ n => (n : ℝ≥0∞))
      ≤ SPMF.Cost.expectObs.spec (genTree : SPMF.Cost Tree) (fun _ n => (n : ℝ≥0∞)) := by
  conv_rhs => rw [genTree]
  walk [SPMF.Cost.le_expect_add (x := genTree) (h := fun _ n => (n : ℝ≥0∞)) hm le_rfl]
  trace_state
  generalize SPMF.Cost.expectObs.spec (genTree : SPMF.Cost Tree) (fun _ n => (n : ℝ≥0∞)) = E
  norm_num
  rw [ENNReal.le_div_iff_mul_le (by norm_num) (by norm_num)]
  exact le_of_eq (by ring)

-- The cookbook's expected-cost bounds are this walk followed by arithmetic, with the source's bound
-- passed as a fact: `Tree.genBSTByFiltering.cost` (`BST/ByFiltering.lean`); its lower bound is
-- `AllTwoTree.genTree.not_expected_cost_bounded` (`AllTwoTree.lean`).

end ExpectedCostTest
