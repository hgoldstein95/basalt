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

-- A critical generator's step is `1 + B ≤ B`, which only `⊤` satisfies.
/--
trace: B : ℝ≥0∞
hB : B = ∞
genTree : SPMF.Cost AllTwoTree.Tree
ih : (SPMF.Cost.expectObs.spec genTree fun x n => ↑n) ≤ B
⊢ [↑(1 + 0), 1 + B + B].sum / ↑[↑(1 + 0), 1 + B + B].length ≤ B
-/
#guard_msgs in
example (B : ℝ≥0∞) (hB : B = ⊤) : IsExpectedCostBounded (genTree : SPMF.Cost Tree) B := by
  rw [IsExpectedCostBounded.iff_obs]
  walk fixpoint
  trace_state
  subst hB
  exact le_top

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

-- The cookbook's expected-cost bounds are this walk followed by arithmetic, with the source's bound
-- passed as a fact: `Tree.genBSTByFiltering.cost` (`BST/ByFiltering.lean`).

end ExpectedCostTest
