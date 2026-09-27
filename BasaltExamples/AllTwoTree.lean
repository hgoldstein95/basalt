/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt

/-!
# Trees of All Twos

Binary trees whose every node holds `2`. This example exists to contrast two termination regimes on
the *same* shape:

- `genTree` recurses on both children with a uniform `oneOf`, giving mean offspring exactly `1` — it
  is **critical**. It still terminates almost surely, but no finite bound holds of its expected
  cost (`genTree.not_expected_cost_bounded`), which is one choice per constructor.
- `genWeightedTree` uses `frequency` to make the leaf branch twice as likely (mean offspring `2/3`),
  making it **subcritical**, with expected cost at most `3` (`genWeightedTree.cost`).
-/

open RandomChoice

namespace AllTwoTree

/-- A binary tree with `Nat`-labelled nodes. -/
inductive Tree : Type where
  | leaf : Tree
  | node : Tree → Nat → Tree → Tree

/-- The number of nodes in the tree. -/
def Tree.size : Tree → Nat
  | .leaf => 0
  | .node l _ r => l.size + r.size + 1

/-- The validity predicate: every node holds `2`. -/
def Tree.isAllTwos : Tree → Prop
  | .leaf => True
  | .node l v r => v = 2 ∧ Tree.isAllTwos l ∧ Tree.isAllTwos r

/-- The cost bound: three choices per node (one `oneOf` plus two recursive calls), plus one. -/
def Tree.cost : Tree → Nat := fun t => 3 * t.size + 1

/-- Generates an all-`2`s tree with a uniform `oneOf`. Mean offspring `1`: critical, so almost surely
terminating, with no finite bound on its expected cost (`genTree.not_expected_cost_bounded`). -/
def genTree [Gen G] : G Tree :=
  oneOf! [
    fun _ => pure .leaf,
    fun _ => do
      let l ← genTree
      let r ← genTree
      return .node l 2 r]
partial_fixpoint

theorem genTree.sound_complete : IsSoundAndComplete genTree Tree.isAllTwos := by
  refine .intro ?sound ?complete
  case sound =>
    rw [IsSoundFor.iff_obs]
    walk fixpoint
    all_goals simp_all [Tree.isAllTwos]
  case complete =>
    intro t
    induction t with
    | leaf => intro _; rw [genTree, SPMF.mem_support_iff_may]; walk
    | node l v r ihl ihr =>
      intro ⟨hv, hl, hr⟩
      subst hv
      rw [genTree, SPMF.mem_support_iff_may]; walk
      exact ⟨l, ihl hl, r, ihr hr, rfl⟩

theorem genTree.terminates : IsAlmostSurelyTerminating genTree := by
  mass_fixpoint using SPMF.LfpIsOne.quadratic (a := 1 / 2) (b := 0) (d := 1 / 2)
    (by ennreal_to_real; norm_num) (by ennreal_to_real; norm_num) (by norm_num)
  simp [sq, ENNReal.div_eq_inv_mul, mul_add]

theorem genTree.cost_bounded : IsCostBounded genTree Tree.cost := by
  rw [IsCostBounded.iff_obs]
  walk fixpoint
  all_goals simp only [Tree.cost, Tree.size] at *; omega

theorem genTree.faithful : IsFaithful genTree := by
  faithful_fixpoint [genTree.terminates]

theorem genTree.cost_faithful : IsCostFaithful genTree := ⟨by walk fixpoint, by walk fixpoint⟩

open scoped ENNReal in
/-- Unfolded once, the expected cost `E` is at least `1 + E`: one choice, then two subtrees half the
time. -/
theorem genTree.not_expected_cost_bounded {B : ℝ≥0∞} (hB : B ≠ ⊤) :
    ¬ IsExpectedCostBounded (genTree : SPMF.Cost Tree) B := by
  have hm := genTree.cost_faithful.one_le_mass genTree.terminates
  refine IsExpectedCostBounded.not_of_step one_ne_zero hB ?_
  conv_rhs => rw [genTree]
  walk [SPMF.Cost.le_expect_add (x := genTree) (h := fun _ n => (n : ℝ≥0∞)) hm le_rfl]
  generalize SPMF.Cost.expectObs.spec (genTree : SPMF.Cost Tree) (fun _ n => (n : ℝ≥0∞)) = E
  norm_num
  rw [ENNReal.le_div_iff_mul_le (by norm_num) (by norm_num)]
  exact le_of_eq (by ring)

section weighted

open scoped NNReal ENNReal

/-- Generates an all-`2`s tree, but weights the leaf branch twice as heavily as the node branch. -/
def genWeightedTree [Gen G] : G Tree :=
  frequency! [
    (2, fun _ => pure .leaf),
    (1, fun _ => do
      let l ← genWeightedTree
      let r ← genWeightedTree
      return .node l 2 r)
  ] (by simp)
partial_fixpoint

theorem genWeightedTree.terminates : IsAlmostSurelyTerminating genWeightedTree := by
  mass_fixpoint using SPMF.LfpIsOne.quadratic (a := 2 / 3) (b := 0) (d := 1 / 3)
    (by ennreal_to_real; norm_num) (by ennreal_to_real; norm_num) (by norm_num)
  simp [sq, ENNReal.div_eq_inv_mul, mul_add]

theorem genWeightedTree.faithful : IsFaithful genWeightedTree := by
  faithful_fixpoint [genWeightedTree.terminates]

/-- One choice per constructor, `1 / (1 - 2/3) = 3` of them on average. -/
theorem genWeightedTree.cost : IsExpectedCostBounded (genWeightedTree : SPMF.Cost Tree) 3 := by
  rw [IsExpectedCostBounded.iff_obs]
  walk fixpoint
  norm_num
  exact ENNReal.div_le_of_le_mul (by norm_num)

end weighted

end AllTwoTree
