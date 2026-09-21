/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt

open RandomChoice

/-!
# Trees of All Twos

Binary trees whose every node holds `2`. This example exists to contrast two termination regimes on
the *same* shape:

- `genTree` recurses on both children with a uniform `pick`, giving mean offspring exactly `1` — it
  is **critical**. It still terminates almost surely, but with *infinite expected size*.
- `genWeightedTree` uses `frequency` to make the leaf branch twice as likely (mean offspring `2/3`),
  making it **subcritical** and giving finite expected size.

The `expectedSteps` theorems at the end make the contrast quantitative: `3` for the weighted
generator versus `⊤` for the critical one.
-/

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

/-- The cost bound: three choices per node (one `pick` plus two recursive calls), plus one. -/
def Tree.cost : Tree → Nat := fun t => 3 * t.size + 1

/-- Generates an all-`2`s tree with a uniform `pick`. Mean offspring `1`: critical, so almost surely
terminating but with infinite expected size. -/
def genTree [Gen G] : G Tree :=
  pick
    (fun () => pure .leaf)
    (fun () => do
      let l ← genTree
      let r ← genTree
      return .node l 2 r)
partial_fixpoint

theorem genTree.sound_complete : IsSoundAndComplete genTree Tree.isAllTwos := by
  refine .intro ?sound ?complete
  case sound =>
    sound_fixpoint
    all_goals simp_all [Tree.isAllTwos]
  case complete =>
    intro t
    induction t with
    | leaf => intro _; rw [genTree]; complete_bound
    | node l v r ihl ihr =>
      intro ⟨hv, hl, hr⟩
      subst hv
      rw [genTree]; complete_bound
      exact ⟨l, ihl hl, r, ihr hr, rfl⟩

theorem genTree.terminates : IsAlmostSurelyTerminating genTree := by
  mass_fixpoint using SPMF.LfpIsOne.quadratic (a := 1 / 2) (b := 0) (d := 1 / 2)
    (by ennreal_to_real; norm_num) (by ennreal_to_real; norm_num) (by norm_num)
  simp [sq]

theorem genTree.cost_bounded : IsCostBounded genTree Tree.cost := by
  cost_fixpoint
  all_goals simp only [Tree.cost, Tree.size] at *; omega

section weighted

open scoped NNReal ENNReal

/-- Generates an all-`2`s tree, but weights the leaf branch twice as heavily as the node branch. -/
def genWeightedTree [Gen G] : G Tree :=
  frequency [
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

/-- Expected size of the subcritical `genWeightedTree`: `1 / (1 - 2/3) = 3`. -/
theorem genWeightedTree_expectedSteps :
    SPMF.LevelOp.expectedSteps (fun e (j : Unit) => 2 / 3 * e j) () = 3 := by
  rw [SPMF.LevelOp.expectedSteps_const_mul,
    show (1 : ℝ≥0∞) - 2 / 3 = 1 / 3 from by ennreal_to_real; norm_num, one_div, inv_inv]

/-- Expected size of the critical `genTree` is infinite, even though it terminates a.s. -/
theorem genTree_expectedSteps_infinite :
    SPMF.LevelOp.expectedSteps (fun e (j : Unit) => 1 * e j) () = ⊤ := by
  rw [SPMF.LevelOp.expectedSteps_const_mul]
  simp

end weighted

end AllTwoTree
