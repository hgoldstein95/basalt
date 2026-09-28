/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt
import BasaltExamples.ArbNat

/-!
# Min-Heaps

`Tree.genHeap lo` generates arbitrary binary min-heaps whose values are all at least `lo`. It draws
each node's value as `lo` plus a `Nat.arbitrary` gap, then recurses on both children with that
value as the new lower bound. Like `SortedList`, the recursion re-indexes the seed; unlike it,
recursing on *two* children makes the mean offspring exactly `1`, so this is a **critical**
generator: almost surely terminating, with no finite bound on its expected cost
(`Tree.genHeap.not_expected_cost_bounded`).
-/

open RandomChoice ArbNat

namespace Heap

/-- A binary tree with `Nat`-labelled nodes. -/
inductive Tree where
  | leaf : Tree
  | node : Tree → Nat → Tree → Tree
deriving Repr

/-- The number of nodes in the tree. -/
def Tree.size : Tree → Nat
  | leaf => 0
  | node l _ r => l.size + r.size + 1

/-- The sum of every value stored in the tree. -/
def Tree.sum : Tree → Nat
  | leaf => 0
  | node l x r => l.sum + x + r.sum

/-- A `Tree` is a min-heap bounded below by `lo` when every node's value is at
    least `lo` and each subtree is itself a min-heap bounded below by that node's
    value. -/
def Tree.isHeap (lo : Nat) : Tree → Prop
  | leaf => True
  | node l x r =>
    lo ≤ x ∧
    isHeap x l ∧
    isHeap x r

/-- Generates an arbitrary min-heap whose values are all at least `lo`. -/
def Tree.genHeap [Gen G] (lo : Nat) : G Tree :=
  oneOf! [
    fun _ => pure leaf,
    fun _ => do
      let delta ← Nat.arbitrary
      let x := lo + delta
      let l ← Tree.genHeap x
      let r ← Tree.genHeap x
      return node l x r]
partial_fixpoint

theorem Tree.genHeap.sound_complete :
    IsSoundAndComplete (Tree.genHeap lo) (Tree.isHeap lo) := by
  refine .intro ?sound ?complete
  case sound =>
    rw [IsSoundFor.iff_obs]
    walk fixpoint [Nat.arbitrary.sound_complete.sound.obs]
    all_goals simp_all [Tree.isHeap]
  case complete =>
    intro t h
    fun_induction isHeap <;> rw [Tree.genHeap, SPMF.mem_support_iff_may]
    all_goals walk [Nat.arbitrary.sound_complete.complete.obs]
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h.1
    simp_all

theorem Tree.genHeap.terminates : IsAlmostSurelyTerminating (Tree.genHeap lo) := by
  mass_fixpoint [Nat.arbitrary.terminates.obs]
    using SPMF.LfpIsOne.quadratic (a := 1 / 2) (b := 0) (d := 1 / 2)
    (by ennreal_to_real; norm_num) (by ennreal_to_real; norm_num) (by norm_num)
  simp [sq, ENNReal.div_eq_inv_mul, mul_add]

/-- The number of random choices is bounded by the tree's size and value-sum (no backtracking). -/
theorem Tree.genHeap.cost_bounded :
    IsCostBounded (Tree.genHeap lo) (fun t => 3 * t.size + t.sum + 1) := by
  rw [IsCostBounded.iff_obs]
  walk fixpoint [Nat.arbitrary.cost_bounded.obs]
  all_goals simp only [Tree.size, Tree.sum]; omega

theorem Tree.genHeap.faithful : IsFaithful (Tree.genHeap lo) := by
  faithful_fixpoint [Tree.genHeap.terminates, Nat.arbitrary.faithful]

theorem Tree.genHeap.cost_faithful : IsCostFaithful (Tree.genHeap lo) :=
  ⟨by walk fixpoint [Nat.arbitrary.cost_faithful.erasedLe],
    by walk fixpoint [Nat.arbitrary.cost_faithful.leErased]⟩

open scoped ENNReal in
/-- The children are drawn at a new lower bound, so the step is stated over the least expected cost
at any bound, `m`: one unfolding costs at least `1 + m`. -/
theorem Tree.genHeap.not_expected_cost_bounded {B : ℝ≥0∞} (hB : B ≠ ⊤) (lo : Nat) :
    ¬ IsExpectedCostBounded (Tree.genHeap lo : SPMF.Cost Tree) B := by
  refine IsExpectedCostBounded.not_of_step_iInf (g := fun lo => Tree.genHeap lo) one_ne_zero hB
    (fun lo => ?_) lo
  have hm := fun lo' => (Tree.genHeap.cost_faithful (lo := lo')).one_le_mass Tree.genHeap.terminates
  have hnat := Nat.arbitrary.cost_faithful.one_le_mass Nat.arbitrary.terminates
  conv_rhs => rw [Tree.genHeap]
  walk [fun lo' => SPMF.Cost.le_expect_add (hm lo')
      (iInf_le (fun j => SPMF.Cost.expectObs.spec (Tree.genHeap j : SPMF.Cost Tree)
        (fun _ n => (n : ℝ≥0∞))) lo'),
    SPMF.Cost.le_expect_add (x := Nat.arbitrary) (h := fun _ n => (n : ℝ≥0∞)) hnat zero_le]
  generalize ⨅ j, SPMF.Cost.expectObs.spec (Tree.genHeap j : SPMF.Cost Tree)
    (fun _ n => (n : ℝ≥0∞)) = m
  norm_num
  rw [ENNReal.le_div_iff_mul_le (by norm_num) (by norm_num)]
  exact le_of_eq (by ring)

end Heap
