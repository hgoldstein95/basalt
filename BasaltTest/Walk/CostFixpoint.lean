/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt
import BasaltExamples.BST
import BasaltExamples.Heap
import BasaltExamples.SortedList.BySorting

/-!
# The Cost Fixpoint Contract

Pins the step `walk fixpoint` leaves on `SPMF.Cost.alwaysObs.spec`: the recursive function named
after the generator, `ih` over the arguments its recursive calls change, and the walk's residuals.
-/

open RandomChoice ArbNat

namespace CostFixpointTest

/--
trace: arbitrary : SPMF.Cost ℕ
ih : SPMF.Cost.alwaysObs.spec arbitrary fun v n_v => n_v ≤ v + 1
⊢ 1 + 0 ≤ 0 + 1

arbitrary : SPMF.Cost ℕ
ih : SPMF.Cost.alwaysObs.spec arbitrary fun v n_v => n_v ≤ v + 1
n✝ n_n✝ : ℕ
h_n✝ : n_n✝ ≤ n✝ + 1
⊢ 1 + (n_n✝ + 0) ≤ n✝ + 1 + 1
-/
#guard_msgs in
example : IsCostBounded Nat.arbitrary (fun n => n + 1) := by
  rw [IsCostBounded.iff_obs]
  walk fixpoint
  trace_state
  all_goals omega

/--
trace: genHeap : ℕ → SPMF.Cost Heap.Tree
ih : ∀ (lo : ℕ), SPMF.Cost.alwaysObs.spec (genHeap lo) fun v n_v => n_v ≤ 3 * v.size + v.sum + 1
lo : ℕ
⊢ 1 + 0 ≤ 3 * Heap.Tree.leaf.size + Heap.Tree.leaf.sum + 1

genHeap : ℕ → SPMF.Cost Heap.Tree
ih : ∀ (lo : ℕ), SPMF.Cost.alwaysObs.spec (genHeap lo) fun v n_v => n_v ≤ 3 * v.size + v.sum + 1
lo delta✝ n_delta✝ : ℕ
h_delta✝ : n_delta✝ ≤ delta✝ + 1
l✝ : Heap.Tree
n_l✝ : ℕ
h_l✝ : n_l✝ ≤ 3 * l✝.size + l✝.sum + 1
r✝ : Heap.Tree
n_r✝ : ℕ
h_r✝ : n_r✝ ≤ 3 * r✝.size + r✝.sum + 1
⊢ 1 + (n_delta✝ + (n_l✝ + (n_r✝ + 0))) ≤ 3 * (l✝.node (lo + delta✝) r✝).size + (l✝.node (lo + delta✝) r✝).sum + 1
-/
#guard_msgs in
example : IsCostBounded (Heap.Tree.genHeap lo) (fun t => 3 * t.size + t.sum + 1) := by
  rw [IsCostBounded.iff_obs]
  walk fixpoint [Nat.arbitrary.cost_bounded.obs]
  trace_state
  all_goals simp only [Heap.Tree.size, Heap.Tree.sum]; omega

-- A two-argument seed; the `dite`'s and `frequency`'s paths each leave a goal, and a pivot's range
-- is a hypothesis.
/--
trace: genBST : ℤ → ℤ → SPMF.Cost (BST.Tree ℤ)
ih : ∀ (lo hi : ℤ), SPMF.Cost.alwaysObs.spec (genBST lo hi) fun v n_v => n_v ≤ 3 * v.size + 1
lo hi : ℤ
h✝ : lo > hi
⊢ 0 ≤ 3 * BST.Tree.leaf.size + 1

genBST : ℤ → ℤ → SPMF.Cost (BST.Tree ℤ)
ih : ∀ (lo hi : ℤ), SPMF.Cost.alwaysObs.spec (genBST lo hi) fun v n_v => n_v ≤ 3 * v.size + 1
lo hi : ℤ
h✝ : ¬lo > hi
⊢ 1 + 0 ≤ 3 * BST.Tree.leaf.size + 1

genBST : ℤ → ℤ → SPMF.Cost (BST.Tree ℤ)
ih : ∀ (lo hi : ℤ), SPMF.Cost.alwaysObs.spec (genBST lo hi) fun v n_v => n_v ≤ 3 * v.size + 1
lo hi : ℤ
h✝ : ¬lo > hi
x✝ : ℤ
h_x✝ : lo ≤ x✝ ∧ x✝ ≤ hi
l✝ : BST.Tree ℤ
n_l✝ : ℕ
h_l✝ : n_l✝ ≤ 3 * l✝.size + 1
r✝ : BST.Tree ℤ
n_r✝ : ℕ
h_r✝ : n_r✝ ≤ 3 * r✝.size + 1
⊢ 1 + (1 + (n_l✝ + n_r✝)) ≤ 3 * (l✝.node x✝ r✝).size + 1
-/
#guard_msgs in
example : IsCostBounded (BST.Tree.genBST lo hi) (fun t => 3 * t.size + 1) := by
  rw [IsCostBounded.iff_obs]
  walk fixpoint
  trace_state
  all_goals simp only [BST.Tree.size]; omega

/-- A parameter the recursion keeps fixed may come after one it changes. -/
def g [Gen G] (n : Nat) (b : Bool) : G Nat :=
  oneOf [fun _ => pure 0, fun _ => g (n + 1) b >>= fun k => pure (k + 1)]
partial_fixpoint

-- A bound that mentions the seed is restated at each recursive call's.
/--
trace: b : Bool
g : ℕ → SPMF.Cost ℕ
ih : ∀ (n : ℕ), SPMF.Cost.alwaysObs.spec (g n) fun v n_v => n_v ≤ v + 1 + n - n
n : ℕ
⊢ 1 + 0 ≤ 0 + 1 + n - n

b : Bool
g : ℕ → SPMF.Cost ℕ
ih : ∀ (n : ℕ), SPMF.Cost.alwaysObs.spec (g n) fun v n_v => n_v ≤ v + 1 + n - n
n k✝ n_k✝ : ℕ
h_k✝ : n_k✝ ≤ k✝ + 1 + (n + 1) - (n + 1)
⊢ 1 + (n_k✝ + 0) ≤ k✝ + 1 + 1 + n - n
-/
#guard_msgs in
example (n : Nat) (b : Bool) : IsCostBounded (g n b) (fun k => k + 1 + n - n) := by
  rw [IsCostBounded.iff_obs]
  walk fixpoint
  trace_state
  all_goals omega

/-- A generator with no recursion is unfolded and walked. -/
example : IsCostBounded SortedList.List.genSortedBySorting (fun ys => 2 * ys.length + ys.sum + 1) := by
  rw [IsCostBounded.iff_obs]
  walk fixpoint [ArbList.List.arbitrary.cost_bounded.obs]
  expose_names
  have hperm := List.mergeSort_perm xs (fun a b => a ≤ b)
  simp only [hperm.length_eq, hperm.sum_eq]
  omega

/--
error: walk fixpoint: `listOf` is a combinator, not a generator definition; prove a bound on a combinator term with `walk`
-/
#guard_msgs in
example : IsCostBounded (listOf Nat.arbitrary) (fun xs => xs.length + (xs.map (· + 1)).sum + 1) := by
  rw [IsCostBounded.iff_obs]
  walk fixpoint

/-- The goals of a tactic `match` are recognized. -/
def byCases [Gen G] (n : Nat) : G Nat :=
  match n with
  | 0 => pure 0
  | _ + 1 => chooseNat 0 1

example (n : Nat) : IsCostBounded (byCases n) (fun _ => 1) := by
  match n with
  | 0 => rw [IsCostBounded.iff_obs]; walk fixpoint; omega
  | _ + 1 => rw [IsCostBounded.iff_obs]; walk fixpoint; omega


-- A `match` on the seed is entered: one goal per case, the seed replaced by its pattern.
/--
trace: ⊢ 0 ≤ 1

v✝ : ℕ
h_v✝ : 0 ≤ v✝ ∧ v✝ ≤ 1
⊢ 1 ≤ 1
-/
#guard_msgs in
example (n : Nat) : IsCostBounded (byCases n) (fun _ => 1) := by
  rw [IsCostBounded.iff_obs]
  walk fixpoint
  trace_state
  all_goals omega

def fuelled [Gen G] (fuel : Nat) : G (BST.Tree Nat) :=
  if _h : fuel = 0 then pure .leaf
  else
    oneOf [fun _ => pure .leaf, fun _ => do
      let l ← fuelled (fuel - 1)
      let r ← fuelled (fuel - 1)
      return .node l 0 r]
termination_by fuel

/--
error: walk fixpoint: `CostFixpointTest.fuelled` is recursive but not a `partial_fixpoint`; induct on its decreasing argument, unfold it, and apply `walk`
-/
#guard_msgs in
example (fuel : Nat) : IsCostBounded (fuelled fuel) (fun t => 3 * t.size + 1) := by
  rw [IsCostBounded.iff_obs]
  walk fixpoint

-- The route the error names. The base case discards the branch it cannot take first: the walk
-- bounds both branches, and nothing bounds `fuelled (0 - 1)`.
example (fuel : Nat) : IsCostBounded (fuelled fuel) (fun t => 3 * t.size + 1) := by
  induction fuel with
  | zero => rw [fuelled, dite_eq_left rfl, IsCostBounded.iff_obs]; walk; simp
  | succ n ih =>
    rw [fuelled, IsCostBounded.iff_obs]
    walk [ih.obs]
    all_goals simp only [BST.Tree.size]; omega

end CostFixpointTest
