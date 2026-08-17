/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt
import Basalt.Combinators

open RandomChoice

/-!
# Binary Search Trees

`Tree.genBST lo hi` generates binary search trees with keys in `[lo, hi]`: pick a uniform pivot,
then recurse on the two subintervals. Like `genTree` and `genHeap` it is *critical* — a leaf with
probability `1/2`, otherwise a node with two recursive children, so mean offspring is exactly `1` —
and termination follows from the same `IsPMF_of_critical_family` criterion, with no ranking function.

The `frequency`-weighted, `@[tunable]` variant `genWeightedBST` lives in `BasaltExamples/BST/Weighted`.
Weighting `node` five times as heavily makes it *supercritical* under that crude bound, so it does
need a ranking function that exploits the shrinking interval — that machinery lives with it.
-/

namespace BST

/-- A binary tree with values of type `α`. -/
inductive Tree (α : Type) where
  | leaf : Tree α
  | node : Tree α → α → Tree α → Tree α
deriving Repr

/-- The number of nodes in the tree. -/
def Tree.size : Tree α → Nat
  | leaf => 0
  | node l _ r => l.size + r.size + 1

/-- The validity predicate: a binary search tree with every key in `[lo, hi]`. -/
def Tree.isBST (lo hi : Nat) : Tree Nat → Prop
  | leaf => true
  | node l x r =>
    lo ≤ x ∧ x ≤ hi ∧
    isBST lo (x - 1) l ∧
    isBST (x + 1) hi r

/-- Generates a BST with keys in `[lo, hi]`: return `leaf` when the interval is empty, else `pick`
between a leaf and a node built from a uniform pivot and two recursive subtrees. -/
def Tree.genBST [Gen G] (lo hi : Nat) : G (Tree Nat) := do
  if h : lo > hi then
    return leaf
  else
    pick
      (fun () => pure leaf)
      (fun () => do
        let x ← chooseNat lo hi (by omega)
        let l ← Tree.genBST lo (x - 1)
        let r ← Tree.genBST (x + 1) hi
        return node l x r)
partial_fixpoint

theorem Tree.genBST.sound_complete :
    IsSoundAndComplete (Tree.genBST lo hi) (Tree.isBST lo hi) := by
  intro t
  fun_induction Tree.isBST
    <;> rw [Tree.genBST]
    <;> split
    <;> simp
    <;> grind

/-! ## Termination -/

section termination
open scoped ENNReal

theorem Tree.genBST.terminates : IsAlmostSurelyTerminating (Tree.genBST lo hi) := by
  refine SPMF.IsPMF_of_critical_family
    (fun p : Nat × Nat => (Tree.genBST p.1 p.2 : SPMF (Tree Nat)))
    (F := fun c => 1 / 2 + 1 / 2 * c ^ 2)
    (fun c hle hge => ?_) ?_ (lo, hi)
  · rw [← ENNReal.toReal_eq_one_iff]
    ennreal_to_real at hge
    ennreal_to_real at hle
    norm_num at hge hle
    nlinarith [sq_nonneg (c.toReal - 1)]
  · rintro ⟨lo, hi⟩
    set b := ⨅ p : Nat × Nat, (Tree.genBST p.1 p.2 : SPMF (Tree Nat)).mass
    by_cases hgt : lo > hi
    · beta_reduce
      rw [Tree.genBST, dif_pos hgt, SPMF.mass_pure]
      have hb1 : b ≤ 1 := le_trans (SPMF.mass_ge_iInf _ (lo, hi)) (SPMF.mass_le_one _)
      calc (1 : ℝ≥0∞) / 2 + 1 / 2 * b ^ 2 ≤ 1 / 2 + 1 / 2 * 1 ^ 2 := by gcongr
        _ = 1 := by rw [one_pow, mul_one, ENNReal.add_halves]
    · beta_reduce
      conv_rhs => rw [Tree.genBST]
      rw [dif_neg hgt]
      simp only [SPMF.mass_pick, SPMF.mass_pure, mul_one]
      gcongr
      rw [sq]
      refine SPMF.mass_bind_ge_of_isPMF (SPMF.mass_chooseNat lo hi (by omega)) (fun x => ?_)
      refine SPMF.mass_bind_ge_mul (SPMF.mass_ge_iInf _ (lo, x - 1)) (fun l => ?_)
      simpa [SPMF.mass_bind_pure] using
        SPMF.mass_ge_iInf (fun p : Nat × Nat => (Tree.genBST p.1 p.2 : SPMF (Tree Nat))) (x + 1, hi)

end termination

/-! ## Cost -/

/-- Producing a tree of `n` nodes costs at most `3 * n + 1` choices: one `pick` and two recursive
calls per node. -/
theorem Tree.genBST.cost_bounded :
    IsCostBounded (Tree.genBST lo hi) (fun t => 3 * t.size + 1) := by
  open Lean.Order in
  delta genBST
  apply (fix_induct (motive := fun (g : Nat → Nat → SPMF.Cost (Tree Nat)) =>
    ∀ lo hi, IsBounded (g lo hi) (fun t => 3 * t.size + 1)) _ ?admissible ?step)
  case admissible =>
    exact admissible_pi_apply _ fun _ => admissible_pi_apply _ fun _ => admissible_IsBounded _
  case step =>
    intro genBST_rec ih lo hi
    rw [IsBounded_iff]
    rintro ⟨t, n⟩ hmem
    cost_support_simp at hmem
    obtain ⟨_, rfl, rfl⟩ | ⟨_, m, hn, hmem⟩ := hmem
    · simp [Tree.size]
    · obtain ⟨rfl, rfl⟩ | ⟨x, n1, n2, ⟨⟨hxlo, hxhi⟩, hn1⟩, hmem, hm⟩ := hmem
      · simp only [Tree.size]
        omega
      · obtain ⟨l, n3, n4, hl, hmem, hn2⟩ := hmem
        obtain ⟨r, n5, n6, hr, ⟨rfl, hn6⟩, hn4⟩ := hmem
        have hL : n3 ≤ 3 * l.size + 1 := ih lo (x - 1) (l, n3) hl
        have hR : n5 ≤ 3 * r.size + 1 := ih (x + 1) hi (r, n5) hr
        simp only [Tree.size]
        omega

end BST
