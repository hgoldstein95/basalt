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

/-- Generates a BST with keys in `[lo, hi]`: return `leaf` when the interval is empty, else choose
with equal weight between a leaf and a node built from a uniform pivot and two recursive subtrees. -/
def Tree.genBST [Gen G] (lo hi : Nat) : G (Tree Nat) := do
  if h : lo > hi then
    return leaf
  else
    frequency [
      (1, fun () => pure leaf),
      (1, fun () => do
        let x ← chooseNat lo hi (by omega)
        let l ← Tree.genBST lo (x - 1)
        let r ← Tree.genBST (x + 1) hi
        return node l x r)
    ] (by simp)
partial_fixpoint

theorem Tree.genBST.sound_complete :
    IsSoundAndComplete (Tree.genBST lo hi) (Tree.isBST lo hi) := by
  intro t
  fun_induction Tree.isBST
    <;> rw [Tree.genBST]
    <;> split
    <;> simp
  · exact ⟨1, fun _ => Pure.pure .leaf, Or.inl ⟨rfl, rfl⟩, one_pos, by simp⟩
  · intros
    omega
  · constructor
    · rintro ⟨w, g, hbr, hw, hmem⟩
      rcases hbr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · simp at hmem
      · revert hmem
        simp
        grind
    · rintro ⟨h1, h2, hl, hr⟩
      refine ⟨1, _, Or.inr ⟨rfl, rfl⟩, one_pos, ?_⟩
      simp
      grind

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
    · rw [Tree.genBST, dif_pos hgt, SPMF.mass_pure]
      have hb1 : b ≤ 1 := le_trans (SPMF.mass_ge_iInf _ (lo, hi)) (SPMF.mass_le_one _)
      calc (1 : ℝ≥0∞) / 2 + 1 / 2 * b ^ 2 ≤ 1 / 2 + 1 / 2 * 1 ^ 2 := by gcongr
        _ = 1 := by rw [one_pow, mul_one, ENNReal.add_halves]
    · conv_rhs => rw [Tree.genBST]
      rw [dif_neg hgt]
      rw [SPMF.mass_frequency]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, SPMF.mass_pure,
        Nat.cast_one, add_zero, one_mul]
      rw [show ((1 + 1 : ℕ) : ℝ≥0∞) = 2 by norm_num, ENNReal.add_div, ENNReal.div_eq_inv_mul,
        ENNReal.div_eq_inv_mul]
      simp only [mul_one]
      gcongr
      rw [sq]
      refine SPMF.mass_bind_ge_of_isPMF (SPMF.mass_chooseNat lo hi (by omega)) (fun x => ?_)
      refine SPMF.mass_bind_ge_mul (SPMF.mass_ge_iInf _ (lo, x - 1)) (fun l => ?_)
      simpa [SPMF.mass_bind_pure] using
        SPMF.mass_ge_iInf (fun p : Nat × Nat => (Tree.genBST p.1 p.2 : SPMF (Tree Nat))) (x + 1, hi)

end termination

/-! ## Cost -/

/-- Producing a tree of `n` nodes costs at most `3 * n + 1` choices: one `frequency` choice, one
pivot, and two recursive calls per node. -/
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
    rw [SPMF.mem_support_dite_iff] at hmem
    obtain ⟨_, hmem⟩ | ⟨_, hmem⟩ := hmem
    · cost_support_simp at hmem
      obtain ⟨rfl, rfl⟩ := hmem
      simp [Tree.size]
    · obtain ⟨w, g, m, hbr, hw, hmem, rfl⟩ := SPMF.Cost.mem_support_frequency hmem
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hbr
      obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := hbr
      · cost_support_simp at hmem
        obtain ⟨rfl, rfl⟩ := hmem
        simp [Tree.size]
      · cost_support_simp at hmem
        obtain ⟨x, n1, n2, ⟨⟨hxlo, hxhi⟩, hn1⟩, hmem, hm⟩ := hmem
        obtain ⟨l, n3, n4, hl, hmem, hn2⟩ := hmem
        obtain ⟨r, n5, n6, hr, ⟨rfl, hn6⟩, hn4⟩ := hmem
        have hL : n3 ≤ 3 * l.size + 1 := ih lo (x - 1) (l, n3) hl
        have hR : n5 ≤ 3 * r.size + 1 := ih (x + 1) hi (r, n5) hr
        simp only [Tree.size]
        omega

end BST
