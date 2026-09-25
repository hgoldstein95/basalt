/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt
import Basalt.Combinators

/-!
# Binary Search Trees
-/

open RandomChoice

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
def Tree.isBST (lo hi : Int) : Tree Int → Prop
  | leaf => true
  | node l x r =>
    lo ≤ x ∧ x ≤ hi ∧
    isBST lo (x - 1) l ∧
    isBST (x + 1) hi r

/-- Generates a BST with keys in `[lo, hi]`: return `leaf` when the interval is empty, else choose
with equal weight between a leaf and a node built from a uniform pivot and two recursive subtrees. -/
def Tree.genBST [Gen G] (lo hi : Int) : G (Tree Int) := do
  if h : lo > hi then
    return leaf
  else
    frequency! [
      (1, fun () => pure leaf),
      (1, fun () => do
        let x ← chooseInt lo hi (by omega)
        let l ← Tree.genBST lo (x - 1)
        let r ← Tree.genBST (x + 1) hi
        return node l x r)
    ] (by simp)
partial_fixpoint

theorem Tree.genBST.sound_complete :
    IsSoundAndComplete (Tree.genBST lo hi) (Tree.isBST lo hi) := by
  refine .intro ?sound ?complete
  case sound =>
    sound_fixpoint
    all_goals simp_all [Tree.isBST]
  case complete =>
    intro t
    induction t generalizing lo hi with
    | leaf => intro _; rw [Tree.genBST]; complete_bound
    | node l x r ihl ihr =>
      intro ⟨h1, h2, hl, hr⟩
      rw [Tree.genBST]; complete_bound
      rw [dite_eq_right (by omega)]
      exact ⟨x, ⟨h1, h2⟩, l, ihl hl, r, ihr hr, rfl⟩

/-! ## Termination -/

section termination
open scoped ENNReal

theorem Tree.genBST.terminates : IsAlmostSurelyTerminating (Tree.genBST lo hi) := by
  mass_fixpoint using SPMF.LfpIsOne.quadratic (a := 1 / 2) (b := 0) (d := 1 / 2)
    (by ennreal_to_real; norm_num) (by ennreal_to_real; norm_num) (by norm_num)
  split
  · rw [zero_mul, add_zero]
    calc (1 : ℝ≥0∞) / 2 + 1 / 2 * c ^ 2 ≤ 1 / 2 + 1 / 2 * 1 ^ 2 := by gcongr
      _ = 1 := by rw [one_pow, mul_one, ENNReal.add_halves]
  · simp [sq, ENNReal.div_eq_inv_mul, mul_add]

end termination

/-! ## Faithfulness -/

theorem Tree.genBST.faithful : IsFaithful (Tree.genBST lo hi) := by
  faithful_fixpoint

/-! ## Cost -/

/-- Producing a tree of `n` nodes costs at most `3 * n + 1` choices: one `frequency` choice, one
pivot, and two recursive calls per node. -/
theorem Tree.genBST.cost_bounded :
    IsCostBounded (Tree.genBST lo hi) (fun t => 3 * t.size + 1) := by
  cost_fixpoint
  all_goals simp only [Tree.size]; omega

/-! ## Distribution -/

section distribution
open scoped ENNReal

/-- Half of the trees generated on a nonempty interval are `leaf`. -/
theorem Tree.genBST.prob_leaf {lo hi : Int} (h : lo ≤ hi) :
    SPMF.prob (Tree.genBST lo hi) {Tree.leaf} = 1/2 := by
  conv_lhs => rw [Tree.genBST]
  rw [dite_eq_right (by omega), frequencyWith_eq, SPMF.prob_frequency]
  have hleaf : SPMF.prob (Pure.pure Tree.leaf : SPMF (Tree Int)) {Tree.leaf} = 1 := by
    rw [SPMF.prob_singleton]
    simp
  have hnode : SPMF.prob
      ((chooseInt lo hi (by omega) >>= fun x =>
        Tree.genBST lo (x - 1) >>= fun l =>
        Tree.genBST (x + 1) hi >>= fun r =>
        Pure.pure (Tree.node l x r)) : SPMF (Tree Int)) {Tree.leaf} = 0 := by
    rw [SPMF.prob_eq_zero_iff]
    intro t ht
    support_simp at ht
    obtain ⟨x, hx, l, hl, r, hr, rfl⟩ := ht
    simp
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.cast_one, one_mul,
    add_zero, hleaf, hnode]
  rw [show ((1 + 1 : ℕ) : ℝ≥0∞) = 2 by norm_num]

/-- The `n`-th harmonic number, in `ℝ≥0∞`. -/
noncomputable def harmonic (n : ℕ) : ℝ≥0∞ := ∑ k ∈ Finset.range n, 1 / ((k : ℝ≥0∞) + 1)

/-- The Abel-summation identity `Σ_{k<n} Hₖ = n·Hₙ - n`, stated additively for `ℝ≥0∞`. -/
theorem sum_harmonic (n : ℕ) :
    ∑ k ∈ Finset.range n, harmonic k + (n : ℝ≥0∞) = (n : ℝ≥0∞) * harmonic n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hh : harmonic (n + 1) = harmonic n + 1 / ((n : ℝ≥0∞) + 1) := by
      unfold harmonic
      rw [Finset.sum_range_succ]
    have hcancel : ((n : ℝ≥0∞) + 1) * (1 / ((n : ℝ≥0∞) + 1)) = 1 := by
      rw [one_div, ENNReal.mul_inv_cancel (by positivity) (by finiteness)]
    rw [Finset.sum_range_succ, hh]
    push_cast
    calc ∑ k ∈ Finset.range n, harmonic k + harmonic n + ((n : ℝ≥0∞) + 1)
        = (∑ k ∈ Finset.range n, harmonic k + (n : ℝ≥0∞)) + (harmonic n + 1) := by ring
      _ = (n : ℝ≥0∞) * harmonic n + (harmonic n + 1) := by rw [ih]
      _ = ((n : ℝ≥0∞) + 1) * harmonic n + ((n : ℝ≥0∞) + 1) * (1 / ((n : ℝ≥0∞) + 1)) := by
          rw [hcancel]; ring
      _ = ((n : ℝ≥0∞) + 1) * (harmonic n + 1 / ((n : ℝ≥0∞) + 1)) := by ring

private theorem sum_Icc_harmonic_left {lo hi : Int} :
    ∑ x ∈ Finset.Icc lo hi, harmonic (x - lo).toNat
      = ∑ k ∈ Finset.range (hi + 1 - lo).toNat, harmonic k := by
  refine Finset.sum_nbij' (fun x => (x - lo).toNat) (fun k => lo + (k : Int))
    (fun x hx => ?_) (fun k hk => ?_) (fun x hx => ?_) (fun k hk => ?_) (fun x hx => rfl)
  · simp only [Finset.mem_Icc] at hx; simp only [Finset.mem_range]; omega
  · simp only [Finset.mem_range] at hk; simp only [Finset.mem_Icc]; omega
  · simp only [Finset.mem_Icc] at hx; omega
  · simp only [Finset.mem_range] at hk; omega

private theorem sum_Icc_harmonic_right {lo hi : Int} :
    ∑ x ∈ Finset.Icc lo hi, harmonic (hi - x).toNat
      = ∑ k ∈ Finset.range (hi + 1 - lo).toNat, harmonic k := by
  refine Finset.sum_nbij' (fun x => (hi - x).toNat) (fun k => hi - (k : Int))
    (fun x hx => ?_) (fun k hk => ?_) (fun x hx => ?_) (fun k hk => ?_) (fun x hx => rfl)
  · simp only [Finset.mem_Icc] at hx; simp only [Finset.mem_range]; omega
  · simp only [Finset.mem_range] at hk; simp only [Finset.mem_Icc]; omega
  · simp only [Finset.mem_Icc] at hx; omega
  · simp only [Finset.mem_range] at hk; omega

/-- The expected size on `n` available keys is at most `Hₙ / 2` — logarithmic, and in fact exact:
a uniform pivot splits the interval like a random binary search tree, and the geometric stop
halves each level's contribution. -/
theorem Tree.genBST.expect_size_le {lo hi : Int} :
    SPMF.expect (Tree.genBST lo hi) (fun t => (t.size : ℝ≥0∞))
      ≤ harmonic (hi + 1 - lo).toNat / 2 := by
  expect_fixpoint
  split
  · simp [Tree.size]
  · rename_i hgt
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.cast_one, one_mul,
      add_zero, Tree.size, Nat.cast_zero, zero_add]
    rw [show ((1 + 1 : ℕ) : ℝ≥0∞) = 2 by norm_num,
      show (hi - lo + 1).toNat = (hi + 1 - lo).toNat from by omega]
    gcongr
    set n := (hi + 1 - lo).toNat with hn
    have hn0 : (n : ℝ≥0∞) ≠ 0 := by
      simp only [ne_eq, Nat.cast_eq_zero]
      omega
    have hsummand : ∀ x ∈ Finset.Icc lo hi,
        (1 + harmonic (hi + 1 - (x + 1)).toNat / 2 + harmonic (x - 1 + 1 - lo).toNat / 2 : ℝ≥0∞)
          = 1 + harmonic (x - lo).toNat / 2 + harmonic (hi - x).toNat / 2 := by
      intro x _
      rw [show hi + 1 - (x + 1) = hi - x by ring, show x - 1 + 1 - lo = x - lo by ring]
      ring
    rw [Finset.sum_congr rfl hsummand]
    calc (∑ x ∈ Finset.Icc lo hi,
            (1 + harmonic (x - lo).toNat / 2 + harmonic (hi - x).toNat / 2)) / (n : ℝ≥0∞)
        = ((∑ k ∈ Finset.range n, harmonic k) + (n : ℝ≥0∞)) / (n : ℝ≥0∞) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Int.card_Icc]
          simp only [div_eq_mul_inv, ← Finset.sum_mul]
          simp only [← div_eq_mul_inv]
          rw [sum_Icc_harmonic_left, sum_Icc_harmonic_right, ← hn, nsmul_eq_mul, mul_one,
            add_assoc, ENNReal.add_halves,
            add_comm ((n : ℝ≥0∞)) (∑ k ∈ Finset.range n, harmonic k)]
      _ = ((n : ℝ≥0∞) * harmonic n) / (n : ℝ≥0∞) := by rw [sum_harmonic]
      _ ≤ harmonic n := by
          rw [mul_comm, ENNReal.mul_div_cancel_right hn0 (by finiteness)]

end distribution

end BST
