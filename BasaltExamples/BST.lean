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
    frequency [
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
    (fun p : Int × Int => (Tree.genBST p.1 p.2 : SPMF (Tree Int)))
    (F := fun c => 1 / 2 + 1 / 2 * c ^ 2)
    (fun c hle hge => ?_) ?_ (lo, hi)
  · rw [← ENNReal.toReal_eq_one_iff]
    ennreal_to_real at hge
    ennreal_to_real at hle
    norm_num at hge hle
    nlinarith [sq_nonneg (c.toReal - 1)]
  · rintro ⟨lo, hi⟩
    set b := ⨅ p : Int × Int, (Tree.genBST p.1 p.2 : SPMF (Tree Int)).mass
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
      refine SPMF.mass_bind_ge_of_isPMF (SPMF.mass_chooseInt lo hi (by omega)) (fun x => ?_)
      refine SPMF.mass_bind_ge_mul (SPMF.mass_ge_iInf _ (lo, x - 1)) (fun l => ?_)
      simpa [SPMF.mass_bind_pure] using
        SPMF.mass_ge_iInf (fun p : Int × Int => (Tree.genBST p.1 p.2 : SPMF (Tree Int))) (x + 1, hi)

end termination

/-! ## Cost -/

/-- Producing a tree of `n` nodes costs at most `3 * n + 1` choices: one `frequency` choice, one
pivot, and two recursive calls per node. -/
theorem Tree.genBST.cost_bounded :
    IsCostBounded (Tree.genBST lo hi) (fun t => 3 * t.size + 1) := by
  open Lean.Order in
  delta genBST
  apply (fix_induct (motive := fun (g : Int → Int → SPMF.Cost (Tree Int)) =>
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

/-! ## Distribution -/

section distribution
open scoped ENNReal

/-- Half of the trees generated on a nonempty interval are `leaf`. -/
theorem Tree.genBST.prob_leaf {lo hi : Int} (h : lo ≤ hi) :
    SPMF.prob (Tree.genBST lo hi) {Tree.leaf} = 1/2 := by
  conv_lhs => rw [Tree.genBST]
  rw [dif_neg (by omega), SPMF.prob_frequency]
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
  delta Tree.genBST
  apply Lean.Order.fix_induct (motive := fun (g : Int → Int → SPMF (Tree Int)) =>
    ∀ lo hi, SPMF.expect (g lo hi) (fun t => (t.size : ℝ≥0∞))
      ≤ harmonic (hi + 1 - lo).toNat / 2) _ ?admissible ?step
  case admissible =>
    exact Lean.Order.admissible_pi_apply _ fun _ =>
      Lean.Order.admissible_pi_apply _ fun _ => SPMF.admissible_expect_le _ _
  case step =>
    intro genBST_rec ih lo hi
    by_cases hgt : lo > hi
    · rw [dif_pos hgt, SPMF.expect_pure]
      simp [Tree.size]
    · have hle : lo ≤ hi := by omega
      rw [dif_neg hgt, SPMF.expect_frequency]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.cast_one, one_mul,
        add_zero, SPMF.expect_pure, Tree.size, Nat.cast_zero, zero_add]
      rw [show ((1 + 1 : ℕ) : ℝ≥0∞) = 2 by norm_num]
      gcongr
      -- The node branch: average over the pivot, one `ih` per subtree, then Abel summation.
      rw [SPMF.expect_bind_chooseInt hle,
        show (hi - lo + 1).toNat = (hi + 1 - lo).toNat from by omega]
      set n := (hi + 1 - lo).toNat with hn
      have hn0 : (n : ℝ≥0∞) ≠ 0 := by
        simp only [ne_eq, Nat.cast_eq_zero]
        omega
      have hinner : ∀ x ∈ Finset.Icc lo hi,
          SPMF.expect (genBST_rec lo (x - 1) >>= fun l =>
              genBST_rec (x + 1) hi >>= fun r => Pure.pure (Tree.node l x r))
            (fun t => (t.size : ℝ≥0∞))
            ≤ 1 + harmonic (x - lo).toNat / 2 + harmonic (hi - x).toNat / 2 := by
        intro x _
        rw [SPMF.expect_bind]
        have hright : ∀ l : Tree Int,
            SPMF.expect (genBST_rec (x + 1) hi >>= fun r => Pure.pure (Tree.node l x r))
              (fun t => (t.size : ℝ≥0∞))
              ≤ (l.size : ℝ≥0∞) + (1 + harmonic (hi - x).toNat / 2) := by
          intro l
          rw [SPMF.expect_bind]
          simp only [SPMF.expect_pure]
          calc SPMF.expect (genBST_rec (x + 1) hi)
                (fun r => ((Tree.node l x r).size : ℝ≥0∞))
              = SPMF.expect (genBST_rec (x + 1) hi)
                  (fun r => ((l.size : ℝ≥0∞) + 1) + (r.size : ℝ≥0∞)) := by
                congr 1
                funext r
                simp only [Tree.size]
                push_cast
                ring
            _ = SPMF.expect (genBST_rec (x + 1) hi) (fun _ => (l.size : ℝ≥0∞) + 1)
                  + SPMF.expect (genBST_rec (x + 1) hi) (fun r => (r.size : ℝ≥0∞)) :=
                SPMF.expect_add _ _ _
            _ ≤ ((l.size : ℝ≥0∞) + 1) + harmonic (hi - x).toNat / 2 := by
                refine add_le_add ?_ ?_
                · rw [SPMF.expect_const]
                  exact le_trans (mul_le_mul_left (SPMF.mass_le_one _) _) (one_mul _).le
                · have h := ih (x + 1) hi
                  rw [show hi + 1 - (x + 1) = hi - x from by ring] at h
                  exact h
            _ = (l.size : ℝ≥0∞) + (1 + harmonic (hi - x).toNat / 2) := by ring
        calc SPMF.expect (genBST_rec lo (x - 1))
              (fun l => SPMF.expect (genBST_rec (x + 1) hi >>= fun r =>
                Pure.pure (Tree.node l x r)) (fun t => (t.size : ℝ≥0∞)))
            ≤ SPMF.expect (genBST_rec lo (x - 1))
                (fun l => (l.size : ℝ≥0∞) + (1 + harmonic (hi - x).toNat / 2)) :=
              SPMF.expect_mono fun l => hright l
          _ = SPMF.expect (genBST_rec lo (x - 1)) (fun l => (l.size : ℝ≥0∞))
                + SPMF.expect (genBST_rec lo (x - 1))
                    (fun _ => 1 + harmonic (hi - x).toNat / 2) := SPMF.expect_add _ _ _
          _ ≤ harmonic (x - lo).toNat / 2 + (1 + harmonic (hi - x).toNat / 2) := by
              refine add_le_add ?_ ?_
              · have h := ih lo (x - 1)
                rw [show x - 1 + 1 - lo = x - lo from by ring] at h
                exact h
              · rw [SPMF.expect_const]
                exact le_trans (mul_le_mul_left (SPMF.mass_le_one _) _) (one_mul _).le
          _ = 1 + harmonic (x - lo).toNat / 2 + harmonic (hi - x).toNat / 2 := by ring
      calc (∑ x ∈ Finset.Icc lo hi,
              SPMF.expect (genBST_rec lo (x - 1) >>= fun l =>
                genBST_rec (x + 1) hi >>= fun r => Pure.pure (Tree.node l x r))
                (fun t => (t.size : ℝ≥0∞))) / (n : ℝ≥0∞)
          ≤ (∑ x ∈ Finset.Icc lo hi,
              (1 + harmonic (x - lo).toNat / 2 + harmonic (hi - x).toNat / 2)) / (n : ℝ≥0∞) := by
            gcongr with x hx
            exact hinner x hx
        _ = ((∑ k ∈ Finset.range n, harmonic k) + (n : ℝ≥0∞)) / (n : ℝ≥0∞) := by
            rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Int.card_Icc]
            simp only [div_eq_mul_inv, ← Finset.sum_mul]
            simp only [← div_eq_mul_inv]
            rw [sum_Icc_harmonic_left, sum_Icc_harmonic_right, ← hn, nsmul_eq_mul, mul_one,
              add_assoc, ENNReal.add_halves,
              add_comm ((n : ℝ≥0∞)) (∑ k ∈ Finset.range n, harmonic k)]
        _ = ((n : ℝ≥0∞) * harmonic n) / (n : ℝ≥0∞) := by rw [sum_harmonic]
        _ = harmonic n := by
            rw [mul_comm, ENNReal.mul_div_cancel_right hn0 (by finiteness)]

end distribution

end BST
