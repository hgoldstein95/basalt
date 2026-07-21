/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt
import BasaltExamples.BST

open RandomChoice
open SPMF
open scoped NNReal ENNReal

/-!
# Weighted Binary Search Trees

`Tree.genWeightedBST` is a `frequency`-weighted, `tunable` variant of `genBST`
(`BasaltExamples/BST`) that makes `node` five times as likely as `leaf`. It produces the same trees
with the same cost bound; only the distribution differs.

Unlike `genBST`, this weighting is *supercritical* under the crude branching bound (`node` has
probability `5/6`, so mean offspring is `5/6 · 2 = 5/3 > 1`), so `IsPMF_of_critical_family` does not
apply. Termination instead goes through a ranking function on the seed `(lo, hi)`, exploiting the
fact that the interval genuinely shrinks. The machinery (`bstLevel`, `bstRank`) lives here since it
is used nowhere else, instantiated at recursion weight `w = 5/6` and drift `ε = 1/6`.
-/

namespace BST

/-- Like `genBST` but `frequency`-weighted so `node` is five times as likely as `leaf`, and
`tunable` so the weights are runtime-addressable (see `BasaltTest/Tuning.lean`). -/
tunable def Tree.genWeightedBST [Gen G] (lo hi : Nat) : G (Tree Nat) := do
  if h : lo > hi then
    return leaf
  else
    frequency [
      (1, fun _ => pure leaf),
      (5, fun _ => do
        let x ← choose lo hi (by omega)
        let l ← Tree.genWeightedBST lo (x.down.val - 1)
        let r ← Tree.genWeightedBST (x.down.val + 1) hi
        return node l x.down.val r)
    ] (by simp)
partial_fixpoint

/-- The level operator: recurse with probability `w` on the two subintervals of a uniform pivot. -/
private noncomputable def bstLevel (w : ℝ≥0∞) (e : Nat × Nat → ℝ≥0∞) (p : Nat × Nat) : ℝ≥0∞ :=
  if p.1 > p.2 then 0
  else w * ((∑ x ∈ Finset.Icc p.1 p.2, (e (p.1, x - 1) + e (x + 1, p.2)))
    / ((p.2 - p.1 + 1 : ℕ) : ℝ≥0∞))

/-- The ranking function. The `+ 4` bump at `lo = 0` compensates for `Nat` truncation: the
  pivot `x = 0` recurses on `(0, 0 - 1) = (0, 0)`, an unshrunk seed, so the plain interval
  measure has positive drift there. -/
private def bstRank (p : Nat × Nat) : Nat :=
  (p.2 + 1 - p.1) + 1 + (if p.1 = 0 then 4 else 0)

private theorem levelOp_bstLevel (w : ℝ≥0∞) : LevelOp (bstLevel w) := by
  constructor
  · -- mono
    intro e f hef p
    unfold bstLevel
    split
    · exact le_rfl
    · gcongr with x hx <;> exact hef _
  · -- add
    intro e f
    funext p
    simp only [bstLevel, Pi.add_apply]
    split
    · simp
    · simp only [add_add_add_comm, Finset.sum_add_distrib, ← ENNReal.div_add_div_same, mul_add]
  · -- smul
    intro r e
    funext p
    simp only [bstLevel]
    split
    · simp
    · simp only [← mul_add, ← Finset.mul_sum, ← mul_div_assoc, mul_left_comm]

/-- Away from `lo = 0`, the children's total rank equals the parent's rank *exactly, for every
  pivot* — the interval partitions. Summed over the `hi - lo + 1` pivots: -/
private lemma bstRank_sum_pos {lo hi : Nat} (h1 : 1 ≤ lo) (hle : lo ≤ hi) :
    ∑ x ∈ Finset.Icc lo hi, (bstRank (lo, x - 1) + bstRank (x + 1, hi))
      = (hi - lo + 1) * bstRank (lo, hi) := by
  have hterm : ∀ x ∈ Finset.Icc lo hi,
      bstRank (lo, x - 1) + bstRank (x + 1, hi)
        = bstRank (lo, hi) := by
    intro x hx
    rw [Finset.mem_Icc] at hx
    have hlo : ¬(lo = 0) := by omega
    have hx1 : ¬(x + 1 = 0) := by omega
    simp only [bstRank, if_neg hlo, if_neg hx1]
    omega
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, Nat.card_Icc, smul_eq_mul]
  congr 1
  omega

/-- At `lo = 0` the pivot `x = 0` recurses on `(0, 0)` — an *unshrunk* child — and the
  children's total rank exceeds the parent's by exactly 1 at that pivot (and only there). -/
private lemma bstRank_sum_zero (hi : Nat) :
    ∑ x ∈ Finset.Icc 0 hi, (bstRank (0, x - 1) + bstRank (x + 1, hi))
      = (hi + 1) * bstRank (0, hi) + 1 := by
  have hsplit : Finset.Icc 0 hi = insert 0 (Finset.Icc 1 hi) := by
    ext y
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have h0 : (0 : Nat) ∉ Finset.Icc 1 hi := by simp
  have hhead : bstRank (0, 0 - 1) + bstRank (0 + 1, hi)
      = bstRank (0, hi) + 1 := by
    simp only [bstRank, if_neg (by omega : ¬(0 + 1 = 0))]
    omega
  have htail : ∀ x ∈ Finset.Icc 1 hi,
      bstRank (0, x - 1) + bstRank (x + 1, hi)
        = bstRank (0, hi) := by
    intro x hx
    rw [Finset.mem_Icc] at hx
    simp only [bstRank, if_neg (by omega : ¬(x + 1 = 0))]
    omega
  rw [hsplit, Finset.sum_insert h0, hhead, Finset.sum_congr rfl htail, Finset.sum_const,
    Nat.card_Icc, smul_eq_mul]
  have : hi + 1 - 1 = hi := by omega
  rw [this]
  ring

private theorem genWeightedBST_drift (p : Nat × Nat) :
    bstLevel (5 / 6) (fun q => (bstRank q : ℝ≥0∞)) p + 1 / 6
      ≤ (bstRank p : ℝ≥0∞) := by
  obtain ⟨lo, hi⟩ := p
  have hrank1 : (1 : ℝ≥0∞) ≤ (bstRank (lo, hi) : ℝ≥0∞) := by
    exact_mod_cast (show 1 ≤ bstRank (lo, hi) by simp only [bstRank]; omega)
  unfold bstLevel
  by_cases hgt : lo > hi
  · rw [if_pos hgt, zero_add]
    exact (ENNReal.div_le_of_le_mul (by norm_num)).trans hrank1
  · push Not at hgt
    rw [if_neg (by omega)]
    simp only
    by_cases hlo : lo = 0
    · subst hlo
      have hcast : (∑ x ∈ Finset.Icc 0 hi,
            ((bstRank (0, x - 1) : ℝ≥0∞) + (bstRank (x + 1, hi) : ℝ≥0∞)))
          = ((hi + 1 : ℕ) : ℝ≥0∞) * (bstRank (0, hi) : ℝ≥0∞) + 1 := by
        exact_mod_cast congrArg (Nat.cast (R := ℝ≥0∞)) (bstRank_sum_zero hi)
      have hne0 : ((hi + 1 : ℕ) : ℝ≥0∞) ≠ 0 := by positivity
      have h6 : (6 : ℝ≥0∞) ≤ (bstRank (0, hi) : ℝ≥0∞) := by
        exact_mod_cast (show 6 ≤ bstRank (0, hi) by
          simp only [bstRank, reduceIte]; omega)
      rw [Nat.sub_zero, hcast, ENNReal.add_div, mul_div_assoc,
        ENNReal.mul_div_cancel hne0 (ENNReal.natCast_ne_top _)]
      calc 5 / 6 * ((bstRank (0, hi) : ℝ≥0∞) + 1 / ((hi + 1 : ℕ) : ℝ≥0∞)) + 1 / 6
          ≤ 5 / 6 * ((bstRank (0, hi) : ℝ≥0∞) + 1) + 1 / 6 := by
            gcongr
            bound
        _ ≤ (bstRank (0, hi) : ℝ≥0∞) := by
            ennreal_to_real
            ennreal_to_real at h6
            linarith
    · have hcast : (∑ x ∈ Finset.Icc lo hi,
            ((bstRank (lo, x - 1) : ℝ≥0∞) + (bstRank (x + 1, hi) : ℝ≥0∞)))
          = ((hi - lo + 1 : ℕ) : ℝ≥0∞) * (bstRank (lo, hi) : ℝ≥0∞) := by
        exact_mod_cast congrArg (Nat.cast (R := ℝ≥0∞))
          (bstRank_sum_pos (by omega) hgt)
      have hne0 : ((hi - lo + 1 : ℕ) : ℝ≥0∞) ≠ 0 := by positivity
      rw [hcast, mul_div_assoc, ENNReal.mul_div_cancel hne0 (ENNReal.natCast_ne_top _)]
      ennreal_to_real
      ennreal_to_real at hrank1
      linarith

private theorem genWeightedBST_mass_ge (lo hi : Nat) (hle : lo ≤ hi) :
    (Tree.genWeightedBST lo hi : SPMF (Tree Nat)).mass
      ≥ 1 / 6 + 5 / 6 * ((∑ x ∈ Finset.Icc lo hi,
            (Tree.genWeightedBST lo (x - 1) : SPMF (Tree Nat)).mass
              * (Tree.genWeightedBST (x + 1) hi : SPMF (Tree Nat)).mass)
          / ((hi - lo + 1 : ℕ) : ℝ≥0∞)) := by
  conv_lhs => rw [Tree.genWeightedBST]
  rw [dif_neg (by omega)]
  rw [mass_frequency]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, mass_pure,
    Nat.cast_one, Nat.cast_ofNat, add_zero, mul_one]
  rw [show ((1 + 5 : ℕ) : ℝ≥0∞) = 6 by norm_num, ENNReal.add_div, ENNReal.mul_div_right_comm]
  gcongr
  refine mass_bind_choose_ge hle fun a => ?_
  refine mass_bind_ge_mul le_rfl fun l => ?_
  rw [mass_bind_pure]

private theorem genWeightedBST_step (p : Nat × Nat) :
    1 - (Tree.genWeightedBST p.1 p.2 : SPMF (Tree Nat)).mass
      ≤ bstLevel (5 / 6)
          (fun q => 1 - (Tree.genWeightedBST q.1 q.2 : SPMF (Tree Nat)).mass) p := by
  obtain ⟨lo, hi⟩ := p
  unfold bstLevel
  by_cases hgt : lo > hi
  · rw [if_pos hgt, Tree.genWeightedBST, dif_pos hgt]
    simp
  · push Not at hgt
    rw [if_neg (by omega)]
    simp only
    have hne0 : ((hi - lo + 1 : ℕ) : ℝ≥0∞) ≠ 0 := by positivity
    have hcard : ((hi - lo + 1 : ℕ) : ℝ≥0∞) ≤ ((Finset.Icc lo hi).card : ℝ≥0∞) := by
      rw [Nat.card_Icc]
      norm_cast
      omega
    calc 1 - (Tree.genWeightedBST lo hi : SPMF (Tree Nat)).mass
        ≤ 5 / 6 * (1 - (∑ x ∈ Finset.Icc lo hi,
              (Tree.genWeightedBST lo (x - 1) : SPMF (Tree Nat)).mass
                * (Tree.genWeightedBST (x + 1) hi : SPMF (Tree Nat)).mass)
            / ((hi - lo + 1 : ℕ) : ℝ≥0∞)) :=
          ENNReal.one_sub_le_mul_one_sub (by ennreal_to_real; norm_num)
            (by finiteness)
            (genWeightedBST_mass_ge lo hi hgt)
      _ ≤ 5 / 6 * ((∑ x ∈ Finset.Icc lo hi,
              (1 - (Tree.genWeightedBST lo (x - 1) : SPMF (Tree Nat)).mass
                * (Tree.genWeightedBST (x + 1) hi : SPMF (Tree Nat)).mass))
            / ((hi - lo + 1 : ℕ) : ℝ≥0∞)) := by
          gcongr 5 / 6 * ?_
          exact ENNReal.one_sub_sum_div_le hne0 (ENNReal.natCast_ne_top _) hcard
            fun x _ => mul_le_one' (mass_le_one _) (mass_le_one _)
      _ ≤ 5 / 6 * ((∑ x ∈ Finset.Icc lo hi,
              ((1 - (Tree.genWeightedBST lo (x - 1) : SPMF (Tree Nat)).mass)
                + (1 - (Tree.genWeightedBST (x + 1) hi : SPMF (Tree Nat)).mass)))
            / ((hi - lo + 1 : ℕ) : ℝ≥0∞)) := by
          gcongr with x hx
          exact ENNReal.one_sub_mul_le_add (mass_le_one _) (mass_le_one _)

theorem Tree.genWeightedBST.terminates : IsAlmostSurelyTerminating (Tree.genWeightedBST lo hi) := by
  refine SPMF.IsPMF_of_ranking
    (fun p : Nat × Nat => (Tree.genWeightedBST p.1 p.2 : SPMF (Tree Nat)))
    (levelOp_bstLevel (5 / 6))
    (fun p => (bstRank p : ℝ≥0∞))
    (fun p => ENNReal.natCast_ne_top _)
    (ε := 1 / 6) (ENNReal.div_pos one_ne_zero (by norm_num))
    genWeightedBST_drift genWeightedBST_step (lo, hi)

theorem Tree.genWeightedBST.cost_bounded :
    IsCostBounded (Tree.genWeightedBST lo hi) (fun t => 3 * t.size + 1) := by
  open Lean.Order in
  delta genWeightedBST
  apply (fix_induct (motive := fun (g : Nat → Nat → SPMF.Cost (Tree Nat)) =>
    ∀ lo hi, IsBounded (g lo hi) (fun t => 3 * t.size + 1)) _ ?admissible ?step)
  case admissible =>
    exact admissible_pi_apply _ fun _ => admissible_pi_apply _ fun _ => admissible_IsBounded _
  case step =>
    intro rec ih lo hi
    rw [IsBounded_iff]
    rintro ⟨t, n⟩ hmem
    rw [SPMF.mem_support_dite_iff] at hmem
    obtain ⟨_, hmem⟩ | ⟨_, hmem⟩ := hmem
    · cost_support_simp at hmem
      obtain ⟨rfl, rfl⟩ := hmem
      simp [Tree.size]
    · -- `Cost.mem_support_frequency` is an implication, not a simp lemma.
      obtain ⟨w, g, m, hbr, hw, hmem, rfl⟩ := SPMF.Cost.mem_support_frequency hmem
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hbr
      obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := hbr
      · cost_support_simp at hmem
        obtain ⟨rfl, rfl⟩ := hmem
        simp [Tree.size]
      · cost_support_simp at hmem
        obtain ⟨⟨⟨x, hxlo, hxhi⟩⟩, n1, n2, hn1, hmem, hm⟩ := hmem
        obtain ⟨l, n3, n4, hl, hmem, hn2⟩ := hmem
        obtain ⟨r, n5, n6, hr, ⟨rfl, hn6⟩, hn4⟩ := hmem
        have hL : n3 ≤ 3 * l.size + 1 := ih lo (x - 1) (l, n3) hl
        have hR : n5 ≤ 3 * r.size + 1 := ih (x + 1) hi (r, n5) hr
        simp only [Tree.size]
        omega

theorem Tree.genWeightedBST.sound_complete :
    IsSoundAndComplete (Tree.genWeightedBST lo hi) (Tree.isBST lo hi) := by
  intro t
  fun_induction Tree.isBST
    <;> rw [Tree.genWeightedBST]
    <;> split
    <;> simp
  · -- leaf, `lo ≤ hi`: witness the (weight-1) leaf branch of the `frequency`.
    exact ⟨1, fun _ => Pure.pure .leaf, Or.inl ⟨rfl, rfl⟩, one_pos, by simp⟩
  · -- node, `lo > hi`: no pivot fits.
    intros
    omega
  · -- node, `lo ≤ hi`: only the (weight-5) node branch can produce a `node`.
    constructor
    · rintro ⟨w, g, hbr, hw, hmem⟩
      rcases hbr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · simp at hmem
      · revert hmem
        simp
        grind
    · rintro ⟨h1, h2, hl, hr⟩
      refine ⟨5, _, Or.inr ⟨rfl, rfl⟩, by norm_num, ?_⟩
      simp
      grind

end BST
