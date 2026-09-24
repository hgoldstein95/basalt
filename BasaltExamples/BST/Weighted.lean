/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt
import BasaltExamples.BST

/-!
# Weighted Binary Search Trees

`Tree.genWeightedBST` is a `frequency`-weighted, `@[tunable]` variant of `genBST`
(`BasaltExamples/BST`) that makes `node` five times as likely as `leaf`. It produces the same trees
with the same cost bound; only the distribution differs.

Unlike `genBST`, this weighting is *supercritical* under the crude branching bound (`node` has
probability `5/6`, so mean offspring is `5/6 · 2 = 5/3 > 1`), so no `LfpIsOne.quadratic` certificate
applies. Termination instead goes through a ranking function on the seed `(lo, hi)`, exploiting the
fact that the interval genuinely shrinks. The machinery (`bstLevel`, `bstRank`) lives here since it
is used nowhere else, instantiated at recursion weight `w = 5/6` and drift `ε = 1/6`.
-/

open RandomChoice
open SPMF
open scoped NNReal ENNReal

namespace BST

/-- Like `genBST` but `frequency`-weighted so `node` is five times as likely as `leaf`, and
`@[tunable]` so the weights are runtime-addressable (see `BasaltTest/Tuning.lean`). -/
@[tunable]
def Tree.genWeightedBST [Gen G] (lo hi : Int) : G (Tree Int) := do
  if h : lo > hi then
    return leaf
  else
    frequency! [
      (1, fun _ => pure leaf),
      (5, fun _ => do
        let x ← chooseInt lo hi (by omega)
        let l ← Tree.genWeightedBST lo (x - 1)
        let r ← Tree.genWeightedBST (x + 1) hi
        return node l x r)
    ] (by simp)
partial_fixpoint

/-- The level operator: recurse with probability `w` on the two subintervals of a uniform pivot. -/
private noncomputable def bstLevel (w : ℝ≥0∞) (e : Int × Int → ℝ≥0∞) (p : Int × Int) : ℝ≥0∞ :=
  if p.1 > p.2 then 0
  else w * ((∑ x ∈ Finset.Icc p.1 p.2, (e (p.1, x - 1) + e (x + 1, p.2)))
    / (((p.2 - p.1 + 1).toNat : ℕ) : ℝ≥0∞))

/-- The ranking function: the number of keys the interval still admits, plus one to keep it `≥ 1`
  on the empty interval. -/
private def bstRank (p : Int × Int) : Nat :=
  (p.2 + 1 - p.1).toNat + 1

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

/-- The children's total rank equals the parent's rank *exactly, for every pivot* — the interval
  partitions, and with integer bounds it does so at every `lo`. Summed over the pivots: -/
private lemma bstRank_sum {lo hi : Int} (hle : lo ≤ hi) :
    ∑ x ∈ Finset.Icc lo hi, (bstRank (lo, x - 1) + bstRank (x + 1, hi))
      = ((hi - lo + 1).toNat) * bstRank (lo, hi) := by
  have hterm : ∀ x ∈ Finset.Icc lo hi,
      bstRank (lo, x - 1) + bstRank (x + 1, hi) = bstRank (lo, hi) := by
    intro x hx
    rw [Finset.mem_Icc] at hx
    simp only [bstRank]
    omega
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, Int.card_Icc, smul_eq_mul]
  congr 1
  omega

private theorem genWeightedBST_drift (p : Int × Int) :
    bstLevel (5 / 6) (fun q => (bstRank q : ℝ≥0∞)) p + 1 / 6
      ≤ (bstRank p : ℝ≥0∞) := by
  obtain ⟨lo, hi⟩ := p
  have hrank1 : (1 : ℝ≥0∞) ≤ (bstRank (lo, hi) : ℝ≥0∞) := by
    exact_mod_cast (show 1 ≤ bstRank (lo, hi) by simp only [bstRank]; omega)
  unfold bstLevel
  by_cases hgt : lo > hi
  · rw [ite_eq_left hgt, zero_add]
    exact (ENNReal.div_le_of_le_mul (by norm_num)).trans hrank1
  · push Not at hgt
    rw [ite_eq_right (by omega)]
    simp only
    have hcast : (∑ x ∈ Finset.Icc lo hi,
          ((bstRank (lo, x - 1) : ℝ≥0∞) + (bstRank (x + 1, hi) : ℝ≥0∞)))
        = (((hi - lo + 1).toNat : ℕ) : ℝ≥0∞) * (bstRank (lo, hi) : ℝ≥0∞) := by
      exact_mod_cast congrArg (Nat.cast (R := ℝ≥0∞)) (bstRank_sum hgt)
    have hne0 : (((hi - lo + 1).toNat : ℕ) : ℝ≥0∞) ≠ 0 := by
      simp only [ne_eq, Nat.cast_eq_zero]
      omega
    rw [hcast, mul_div_assoc, ENNReal.mul_div_cancel hne0 (ENNReal.natCast_ne_top _)]
    ennreal_to_real
    ennreal_to_real at hrank1
    linarith

theorem Tree.genWeightedBST.terminates : IsAlmostSurelyTerminating (Tree.genWeightedBST lo hi) := by
  mass_fixpoint per_seed
  refine LfpIsOne.ranking (levelOp_bstLevel (5 / 6)) (fun p => (bstRank p : ℝ≥0∞))
    (fun p => ENNReal.natCast_ne_top _) (ε := 1 / 6) (by norm_num) genWeightedBST_drift ?_
  rintro c hc ⟨lo, hi⟩
  simp only [bstLevel, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.cast_one,
    Nat.cast_ofNat, mul_one, add_zero]
  split_ifs with hgt
  · simp
  have hne0 : (((hi - lo + 1).toNat : ℕ) : ℝ≥0∞) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]
    omega
  have hcard : (((hi - lo + 1).toNat : ℕ) : ℝ≥0∞) ≤ ((Finset.Icc lo hi).card : ℝ≥0∞) := by
    rw [Int.card_Icc]
    norm_cast
    omega
  -- Split off the leaf branch, then the union bound over the pivot and over the two children.
  calc _ ≤ 5 / 6 * (1 - (∑ x ∈ Finset.Icc lo hi, c (lo, x - 1) * c (x + 1, hi))
          / (((hi - lo + 1).toNat : ℕ) : ℝ≥0∞)) :=
        ENNReal.one_sub_le_mul_one_sub (w := 1 / 6) (by ennreal_to_real; norm_num) (by finiteness)
          (by rw [show ((1 + 5 : ℕ) : ℝ≥0∞) = 6 by norm_num, ENNReal.add_div,
            ENNReal.mul_div_right_comm])
    _ ≤ 5 / 6 * ((∑ x ∈ Finset.Icc lo hi, (1 - c (lo, x - 1) * c (x + 1, hi)))
          / (((hi - lo + 1).toNat : ℕ) : ℝ≥0∞)) := by
        gcongr 5 / 6 * ?_
        exact ENNReal.one_sub_sum_div_le hne0 (ENNReal.natCast_ne_top _) hcard
          fun x _ => mul_le_one' (hc _) (hc _)
    _ ≤ _ := by
        gcongr with x
        exact ENNReal.one_sub_mul_le_add (hc _) (hc _)

theorem Tree.genWeightedBST.cost_bounded :
    IsCostBounded (Tree.genWeightedBST lo hi) (fun t => 3 * t.size + 1) := by
  cost_fixpoint
  all_goals simp only [Tree.size]; omega

theorem Tree.genWeightedBST.sound_complete :
    IsSoundAndComplete (Tree.genWeightedBST lo hi) (Tree.isBST lo hi) := by
  refine .intro ?sound ?complete
  case sound =>
    sound_fixpoint
    all_goals simp_all [Tree.isBST]
  case complete =>
    intro t
    induction t generalizing lo hi with
    | leaf => intro _; rw [Tree.genWeightedBST]; complete_bound
    | node l x r ihl ihr =>
      intro ⟨h1, h2, hl, hr⟩
      rw [Tree.genWeightedBST]; complete_bound
      rw [dite_eq_right (by omega)]
      exact ⟨x, ⟨h1, h2⟩, l, ihl hl, r, ihr hr, rfl⟩

end BST
