/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
module

public meta import Mathlib.Tactic.Basify
public import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Tactic.Linarith
public import Basalt.SPMF.Mass

/-!
# Almost-Sure Termination

Tools for proving almost-sure termination of Basalt generators.
-/

@[expose] public section

open ENNReal RandomChoice

namespace SPMF

section criterion

variable {β ι α : Type*}

/-- `T` has no sub-fixed point at or below `1` other than `1` itself. For a monotone `T` that maps
`[0, 1]` into itself this is `OrderHom.lfp T = 1`, the least fixed point being the infimum of the
sub-fixed points; a generator's mass is the least fixed point of its one-step mass equation. -/
def LfpIsOne [Preorder β] [One β] (T : β → β) : Prop :=
  ∀ c ≤ 1, T c ≤ c → c = 1

/-- **The termination criterion.** If one unfolding of the family `g` bounds its masses below by
`T c` whenever `c` bounds them below, and `T` has least fixed point `1`, every member has mass
`1`. -/
theorem mass_eq_one_of_lfpIsOne (g : ι → SPMF α) {T : (ι → ℝ≥0∞) → (ι → ℝ≥0∞)}
    (hT : LfpIsOne T) (hstep : ∀ c ≤ 1, (∀ j, c j ≤ (g j).mass) → ∀ i, T c i ≤ (g i).mass) :
    ∀ i, (g i).mass = 1 := by
  have hle : (fun j => (g j).mass) ≤ 1 := fun j => mass_le_one _
  exact congrFun (hT _ hle fun i => hstep _ hle (fun _ => le_rfl) i)

/-- A certificate for one bound on the whole family serves the family: `F` sees its infimum. -/
theorem LfpIsOne.iInf [Nonempty ι] {F : ℝ≥0∞ → ℝ≥0∞} (hF : LfpIsOne F) :
    LfpIsOne fun (c : ι → ℝ≥0∞) (_ : ι) => F (⨅ j, c j) := by
  intro c hc hTc
  have hinf := hF _ ((iInf_le _ (Classical.arbitrary ι)).trans (hc _)) (le_iInf fun i => hTc i)
  funext i
  exact le_antisymm (hc i) (hinf.symm.le.trans (iInf_le _ i))

/-- The criterion with one bound `c` for every member of the family. -/
theorem mass_eq_one_of_lfpIsOne_uniform (g : ι → SPMF α) {F : ℝ≥0∞ → ℝ≥0∞} (hF : LfpIsOne F)
    (hstep : ∀ c ≤ 1, (∀ j, c ≤ (g j).mass) → ∀ i, F c ≤ (g i).mass) :
    ∀ i, (g i).mass = 1 := by
  intro i
  have : Nonempty ι := ⟨i⟩
  refine mass_eq_one_of_lfpIsOne g hF.iInf (fun c hc hrec k => hstep _ ?_ ?_ k) i
  · exact (iInf_le _ i).trans (hc i)
  · exact fun j => (iInf_le _ j).trans (hrec j)

/-- Raising `T` keeps its least fixed point at `1`. -/
theorem LfpIsOne.mono [Preorder β] [One β] {T U : β → β} (hT : LfpIsOne T)
    (h : ∀ c ≤ 1, T c ≤ U c) : LfpIsOne U :=
  fun c hc hU => hT c hc ((h c hc).trans hU)

end criterion

section certificates

/-- A generator with no recursive occurrence. -/
theorem LfpIsOne.one : LfpIsOne fun _ : ℝ≥0∞ => (1 : ℝ≥0∞) :=
  fun _ hc h1 => le_antisymm hc h1

/-- **Subcritical**: the non-recursive branches carry probability `1 - m`, with `m < 1` the mean
number of recursive calls. -/
theorem LfpIsOne.affine {m : ℝ≥0∞} (hm : m < 1 := by norm_num) :
    LfpIsOne fun c => (1 - m) + m * c := by
  intro c hle hge
  simp only at hge
  basify
  rw [max_eq_left (by linarith)] at hge
  nlinarith

/-- Bernoulli's inequality, as one branch's slack in `LfpIsOne.poly`. -/
private theorem pow_sub_self_ge {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (i : ℕ) :
    (1 - i) * (x * (1 - x)) ≤ x ^ i - x := by
  rcases i with _ | k
  · simp only [Nat.cast_zero, sub_zero, one_mul, pow_zero]; nlinarith
  · have h := one_add_mul_le_pow (show (-2 : ℝ) ≤ x - 1 by linarith) k
    rw [add_sub_cancel] at h
    push_cast
    rw [pow_succ]
    nlinarith [mul_le_mul_of_nonneg_left h hx0]

private theorem lfpIsOne_poly_succ {n : ℕ} (a : Fin (n + 1) → ℝ≥0∞) (hsum : ∑ i, a i = 1)
    (hmean : ∑ i, (i.val : ℝ≥0∞) * a i ≤ 1) (ha : 0 < a 0) :
    LfpIsOne fun c => ∑ i, a i * c ^ (i : ℕ) := by
  intro c hc hle
  refine le_antisymm hc (not_lt.mp fun hlt => ?_)
  simp only at hle
  have hfin : ∀ i, a i ≠ ⊤ := fun i => ne_top_of_le_ne_top one_ne_top
    (hsum ▸ Finset.single_le_sum (fun j _ => zero_le) (Finset.mem_univ i))
  have hct : c ≠ ⊤ := ne_top_of_le_ne_top one_ne_top hc
  have hsumR : ∑ i, (a i).toReal = 1 := by
    rw [← ENNReal.toReal_sum fun i _ => hfin i, hsum, toReal_one]
  have hmeanR : ∑ i, (i.val : ℝ) * (a i).toReal ≤ 1 := by
    have h := (ENNReal.toReal_le_toReal (ne_top_of_le_ne_top one_ne_top hmean) one_ne_top).2 hmean
    simpa [ENNReal.toReal_sum fun i _ => mul_ne_top (natCast_ne_top _) (hfin i), toReal_mul]
      using h
  have hleR : ∑ i, (a i).toReal * c.toReal ^ (i : ℕ) ≤ c.toReal := by
    have h := (ENNReal.toReal_le_toReal (ne_top_of_le_ne_top hct hle) hct).2 hle
    simpa [ENNReal.toReal_sum fun i _ => mul_ne_top (hfin i) (pow_ne_top hct), toReal_mul,
      toReal_pow] using h
  have ha0 : 0 < (a 0).toReal := ENNReal.toReal_pos ha.ne' (hfin 0)
  have hx1 : c.toReal < 1 := by
    simpa using (ENNReal.toReal_lt_toReal hct one_ne_top).2 hlt
  have hx0 : 0 ≤ c.toReal := toReal_nonneg
  generalize c.toReal = x at *
  -- Branchwise Bernoulli, with the stopping branch's slack `a₀ (1 - x)²` kept.
  have hbranch :
      ∑ i, (a i).toReal * ((1 - (i.val : ℝ)) * (x * (1 - x))) + (a 0).toReal * (1 - x) ^ 2
        ≤ ∑ i, (a i).toReal * (x ^ (i : ℕ) - x) := by
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ (fun i => (a i).toReal * (x ^ (i : ℕ) - x))]
    have htail := Finset.sum_le_sum fun (j : Fin n) (_ : j ∈ Finset.univ) =>
      mul_le_mul_of_nonneg_left (pow_sub_self_ge hx0 hx1.le (j.succ : ℕ)) toReal_nonneg
        (a := (a j.succ).toReal)
    simp only [Fin.val_zero, Fin.val_succ, Nat.cast_zero, pow_zero] at htail ⊢
    nlinarith
  have hlhs : ∑ i, (a i).toReal * ((1 - (i.val : ℝ)) * (x * (1 - x)))
      = (∑ i, (a i).toReal - ∑ i, (i.val : ℝ) * (a i).toReal) * (x * (1 - x)) := by
    rw [← Finset.sum_sub_distrib, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hrhs : ∑ i, (a i).toReal * (x ^ (i : ℕ) - x)
      = ∑ i, (a i).toReal * x ^ (i : ℕ) - (∑ i, (a i).toReal) * x := by
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hlhs, hrhs, hsumR] at hbranch
  nlinarith [mul_nonneg (mul_nonneg hx0 (sub_nonneg.2 hx1.le)) (sub_nonneg.2 hmeanR),
    mul_pos ha0 (pow_pos (sub_pos.2 hx1) 2)]

/-- **At most `n - 1` recursive calls**, with `a i` the probability of `i` of them: mean offspring
`∑ i * a i ≤ 1`, critical case included, provided a step can stop (`0 < a 0`). -/
theorem LfpIsOne.poly {n : ℕ} [NeZero n] (a : Fin n → ℝ≥0∞)
    (hsum : ∑ i, a i = 1 := by simp [Fin.sum_univ_succ] <;> basify <;> norm_num)
    (hmean : ∑ i, (i.val : ℝ≥0∞) * a i ≤ 1 := by simp [Fin.sum_univ_succ] <;> basify <;> norm_num)
    (ha : 0 < a 0 := by norm_num) :
    LfpIsOne fun c => ∑ i, a i * c ^ (i : ℕ) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  exact lfpIsOne_poly_succ a hsum hmean ha

end certificates

end SPMF
