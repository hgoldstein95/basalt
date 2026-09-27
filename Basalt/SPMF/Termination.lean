/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt.SPMF.Mass
import Basalt.Tactic.ENNReal

/-!
# Almost-Sure Termination

Tools for proving almost-sure termination of Basalt generators.
-/

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
theorem LfpIsOne.affine {m : ℝ≥0∞} (hm : m < 1) : LfpIsOne fun c => (1 - m) + m * c := by
  intro c hle hge
  have hm_top : m ≠ ⊤ := (hm.trans one_lt_top).ne
  have hdef : 1 - c ≤ m * (1 - c) :=
    calc 1 - c
        ≤ 1 - ((1 - m) + m * c) := tsub_le_tsub_left hge 1
      _ = (1 - (1 - m)) - m * c := by rw [tsub_add_eq_tsub_tsub]
      _ = m - m * c := by rw [ENNReal.sub_sub_cancel one_ne_top hm.le]
      _ = m * (1 - c) := by rw [ENNReal.mul_sub fun _ _ => hm_top, mul_one]
  by_contra hne
  have hpos : 0 < 1 - c :=
    pos_iff_ne_zero.mpr fun h0 => hne (le_antisymm hle (tsub_eq_zero_iff_le.mp h0))
  have htop : (1 : ℝ≥0∞) - c ≠ ⊤ := (tsub_le_self.trans_lt one_lt_top).ne
  have hlt : (1 : ℝ≥0∞) - c < 1 - c :=
    calc 1 - c ≤ m * (1 - c) := hdef
      _ = (1 - c) * m := mul_comm _ _
      _ < (1 - c) * 1 := ENNReal.mul_lt_mul_right hpos.ne' htop hm
      _ = 1 - c := mul_one _
  exact lt_irrefl _ hlt

/-- **At most two recursive calls**, with probabilities `a`, `b`, `d` of zero, one, and two: mean
offspring `b + 2d ≤ 1`, so this covers the critical case, provided a step can stop (`0 < a`). -/
theorem LfpIsOne.quadratic {a b d : ℝ≥0∞} (habd : a + b + d = 1) (hbd : b + 2 * d ≤ 1)
    (ha : 0 < a) : LfpIsOne fun c => a + b * c + d * c ^ 2 := by
  intro c hle hge
  have ha1 : a ≤ 1 := habd ▸ le_self_add.trans le_self_add
  have hb1 : b ≤ 1 := habd ▸ le_add_self.trans le_self_add
  have hd1 : d ≤ 1 := habd ▸ le_add_self
  have ha0 : 0 < a.toReal := ENNReal.toReal_pos ha.ne' (by finiteness)
  have hb0 := b.toReal_nonneg
  have hd0 := d.toReal_nonneg
  have hc0 := c.toReal_nonneg
  simp only at hge
  ennreal_to_real at hge
  ennreal_to_real at habd
  ennreal_to_real at hbd
  ennreal_to_real at hle
  rw [← ENNReal.toReal_eq_one_iff]
  refine le_antisymm hle (not_lt.mp fun hlt => ?_)
  have hb : b.toReal = 1 - a.toReal - d.toReal := by linarith
  rw [hb] at hge
  -- `a + bc + dc² - c = a(1-c)² + c(1-c)(a-d)`, and `a ≥ d`
  nlinarith [mul_pos (mul_pos ha0 (sub_pos.mpr hlt)) (sub_pos.mpr hlt),
    mul_nonneg (mul_nonneg hc0 (sub_nonneg.mpr hle)) (show 0 ≤ a.toReal - d.toReal by linarith)]

end certificates

end SPMF
