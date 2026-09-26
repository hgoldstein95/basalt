/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt.IO.Ideal
import Basalt.Walk.Expect
import Basalt.Tactic.MassFixpoint

/-!
# Uniform Words Make a Uniform Choice

SplitMix's range reduction on uniform words is `SPMF`'s `choose` (`chooseVia_uniformWord`): the
step that carries the ideal law from one word to a whole draw (`IdealSource.below_choose`).
-/

open RandomChoice ENNReal

namespace SPMF

section uniform

private theorem sum_range_mul {M : Type*} [AddCommMonoid M] (A B : Nat) (f : Nat → M) :
    ∑ x ∈ Finset.range (A * B), f x
      = ∑ a ∈ Finset.range A, ∑ b ∈ Finset.range B, f (a * B + b) := by
  induction A with
  | zero => simp
  | succ A ih => rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]

private theorem mul_inv_mul_inv_natCast (x : ℝ≥0∞) (A B : Nat) :
    x * (B : ℝ≥0∞)⁻¹ * (A : ℝ≥0∞)⁻¹ = x * ((A * B : Nat) : ℝ≥0∞)⁻¹ := by
  rw [mul_assoc, Nat.cast_mul, ENNReal.mul_inv (by simp) (by simp), mul_comm (B : ℝ≥0∞)⁻¹]

/-- Two uniform draws are one on the product range. -/
theorem expect_chooseNat_mul {A B : Nat} (hA : 0 < A) (hB : 0 < B) (f : Nat → ℝ≥0∞) :
    expect (chooseNat 0 (A - 1)) (fun a => expect (chooseNat 0 (B - 1)) fun b => f (a * B + b))
      = expect (chooseNat 0 (A * B - 1)) f := by
  simp only [expect_chooseNat_zero hA, expect_chooseNat_zero hB,
    expect_chooseNat_zero (Nat.mul_pos hA hB), sum_range_mul, div_eq_mul_inv, ← Finset.sum_mul,
    mul_inv_mul_inv_natCast]

end uniform

section digits

private theorem toNat_toUInt64 {n : Nat} (h : n < 2 ^ 64) : n.toUInt64.toNat = n :=
  UInt64.toNat_ofNat_of_lt' h

/-- A uniform word masked to its low `k` bits is uniform on them. -/
theorem expect_uniformWord_mask {k : Nat} (hk : k ≤ 64) (f : Nat → ℝ≥0∞) :
    expect uniformWord (fun x => f (x &&& (2 ^ k - 1 : Nat).toUInt64).toNat)
      = expect (chooseNat 0 (2 ^ k - 1)) f := by
  have hk' : 2 ^ k - 1 < 2 ^ 64 := by
    have := Nat.pow_le_pow_right (show 0 < 2 by omega) hk
    have := Nat.one_le_two_pow (n := k)
    omega
  rw [expect_uniformWord, expect_chooseNat_zero (by positivity),
    expect_chooseNat_zero (by positivity)]
  have hmod : ∀ x ∈ Finset.range (2 ^ 64),
      ((fun x : UInt64 => f (x &&& (2 ^ k - 1 : Nat).toUInt64).toNat) ∘ Nat.toUInt64) x
        = f (x % 2 ^ k) := by
    intro x hx
    simp only [Function.comp_apply, UInt64.toNat_and, toNat_toUInt64 (Finset.mem_range.mp hx),
      toNat_toUInt64 hk', Nat.and_two_pow_sub_one_eq_mod]
  have hsplit : 2 ^ 64 = 2 ^ (64 - k) * 2 ^ k := by rw [← pow_add]; congr 1; omega
  rw [Finset.sum_congr rfl hmod, hsplit, sum_range_mul]
  have hb : ∀ a ∈ Finset.range (2 ^ (64 - k)),
      ∑ b ∈ Finset.range (2 ^ k), f ((a * 2 ^ k + b) % 2 ^ k) = ∑ b ∈ Finset.range (2 ^ k), f b :=
    fun a _ => Finset.sum_congr rfl fun b hb => by
      rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt (Finset.mem_range.mp hb)]
  rw [Finset.sum_congr rfl hb, Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_mul]
  exact ENNReal.mul_div_mul_left _ _ (by simp) (by simp)

private theorem expect_go (n acc : Nat) (f : Nat → ℝ≥0∞) :
    expect (drawDigitsVia.go uniformWord acc n) f
      = expect (chooseNat 0 (2 ^ (64 * n) - 1)) fun y => f (acc * 2 ^ (64 * n) + y) := by
  induction n generalizing acc with
  | zero => simp [drawDigitsVia.go, expect_chooseNat]
  | succ n ih =>
    rw [drawDigitsVia.go, expect_bind, expect_uniformWord]
    simp only [Function.comp_def, ih]
    rw [show 2 ^ (64 * (n + 1)) = 2 ^ 64 * 2 ^ (64 * n) by ring,
      ← expect_chooseNat_mul (by positivity) (by positivity), expect_chooseNat_zero (by positivity),
      expect_chooseNat_zero (by positivity)]
    have key : ∀ x ∈ Finset.range (2 ^ 64),
        (expect (chooseNat 0 (2 ^ (64 * n) - 1)) fun y =>
          f ((acc <<< 64 ||| x.toUInt64.toNat) * 2 ^ (64 * n) + y))
        = expect (chooseNat 0 (2 ^ (64 * n) - 1)) fun y =>
          f (acc * (2 ^ 64 * 2 ^ (64 * n)) + (x * 2 ^ (64 * n) + y)) := by
      intro x hx
      rw [toNat_toUInt64 (Finset.mem_range.mp hx),
        ← Nat.shiftLeft_add_eq_or_of_lt (Finset.mem_range.mp hx), Nat.shiftLeft_eq]
      exact congrArg _ (funext fun y => congrArg f (by ring))
    rw [Finset.sum_congr rfl key]

/-- The candidate `SplitMix.drawDigits` draws is uniform, on uniform words. -/
theorem expect_drawDigitsVia {k : Nat} (hk : k ≤ 64) (rest : Nat) (f : Nat → ℝ≥0∞) :
    expect (drawDigitsVia uniformWord (2 ^ k - 1 : Nat).toUInt64 rest) f
      = expect (chooseNat 0 (2 ^ k * 2 ^ (64 * rest) - 1)) f := by
  rw [drawDigitsVia, expect_bind]
  simp only [expect_go]
  rw [expect_uniformWord_mask hk (fun b => expect (chooseNat 0 (2 ^ (64 * rest) - 1)) fun y =>
    f (b * 2 ^ (64 * rest) + y)), expect_chooseNat_mul (by positivity) (by positivity)]

end digits

section rejection

variable {N R : Nat}

/-- `{x // x ≤ R}` as the `Fin` it is. -/
private def finEquivLe (R : Nat) : Fin (R + 1) ≃ {x // x ≤ R} where
  toFun i := ⟨i.val, Nat.lt_succ_iff.mp i.isLt⟩
  invFun x := ⟨x.val, Nat.lt_succ_of_le x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

local instance : Fintype {x // x ≤ R} := Fintype.ofEquiv _ (finEquivLe R)

private theorem card_le : Fintype.card {x // x ≤ R} = R + 1 :=
  (Fintype.card_congr (finEquivLe R).symm).trans (Fintype.card_fin _)

/-- A candidate below `N` is accepted at most `R` or rejected: the accepted ones, one each, and the
`N - (R + 1)` rejected ones, all alike. -/
private theorem sum_Icc_dite (hR : R < N) (f : {x // x ≤ R} → ℝ≥0∞) (c : ℝ≥0∞) :
    ∑ x ∈ Finset.Icc 0 (N - 1), (if h : x ≤ R then f ⟨x, h⟩ else c)
      = ∑ x : {x // x ≤ R}, f x + ((N - (R + 1) : Nat) : ℝ≥0∞) * c := by
  have : Finset.Icc 0 (N - 1) = Finset.range ((R + 1) + (N - (R + 1))) := by ext; simp; omega
  rw [this, Finset.sum_range_add]
  congr 1
  · rw [Finset.sum_subtype (p := (· ≤ R)) (F := inferInstance) (Finset.range (R + 1))
      (fun x => by simp)]
    exact Finset.sum_congr rfl fun x _ => dite_eq_left x.property
  · rw [Finset.sum_congr rfl fun y _ => dite_eq_right_iff.mpr fun h => absurd h (by omega),
      Finset.sum_const, Finset.card_range, nsmul_eq_mul]

theorem rejectVia_terminates (hR : R < N) :
    IsAlmostSurelyTerminating (rejectVia (chooseNat 0 (N - 1) : SPMF Nat) R) := by
  have hN : (N : ℝ≥0∞) ≠ 0 := by simp; omega
  mass_fixpoint using
    LfpIsOne.affine (m := ((N - (R + 1) : Nat) : ℝ≥0∞) * (N : ℝ≥0∞)⁻¹) (by
      rw [← div_eq_mul_inv]
      exact ENNReal.div_lt_of_lt_mul
        (by rw [one_mul]; exact_mod_cast (show N - (R + 1) < N by omega)))
  rw [sum_Icc_dite hR (fun _ => 1)]
  simp only [Finset.sum_const, Finset.card_univ, card_le, nsmul_eq_mul, mul_one,
    show N - 1 - 0 + 1 = N by omega]
  have hq : ((R + 1 : Nat) : ℝ≥0∞) * (N : ℝ≥0∞)⁻¹ + ((N - (R + 1) : Nat) : ℝ≥0∞) * (N : ℝ≥0∞)⁻¹
      = 1 := by
    rw [← add_mul, ← Nat.cast_add, show R + 1 + (N - (R + 1)) = N by omega,
      ENNReal.mul_inv_cancel hN (by simp)]
  rw [ENNReal.sub_eq_of_eq_add (by finiteness) hq.symm, div_eq_mul_inv, add_mul, mul_right_comm]

/-- Each value of the reduction has at most its uniform share. -/
theorem expect_rejectVia_le (hR : R < N) (a : {x // x ≤ R}) :
    expect (rejectVia (chooseNat 0 (N - 1) : SPMF Nat) R) (fun y => if y = a then 1 else 0)
      ≤ ((R + 1 : Nat) : ℝ≥0∞)⁻¹ := by
  rw [expect_eq_obs]
  walk fixpoint
  rw [sum_Icc_dite hR (fun x => if x = a then 1 else 0), Finset.sum_ite_eq']
  simp only [Finset.mem_univ, ite_true, show N - 1 - 0 + 1 = N by omega]
  have hR1 : ((R + 1 : Nat) : ℝ≥0∞) * ((R + 1 : Nat) : ℝ≥0∞)⁻¹ = 1 :=
    ENNReal.mul_inv_cancel (by simp) (by simp)
  rw [← hR1, ← add_mul, ← Nat.cast_add, show R + 1 + (N - (R + 1)) = N by omega,
    mul_comm, mul_div_assoc, ENNReal.div_self (by simp; omega) (by simp), mul_one]

/-- The reduction is exactly uniform: no value exceeds its share, and the shares are all the mass
there is. -/
theorem rejectVia_apply (hR : R < N) (a : {x // x ≤ R}) :
    rejectVia (chooseNat 0 (N - 1) : SPMF Nat) R a = ((R + 1 : Nat) : ℝ≥0∞)⁻¹ := by
  set z := rejectVia (chooseNat 0 (N - 1) : SPMF Nat) R
  have hle : ∀ b, z b ≤ ((R + 1 : Nat) : ℝ≥0∞)⁻¹ := fun b =>
    (expect_ite_eq z b).symm.trans_le (expect_rejectVia_le hR b)
  have hshares : ∑' (_ : {x // x ≤ R}), ((R + 1 : Nat) : ℝ≥0∞)⁻¹ = 1 := by
    rw [tsum_fintype, Finset.sum_const, Finset.card_univ, card_le, nsmul_eq_mul,
      ENNReal.mul_inv_cancel (by simp) (by simp)]
  refine (hle a).antisymm (not_lt.mp fun hlt => ?_)
  have hmass : ∑' b, z b = 1 := rejectVia_terminates hR
  have := ENNReal.tsum_lt_tsum (by rw [hmass]; simp) hle hlt
  rw [hmass, hshares] at this
  exact lt_irrefl _ this

end rejection

section shape

variable (R : Nat)

/-- The width of the leading digit `SplitMix.rangeShape` masks to. -/
private def topBits : Nat := (R >>> (64 * (R.log2 / 64))).log2 + 1

private theorem topBits_le : topBits R ≤ 64 := by
  unfold topBits
  by_cases h0 : R >>> (64 * (R.log2 / 64)) = 0
  · rw [h0, Nat.log2_zero]; omega
  have hR : R ≠ 0 := by rintro rfl; simp at h0
  have := (Nat.log2_lt hR).mp (show R.log2 < 64 + 64 * (R.log2 / 64) by omega)
  have : R >>> (64 * (R.log2 / 64)) < 2 ^ 64 := by
    rwa [Nat.shiftRight_eq_div_pow, Nat.div_lt_iff_lt_mul (by positivity), ← pow_add]
  have := (Nat.log2_lt h0).mpr this
  omega

private theorem lt_candidates : R < 2 ^ topBits R * 2 ^ (64 * (R.log2 / 64)) := by
  unfold topBits
  rw [Nat.shiftRight_eq_div_pow, ← Nat.div_lt_iff_lt_mul (by positivity)]
  exact Nat.lt_log2_self

end shape

/-- SplitMix's range reduction, on uniform words, is `SPMF`'s `choose`. -/
theorem chooseVia_uniformWord (lo hi : Nat) (h : lo ≤ hi) :
    chooseVia uniformWord lo hi h = (choose lo hi h : SPMF _) := by
  ext m
  rw [choose_apply]
  unfold chooseVia
  split
  · rename_i hlt
    have hD : drawDigitsVia uniformWord (SplitMix.rangeShape (hi - lo)).1
          (SplitMix.rangeShape (hi - lo)).2
        = chooseNat 0 (2 ^ topBits (hi - lo) * 2 ^ (64 * ((hi - lo).log2 / 64)) - 1) :=
      ext_expect (expect_drawDigitsVia (topBits_le _) _)
    simp only [hD, ← bind_pure_comp, bind_apply, pure_apply]
    have hi₀ : m.down.val - lo ≤ hi - lo := by have := m.down.property; omega
    rw [tsum_eq_single ⟨m.down.val - lo, hi₀⟩ fun i hi => ?_]
    · have hm : m = ULift.up ⟨lo + (m.down.val - lo), by omega, by omega⟩ := by
        ext; simp; have := m.down.property; omega
      rw [rejectVia_apply (lt_candidates _)]
      split
      · rw [mul_one, one_div]
      · exact absurd hm ‹_›
    · split
      · rename_i hm
        have := congrArg (fun u => u.down.val) hm
        simp only at this
        exact absurd (Subtype.ext (show i.val = m.down.val - lo by omega)) hi
      · rw [mul_zero]
  · rename_i hlt
    have hm : m = ULift.up ⟨lo, Nat.le_refl lo, h⟩ := by
      ext; have := m.down.property; simp; omega
    simp [hm, show hi - lo + 1 = 1 by omega]

end SPMF

namespace IdealSource

open SPMF

variable {σ : Type} [WordSource σ] (src : IdealSource σ)

private theorem below_go {word' : SPMF UInt64} {word : WordModel σ UInt64}
    (hw : src.Below word' word) (acc n : Nat) :
    src.Below (drawDigitsVia.go word' acc n) (drawDigitsVia.go word acc n) := by
  induction n generalizing acc with
  | zero => exact src.below_pure acc
  | succ n ih => exact src.below_bind (fun x => ih _) hw

theorem below_rejectVia {cand' : SPMF Nat} {cand : WordModel σ Nat} (hc : src.Below cand' cand)
    (range : Nat) : src.Below (rejectVia cand' range) (rejectVia cand range) := by
  refine rejectVia.fixpoint_induct (m := SPMF) cand' range
    (fun y => src.Below y (rejectVia cand range)) (Below.admissible src _) (fun z ih => ?_)
  rw [rejectVia]
  exact src.below_bind (fun _ => src.below_dite (fun h => src.below_pure _) fun _ => ih) hc

/-- The ideal law for one word is the ideal law for a choice. -/
@[gen_rule]
theorem below_choose (lo hi : Nat) (h : lo ≤ hi) :
    src.Below (RandomChoice.choose lo hi h) (RandomChoice.choose lo hi h) := by
  rw [show (RandomChoice.choose lo hi h : SPMF _) = chooseVia uniformWord lo hi h from
    (chooseVia_uniformWord lo hi h).symm]
  show src.Below (chooseVia uniformWord lo hi h)
    (chooseVia (fun s => some (WordSource.next s)) lo hi h)
  unfold chooseVia drawDigitsVia
  exact src.below_ite (fun _ => src.below_map _ (src.below_rejectVia
    (src.below_bind (fun _ => src.below_go src.below_word _ _) src.below_word) _))
    fun _ => src.below_pure _

end IdealSource
