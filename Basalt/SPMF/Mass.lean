/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt.SPMF.Support
import Basalt.ENNRealAuto

open Lean.Order RandomChoice NNReal ENNReal MeasureTheory

/-!
# SPMF Mass

`SPMF.mass` (the total probability assigned to values, as opposed to divergence — always ≤ 1),
its equations for each combinator, and `SPMF.IsPMF` (mass exactly 1).
-/

namespace SPMF

section mass

/-- The total mass of an SPMF. Always ≤ 1 by definition. -/
noncomputable def mass (p : SPMF α) : ℝ≥0∞ := ∑' a, p a

theorem mass_le_one (p : SPMF α) : p.mass ≤ 1 := p.tsum_coe

@[simp]
theorem mass_pick {x y : SPMF α} :
    (pick (fun () => x) (fun () => y)).mass = (1/2 : ℝ≥0∞) * x.mass + (1/2 : ℝ≥0∞) * y.mass := tsum_pick

@[simp]
theorem mass_bot : Bot.bot (α := SPMF α).mass = 0 := by
  simp only [mass, ENNReal.tsum_eq_zero]
  solve_by_elim

@[simp]
theorem mass_pure (a : α) : (Pure.pure a : SPMF α).mass = 1 := by
  unfold mass
  simp only [Pure.pure, pure, DFunLike.coe]
  rw [tsum_eq_single a]
  · simp
  · intro a' ha'
    simp [ha']

@[simp]
theorem mass_bind_tsum {x : SPMF α} {f : α → SPMF β} :
    (x >>= f).mass = ∑' a, x a * (f a).mass := by
  unfold SPMF.mass
  simp only [Bind.bind, SPMF.bind, DFunLike.coe]
  rw [ENNReal.tsum_comm]
  simp_rw [ENNReal.tsum_mul_left]

@[simp]
theorem mass_choose (lo hi : Nat) (h : lo ≤ hi) :
    (choose lo hi h : SPMF (ULift {x : Nat // lo ≤ x ∧ x ≤ hi})).mass = 1 := by
  unfold mass
  let n : ℕ := hi - lo + 1
  have hn : n ≠ 0 := Nat.add_one_ne_zero _
  calc ∑' a, (choose lo hi h : SPMF (ULift {x : Nat // lo ≤ x ∧ x ≤ hi})) a
    _ = ∑' (_ : ULift {x : Nat // lo ≤ x ∧ x ≤ hi}), (1 / (n : ℝ≥0∞)) := rfl
    _ = (Finset.Icc lo hi).card * (1 / (n : ℝ≥0∞)) := tsum_subtype_Icc_const lo hi _
    _ = (n : ℝ≥0∞) * (1 / (n : ℝ≥0∞)) := by rw [card_Icc_eq lo hi h]
    _ = 1 := ENNReal.mul_div_cancel (Nat.cast_ne_zero.mpr hn) (ENNReal.natCast_ne_top n)

@[simp]
theorem mass_bind_pure {x : SPMF α} {f : α → β} :
    (x >>= fun a => Pure.pure (f a)).mass = x.mass := by
  classical
  unfold mass
  simp only [Bind.bind, bind, Pure.pure, pure, DFunLike.coe]
  rw [ENNReal.tsum_comm]
  congr 1
  ext a
  rw [tsum_eq_single (f a)]
  · simp
  · intro b hb
    simp only [mul_ite, mul_one, mul_zero]
    split_ifs with heq
    · simp_all
    · rfl

@[simp]
theorem mass_map {x : SPMF α} {f : α → β} :
    (f <$> x).mass = x.mass := by
  rw [map_eq_pure_bind]
  exact mass_bind_pure

@[simp]
theorem mass_chooseNat (lo hi : Nat) (h : lo ≤ hi) :
    (chooseNat lo hi h : SPMF Nat).mass = 1 := by
  unfold chooseNat
  rw [mass_map]
  exact mass_choose lo hi h

@[simp]
theorem mass_chooseInt (lo hi : Int) (h : lo ≤ hi) :
    (chooseInt lo hi h : SPMF Int).mass = 1 := by
  unfold chooseInt
  rw [mass_bind_pure]
  exact mass_chooseNat _ _ _

theorem mass_bind_ge_mul {x : SPMF α} {f : α → SPMF β} {c d : ℝ≥0∞}
    (hx : x.mass ≥ c) (hf : ∀ a, (f a).mass ≥ d) : (x >>= f).mass ≥ c * d := by
  have h : (x >>= f).mass ≥ x.mass * d := by
    simp only [mass, Bind.bind, bind, DFunLike.coe]
    rw [ENNReal.tsum_comm]
    simp [ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_right]
    gcongr with a; exact hf a
  calc (x >>= f).mass ≥ x.mass * d := h
    _ ≥ c * d := by gcongr

/-- A `tsum` over `α` commutes with a weighted `List.sum`. -/
private theorem tsum_map_weighted (gs : List (Nat × (Unit → SPMF α))) :
    ∑' a, (gs.map fun p => (p.1 : ℝ≥0∞) * (p.2 ()) a).sum
      = (gs.map fun p => (p.1 : ℝ≥0∞) * (p.2 ()).mass).sum := by
  induction gs with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, ih]
    rfl

/-- A `tsum` over `α` commutes with an unweighted `List.sum`. -/
private theorem tsum_map_mass (gs : List (Unit → SPMF α)) :
    ∑' a, (gs.map fun p => (p ()) a).sum
      = (gs.map fun p => (p ()).mass).sum := by
  induction gs with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ENNReal.tsum_add, ih]
    rfl

/-- The mass of a uniform choice is the average of the branch masses. -/
@[simp]
theorem mass_oneOf
    {gs : List (Unit → SPMF α)} {h : gs ≠ []} :
    (oneOf gs h : SPMF α).mass
      = (gs.map (fun p => (p ()).mass)).sum / (gs.length : ℝ≥0∞) := by
  have hm : (oneOf gs h : SPMF α).mass = ∑' a, oneOf gs h a := rfl
  rw [hm]
  simp only [oneOf_apply, div_eq_mul_inv]
  rw [ENNReal.tsum_mul_right, tsum_map_mass]

/-- The mass of a weighted choice is the weighted average of the branch masses. -/
@[simp]
theorem mass_frequency
    {gs : List (Nat × (Unit → SPMF α))} (h : 0 < (gs.map Prod.fst).sum) :
    (frequency gs h : SPMF α).mass
      = (gs.map fun p => (p.1 : ℝ≥0∞) * (p.2 ()).mass).sum / ((gs.map Prod.fst).sum : ℝ≥0∞) := by
  have hm : (frequency gs h : SPMF α).mass = ∑' a, frequency gs h a := rfl
  rw [hm]
  simp only [frequency_apply, div_eq_mul_inv]
  rw [ENNReal.tsum_mul_right, tsum_map_weighted]

end mass

section is_pmf

/-- An SPMF is a PMF if the mass sums to exactly 1.

This means that the probability of non-termination is vanishingly small, and therefore that the
generator almost-surely terminates. -/
def IsPMF (p : SPMF α) : Prop := p.mass = 1

/-- The lower half is the only half a termination proof has to supply: it is the form `mass_bound`
proves, for an `SPMF` term that is not a generator definition. -/
theorem IsPMF.of_one_le {p : SPMF α} (h : 1 ≤ p.mass) : IsPMF p :=
  le_antisymm (mass_le_one p) h

end is_pmf

end SPMF
