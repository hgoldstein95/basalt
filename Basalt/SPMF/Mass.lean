/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt.SPMF.Support

open Lean.Order RandomChoice NNReal ENNReal MeasureTheory

/-!
# SPMF Mass

The equations of `SPMF.mass` for each combinator, each the combinator's expectation equation at the
postcondition `1`, and `SPMF.IsPMF` (mass exactly 1).
-/

namespace SPMF

section mass

@[simp]
theorem mass_pick {x y : SPMF α} :
    (pick (fun () => x) (fun () => y)).mass = (1/2 : ℝ≥0∞) * x.mass + (1/2 : ℝ≥0∞) * y.mass := by
  simpa only [expect_one] using expect_pick x y fun _ => 1

@[simp]
theorem mass_bot : Bot.bot (α := SPMF α).mass = 0 := by
  simp only [mass, ENNReal.tsum_eq_zero]
  solve_by_elim

@[simp]
theorem mass_pure (a : α) : (Pure.pure a : SPMF α).mass = 1 := by
  rw [← expect_one, expect_pure]

@[simp]
theorem mass_bind_tsum {x : SPMF α} {f : α → SPMF β} :
    (x >>= f).mass = ∑' a, x a * (f a).mass := by
  rw [← expect_one, expect_bind]
  simp only [expect_one]
  rfl

@[simp]
theorem mass_choose (lo hi : Nat) (h : lo ≤ hi) :
    (choose lo hi h : SPMF (ULift {x : Nat // lo ≤ x ∧ x ≤ hi})).mass = 1 := by
  rw [← expect_one]
  refine (Mix.range_average lo hi fun _ => 1).trans ?_
  rw [Finset.sum_const, card_Icc_eq lo hi h, nsmul_eq_mul, mul_one]
  exact ENNReal.div_self (Nat.cast_ne_zero.mpr (Nat.add_one_ne_zero _)) (ENNReal.natCast_ne_top _)

@[simp]
theorem mass_bind_pure {x : SPMF α} {f : α → β} :
    (x >>= fun a => Pure.pure (f a)).mass = x.mass := by
  rw [← expect_one, expect_bind]
  simp only [expect_one, mass_pure]

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
  calc c * d ≤ x.mass * d := by gcongr
    _ = expect x fun _ => d := (expect_const x d).symm
    _ ≤ expect x fun a => (f a).mass := expect_mono hf
    _ = (x >>= f).mass := by rw [← expect_one, expect_bind]; simp only [expect_one]

/-- The mass of a uniform choice is the average of the branch masses. -/
@[simp]
theorem mass_oneOf
    {gs : List (Unit → SPMF α)} {h : gs ≠ []} :
    (oneOf gs h : SPMF α).mass
      = (gs.map (fun p => (p ()).mass)).sum / (gs.length : ℝ≥0∞) := by
  simpa only [expect_one] using expect_oneOf h fun _ => 1

/-- The mass of a weighted choice is the weighted average of the branch masses. -/
@[simp]
theorem mass_frequency
    {gs : List (Nat × (Unit → SPMF α))} (h : 0 < (gs.map Prod.fst).sum) :
    (frequency gs h : SPMF α).mass
      = (gs.map fun p => (p.1 : ℝ≥0∞) * (p.2 ()).mass).sum / ((gs.map Prod.fst).sum : ℝ≥0∞) := by
  simpa only [expect_one] using expect_frequency h fun _ => 1

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
