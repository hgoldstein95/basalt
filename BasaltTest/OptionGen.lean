/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt

/-!
# A Derived Combinator With No Law

`biasedOptionGen` and `optionGen` are fixtures, not library combinators: they have no `@[gen_map]`
lemma and no law, so a walk has to unfold and traverse their bodies. `BasaltTest/Tactic/Mass.lean`
and `BasaltTest/Tactic/Cost.lean` pin that path; `SPMF.massSome_biasedOptionGen` below is the worked
acceptance rate that `SPMF.retry_attempts` turns into a retry count. The partial-generator laws,
`IsProductive` and `IsFilterFree`, are proved at the end through their introduction lemmas.
-/

open Lean.Order RandomChoice NNReal ENNReal

/-- Lifts a generator of `α`'s into a generator of `Option α`'s, which returns `some <$> g` with
probability `r`.

Note: we explicitly use `bind` instead of `<$>` in the body of this combinator, as there is no
monotonicity lemma for `<$>` in `Lean.Order`. -/
def biasedOptionGen [Gen G] (r : Rat) (g : G α) : G (Option α) := do
  if ← RandomChoice.coin r then do
    let x ← g
    pure (some x)
  else
    pure none

/-- Lifts a generator of `α`'s into a generator of `Option α`'s, which returns `none` with probability 1/2 -/
def optionGen [Gen G] (g : G α) : G (Option α) :=
  biasedOptionGen (1 / 2) g

/-- Lemma allowing us to use `biasedOptionGen` in functions marked as `partial_fixpoint`. -/
@[partial_fixpoint_monotone]
theorem monotone_biasedOptionGen [Gen G] [Lean.Order.PartialOrder γ]
    (g : γ → G α) (hg : monotone g) :
    monotone (fun x => biasedOptionGen r (g x)) := by
  unfold biasedOptionGen
  apply monotone_bind
  . apply Lean.Order.monotone_const
  . apply monotone_of_monotone_apply
    intro b
    cases b <;> simp
    . apply Lean.Order.monotone_const
    . apply monotone_bind
      . assumption
      . apply Lean.Order.monotone_const

/-- Lemma allowing us to use `optionGen` in functions marked as `partial_fixpoint` -/
@[partial_fixpoint_monotone]
theorem monotone_optionGen [Gen G] [Lean.Order.PartialOrder γ]
    (g : γ → G α) (hg : monotone g) :
    monotone (fun x => optionGen (g x)) := by
  unfold optionGen
  apply monotone_biasedOptionGen
  assumption

/-- A generator that draws an unbounded list of successes, exercising the two lemmas above. -/
def optionListOf [Gen G] (g : G α) : G (List α) := do
  match ← optionGen g with
  | none => pure []
  | some x => do
    let xs ← optionListOf g
    pure (x :: xs)
partial_fixpoint

namespace SPMF

/-- The acceptance rate of a biased filter: `biasedOptionGen r g` succeeds with probability
`r · mass g`. Feeds `retry_attempts` to bound the cost of rejection sampling. -/
theorem massSome_biasedOptionGen {r : Rat} {g : SPMF α} (h0 : 0 ≤ r) (h1 : r ≤ 1) :
    massSome (biasedOptionGen r g)
      = (r.num.toNat : ℝ≥0∞) / (r.den : ℝ≥0∞) * g.mass := by
  rw [massSome_eq_prob]
  unfold biasedOptionGen
  rw [prob_bind, expect_coin h0 h1]
  have htrue : prob ((g >>= fun x => Pure.pure (some x)) : SPMF (Option α))
      {o | o.isSome = true} = g.mass := by
    rw [prob_bind]
    calc expect g (fun x => prob (Pure.pure (some x) : SPMF (Option α)) {o | o.isSome = true})
        = expect g (fun _ => 1) := expect_congr_support fun x _ => by rw [prob_pure]; simp
      _ = g.mass := expect_one g
  have hfalse : prob (Pure.pure none : SPMF (Option α)) {o | o.isSome = true} = 0 := by
    rw [prob_pure]
    simp
  rw [ite_eq_left (by trivial), ite_eq_right (by simp), htrue, hfalse, mul_zero, add_zero]

theorem massSome_optionGen {g : SPMF α} : massSome (optionGen g) = g.mass / 2 := by
  unfold optionGen
  rw [massSome_biasedOptionGen (by norm_num) (by norm_num)]
  rw [one_div, Rat.inv_ofNat_num, Rat.inv_ofNat_den, Int.toNat_one, Nat.cast_one,
    Nat.cast_ofNat, one_div, ENNReal.div_eq_inv_mul]

end SPMF

/-! ## The partial-generator laws -/

def genMaybe [Gen G] : G (Option Nat) :=
  oneOf [fun _ => pure none, fun _ => pure (some 0)]

theorem genMaybe.productive : IsProductive (genMaybe (G := SPMF)) :=
  IsProductive.of_mem_support (a := 0)
    (by simp [genMaybe, SPMF.support_oneOf, SPMF.support_pure])

def genSurely [Gen G] : G (Option Nat) :=
  oneOf [fun _ => pure (some 0), fun _ => pure (some 1)]

theorem genSurely.filter_free : IsFilterFree (genSurely (G := SPMF)) := by
  have hmass : SPMF.IsPMF (genSurely (G := SPMF)) := by
    mass_fixpoint using SPMF.LfpIsOne.one
    norm_num [ENNReal.div_self]
  rw [IsFilterFree_iff_massNone_eq_zero hmass]
  show (genSurely (G := SPMF)) none = 0
  rw [SPMF.apply_eq_zero_iff]
  simp [genSurely, SPMF.support_oneOf, SPMF.support_pure]

theorem genSurely.productive : IsProductive (genSurely (G := SPMF)) :=
  IsFilterFree.isProductive genSurely.filter_free
