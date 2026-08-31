/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt.SPMF
import Mathlib.Analysis.SpecificLimits.Basic

open Lean.Order RandomChoice NNReal ENNReal

/-!
# Partial Generators

This file provides lemmas for working with partial generators that can be interpreted at `SPMF (Option α)`.

## Main definitions

- `SPMF.massSome` / `SPMF.massNone` — mass on successful / failing outcomes.
- `SPMF.mass_split` — the total mass splits as `massSome + massNone`.
- `SPMF.retry` — rejection sampling as a global restart: redraw the whole value on `none`.
- `SPMF.massSome_retry` — retrying a productive, a.s.-terminating draw never fails.
- `SPMF.retry_apply` — retrying yields the conditional distribution given success.
- `SPMF.retry_attempts` — the retry loop takes `1 / massSome` draws in expectation.
-/

namespace SPMF

/-- Sums over an `Option`-indexed `ℝ≥0∞` family split off the `none` term. Mathlib has no
`tsum_option` in this toolchain, so we prove the special case we need. -/
theorem tsum_option (f : Option α → ℝ≥0∞) :
    ∑' o, f o = f none + ∑' a, f (some a) := by
  classical
  rw [ENNReal.tsum_eq_add_tsum_ite none]
  congr 1
  rw [← (Option.some_injective α).tsum_eq
        (f := fun x => @ite _ (x = none) (Classical.propDecidable _) (0 : ℝ≥0∞) (f x))
        (by intro o ho
            cases o with
            | none => simp at ho
            | some a => exact ⟨a, rfl⟩)]
  apply tsum_congr
  intro a
  simp

/-- The mass on successful outcomes: the probability a draw yields a value. This is the acceptance
rate of a filtering generator; it is `1` exactly when the generator never fails and never diverges.
-/
noncomputable def massSome (p : SPMF (Option α)) : ℝ≥0∞ := ∑' a, p (some a)

/-- The probability a draw yields an *explicit* failure (`none`). -/
noncomputable def massNone (p : SPMF (Option α)) : ℝ≥0∞ := p none

/-- The expected number of draws of `p` that a retry loop performs before it succeeds. Each attempt
fails independently with probability `massNone p`, so `P(at least k+1 attempts) = massNone p ^ k`,
and this is the tail-sum expectation `∑ₖ P(≥ k+1 attempts)` of that geometric count.
`retry_attempts` evaluates it to `1 / massSome p`. -/
noncomputable def expectedAttempts (p : SPMF (Option α)) : ℝ≥0∞ := ∑' k : ℕ, (massNone p) ^ k

/-- The total mass of a draw splits into successes and explicit failures. Whatever is left over
(`1 - mass`) is divergence. -/
theorem mass_split (p : SPMF (Option α)) :
    p.mass = massSome p + massNone p := by
  unfold SPMF.mass massSome massNone
  rw [SPMF.tsum_option]
  rw [add_comm]

/-- `massSome` is the probability of the success event. -/
theorem massSome_eq_prob (p : SPMF (Option α)) :
    massSome p = prob p {o | o.isSome = true} := by
  unfold prob expect
  rw [tsum_option (fun o => p o * ({o : Option α | o.isSome = true}).indicator 1 o)]
  simp [massSome, Set.indicator]

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
  rw [if_pos (by trivial), if_neg (by simp), htrue, hfalse, mul_zero, add_zero]

theorem massSome_optionGen {g : SPMF α} : massSome (optionGen g) = g.mass / 2 := by
  unfold optionGen
  rw [massSome_biasedOptionGen (by norm_num) (by norm_num)]
  rw [one_div, Rat.inv_ofNat_num, Rat.inv_ofNat_den, Int.toNat_one, Nat.cast_one,
    Nat.cast_ofNat, one_div, ENNReal.div_eq_inv_mul]

/-!
## Retry

On failure (`none`), `retry` discards the whole draw and redraws. This is a `partial_fixpoint` over
`SPMF (Option α)`, and it yields the conditional distribution given success — the theorem that
finally connects filtering to a distribution.
-/

/-- The retry loop: on `some a` stop, on `none` re-enter. Defined by `partial_fixpoint` — it
terminates almost surely exactly when the underlying draw is productive (`SPMF.IsPMF_retry`). -/
noncomputable def retry (p : SPMF (Option α)) : SPMF (Option α) :=
  (p >>= fun o =>
    match o with
    | some a => (Pure.pure (some a) : SPMF (Option α))
    | none => retry p)
  partial_fixpoint

theorem retry_eq (p : SPMF (Option α)) :
    retry p = p >>= fun o =>
      match o with
      | some a => (Pure.pure (some a) : SPMF (Option α))
      | none => retry p := by
  conv_lhs => rw [retry]

/-- The mass recurrence: a retry either succeeds now (mass `massSome p`) or fails now (probability
`massNone p`) and re-enters the same loop. -/
theorem mass_retry (p : SPMF (Option α)) :
    (retry p).mass = massSome p + massNone p * (retry p).mass := by
  conv_lhs => rw [retry_eq]
  rw [SPMF.mass_bind_tsum, SPMF.tsum_option]
  simp only [SPMF.mass_pure, mul_one]
  rw [add_comm]
  rfl

/-- The retry loop terminates almost surely whenever the underlying draw is productive (succeeds
with positive probability) and itself terminates almost surely. -/
theorem IsPMF_retry (p : SPMF (Option α)) (hmass : p.mass = 1)
    (hprod : 0 < massSome p) : SPMF.IsPMF (retry p) := by
  have hsn : massSome p + massNone p = 1 := by rw [← mass_split p]; exact hmass
  refine (SPMF.IsPMF_of_mass_fixpoint
    (g := fun _ : Unit => retry p)
    (F := fun c => massSome p + massNone p * c)
    ?bounds ?mass) ()
  case bounds =>
    intro c hle hge
    have hs1 : massSome p ≤ 1 := le_of_add_le_left hsn.le
    have hn1 : massNone p ≤ 1 := le_of_add_le_right hsn.le
    have hspos : 0 < (massSome p).toReal := ENNReal.toReal_pos hprod.ne' (by finiteness)
    rw [← ENNReal.toReal_eq_one_iff]
    ennreal_to_real at hge   -- before `hle`: finiteness needs `c ≤ 1`
    ennreal_to_real at hsn
    ennreal_to_real at hle
    nlinarith [hge, hsn, hle, hspos]
  case mass =>
    intro _ _
    rw [iInf_const]
    exact (mass_retry p).ge

/-- The retry loop never lands on an explicit failure: it retries every `none`. -/
theorem retry_none (p : SPMF (Option α)) :
    retry p none = massNone p * retry p none := by
  conv_lhs => rw [retry_eq]
  rw [SPMF.bind_apply, SPMF.tsum_option]
  have hz : ∀ a', p (some a') * ((Pure.pure (some a') : SPMF (Option α)) none) = 0 := by
    intro a'
    have hp : (Pure.pure (some a') : SPMF (Option α)) none = 0 := by
      simp only [Pure.pure, SPMF.pure, DFunLike.coe]; simp
    rw [hp, mul_zero]
  simp only [hz, tsum_zero, add_zero]
  rfl

/-- Under productivity, the retry loop puts *zero* mass on explicit failure. -/
theorem retry_none_eq_zero (p : SPMF (Option α)) (hmass : p.mass = 1)
    (hprod : 0 < massSome p) : retry p none = 0 := by
  have hrec := retry_none p
  by_contra hne
  have hNtop : retry p none ≠ ⊤ := SPMF.apply_ne_top _ none
  have hn_lt : massNone p < 1 := by
    calc massNone p < massSome p + massNone p := by
          rw [add_comm]
          exact ENNReal.lt_add_right (SPMF.apply_ne_top p none) hprod.ne'
      _ = 1 := by rw [← mass_split p]; exact hmass
  have hlt : retry p none * massNone p < retry p none := by
    calc retry p none * massNone p < retry p none * 1 :=
          ENNReal.mul_lt_mul_right hne hNtop hn_lt
      _ = retry p none := mul_one _
  rw [mul_comm, ← hrec] at hlt
  exact lt_irrefl _ hlt

/-- **Retry makes a productive generator filter-free.** If `p` terminates almost surely (`mass = 1`)
and succeeds with positive probability (`0 < massSome p`), then `retry p` never fails and never
diverges: all of its mass is on values. -/
theorem massSome_retry (p : SPMF (Option α))
    (hmass : p.mass = 1) (hprod : 0 < massSome p) :
    massSome (retry p) = 1 := by
  have hpmf : (retry p).mass = 1 := IsPMF_retry _ hmass hprod
  have hnone : massNone (retry p) = 0 := retry_none_eq_zero _ hmass hprod
  have hsplit : (retry p).mass = massSome (retry p) + massNone (retry p) := mass_split _
  rw [hpmf, hnone, add_zero] at hsplit
  exact hsplit.symm

/-- The success recurrence: a value `a` comes out either on the first draw, or after a failure and a
re-entry into the loop. -/
theorem retry_some (p : SPMF (Option α)) (a : α) :
    retry p (some a) = p (some a) + massNone p * retry p (some a) := by
  conv_lhs => rw [retry_eq]
  rw [SPMF.bind_apply, SPMF.tsum_option]
  have hsum : (∑' a', p (some a') * ((Pure.pure (some a') : SPMF (Option α)) (some a)))
      = p (some a) := by
    rw [tsum_eq_single a]
    · have h1 : (Pure.pure (some a) : SPMF (Option α)) (some a) = 1 := by
        simp only [Pure.pure, SPMF.pure, DFunLike.coe]; simp
      rw [h1, mul_one]
    · intro a' ha'
      have h0 : (Pure.pure (some a') : SPMF (Option α)) (some a) = 0 := by
        simp only [Pure.pure, SPMF.pure, DFunLike.coe]
        rw [if_neg]; intro h; exact ha' (Option.some_injective _ h).symm
      rw [h0, mul_zero]
  rw [hsum, add_comm]
  rfl

/-- **Retry yields the conditional distribution given success.** For a productive,
almost-surely-terminating draw, the probability that `retry` outputs `a` is `p (some a)`
renormalized by the acceptance rate `massSome`. -/
theorem retry_apply (p : SPMF (Option α)) (hmass : p.mass = 1)
    (hprod : 0 < massSome p) (a : α) :
    retry p (some a) = p (some a) / massSome p := by
  set R := retry p (some a) with hR
  set s := massSome p with hs
  set n := massNone p with hn
  set c := p (some a) with hc
  have hsn : s + n = 1 := by rw [hs, hn, ← mass_split p]; exact hmass
  have hrec : R = c + n * R := retry_some p a
  have hrec' : R = c + R * n := by rw [mul_comm] at hrec; exact hrec
  have hRn_ne : R * n ≠ ⊤ :=
    ENNReal.mul_ne_top (SPMF.apply_ne_top _ _) (SPMF.apply_ne_top _ _)
  have h1 : R * n + R * s = R * n + c := by
    rw [← mul_add, add_comm n s, hsn, mul_one]
    conv_lhs => rw [hrec']
    rw [add_comm]
  have hRs : R * s = c := (ENNReal.add_right_inj hRn_ne).mp h1
  have hs_ne : s ≠ ⊤ := ne_top_of_le_ne_top one_ne_top (le_of_add_le_left hsn.le)
  rw [ENNReal.eq_div_iff hprod.ne' hs_ne, mul_comm]
  exact hRs

/-- **The expected number of attempts is `1 / massSome`.** For an almost-surely-terminating draw,
the retry loop runs `1 / massSome p` draws in expectation. -/
theorem retry_attempts (p : SPMF (Option α)) (hmass : p.mass = 1) :
    expectedAttempts p = 1 / massSome p := by
  unfold expectedAttempts
  rw [ENNReal.tsum_geometric]
  have hsn : massSome p + massNone p = 1 := by rw [← mass_split p]; exact hmass
  have hn_ne : massNone p ≠ ⊤ := SPMF.apply_ne_top _ none
  have h1n : 1 - massNone p = massSome p := by
    rw [← hsn, ENNReal.add_sub_cancel_right hn_ne]
  rw [h1n, one_div]

end SPMF
