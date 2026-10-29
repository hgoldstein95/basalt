/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
module

import Basalt.Order
public import Basalt.SPMF.Mass

/-!
# Expectations of the List Combinators

Event probabilities and expected lengths for `vectorOf` and `listOf`, and the law of `suchThat`, by
induction or fixpoint induction over the equations of `Basalt/SPMF/Expect/Obs.lean`.
-/

@[expose] public section

open RandomChoice NNReal ENNReal

namespace SPMF

section combinators

/-- A fixed-length draw lands entirely in `E` with probability `prob g E ^ n`. -/
theorem prob_vectorOf_all {g : SPMF α} (E : Set α) (n : Nat) :
    prob (vectorOf n g) {xs | ∀ x ∈ xs, x ∈ E} = prob g E ^ n := by
  classical
  induction n with
  | zero =>
    rw [show vectorOf 0 g = (Pure.pure [] : SPMF (List α)) from rfl, prob_pure,
      ite_eq_left (by intro y hy; simp at hy), pow_zero]
  | succ n ih =>
    rw [vectorOf_succ, prob_bind]
    have hpt : ∀ (x : α) (xs : List α),
        prob (Pure.pure (x :: xs) : SPMF (List α)) {xs | ∀ y ∈ xs, y ∈ E}
          = E.indicator 1 x * ({xs : List α | ∀ y ∈ xs, y ∈ E}).indicator 1 xs := by
      intro x xs
      rw [prob_pure]
      by_cases hx : x ∈ E <;> by_cases hxs : ∀ y ∈ xs, y ∈ E <;>
        simp [Set.indicator, hx, hxs]
    calc expect g (fun x =>
            prob (vectorOf n g >>= fun xs => Pure.pure (x :: xs)) {xs | ∀ y ∈ xs, y ∈ E})
        = expect g (fun x => E.indicator 1 x * prob g E ^ n) := by
          refine expect_congr_support fun x _ => ?_
          rw [prob_bind]
          calc expect (vectorOf n g)
                (fun xs => prob (Pure.pure (x :: xs) : SPMF (List α)) {xs | ∀ y ∈ xs, y ∈ E})
              = expect (vectorOf n g)
                  (fun xs => E.indicator 1 x
                    * ({xs : List α | ∀ y ∈ xs, y ∈ E}).indicator 1 xs) :=
                expect_congr_support fun xs _ => hpt x xs
            _ = E.indicator 1 x
                  * expect (vectorOf n g) (({xs : List α | ∀ y ∈ xs, y ∈ E}).indicator 1) :=
                expect_mul_left _ _ _
            _ = E.indicator 1 x * prob g E ^ n := by
                exact congrArg (E.indicator 1 x * ·) ih
      _ = expect g (fun x => prob g E ^ n * E.indicator 1 x) := by
          congr 1
          funext x
          ring
      _ = prob g E ^ n * expect g (E.indicator 1) := expect_mul_left _ _ _
      _ = prob g E ^ (n + 1) := (pow_succ _ _).symm

/-- The length of a `listOf` draw is geometrically distributed. -/
theorem prob_listOf_length (g : SPMF α) (hg : g.mass = 1) (k : Nat) :
    prob (listOf g) {xs | xs.length = k} = (1/2 : ℝ≥0∞) ^ (k + 1) := by
  induction k with
  | zero =>
    rw [listOf, oneOfWith_eq, prob_oneOf]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil, prob_pure, Set.mem_ofPred_eq]
    have hz : prob (g >>= fun x => listOf g >>= fun xs => Pure.pure (x :: xs))
        {xs | xs.length = 0} = 0 := by
      rw [prob_eq_zero_iff]
      intro a ha
      simp only [mem_support_bind_iff, mem_support_pure_iff] at ha
      obtain ⟨x, hx, xs, hxs, rfl⟩ := ha
      simp
    rw [hz]
    norm_num
  | succ k ih =>
    rw [listOf, oneOfWith_eq, prob_oneOf]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil, prob_pure, Set.mem_ofPred_eq]
    rw [ite_eq_right (by omega)]
    have hstep : prob (g >>= fun x => listOf g >>= fun xs => Pure.pure (x :: xs))
        {xs | xs.length = k + 1} = (1/2 : ℝ≥0∞) ^ (k + 1) := by
      rw [prob_bind]
      have hinner : ∀ x : α,
          prob (listOf g >>= fun xs => Pure.pure (x :: xs)) {xs | xs.length = k + 1}
            = (1/2 : ℝ≥0∞) ^ (k + 1) := by
        intro x
        rw [prob_bind]
        have hpt : ∀ xs : List α,
            prob (Pure.pure (x :: xs) : SPMF (List α)) {xs | xs.length = k + 1}
              = ({xs : List α | xs.length = k}).indicator 1 xs := by
          intro xs
          rw [prob_pure]
          by_cases h : xs.length = k
          · simp [Set.indicator, h]
          · rw [ite_eq_right (by simp; omega)]
            simp [Set.indicator, h]
        calc expect (listOf g)
              (fun xs => prob (Pure.pure (x :: xs) : SPMF (List α)) {xs | xs.length = k + 1})
            = expect (listOf g) (({xs : List α | xs.length = k}).indicator 1) :=
              expect_congr_support fun xs _ => hpt xs
          _ = (1/2 : ℝ≥0∞) ^ (k + 1) := ih
      calc expect g (fun x =>
              prob (listOf g >>= fun xs => Pure.pure (x :: xs)) {xs | xs.length = k + 1})
          = expect g (fun _ => (1/2 : ℝ≥0∞) ^ (k + 1)) :=
            expect_congr_support fun x _ => hinner x
        _ = g.mass * (1/2 : ℝ≥0∞) ^ (k + 1) := expect_const _ _
        _ = (1/2 : ℝ≥0∞) ^ (k + 1) := by rw [hg, one_mul]
    rw [hstep]
    simp only [zero_add, add_zero]
    norm_num [pow_succ, div_eq_mul_inv, one_div]

/-- No mass hypothesis: missing mass only lowers the expectation. -/
theorem expect_listOf_length_le (g : SPMF α) :
    expect (listOf g) (fun xs => (xs.length : ℝ≥0∞)) ≤ 1 := by
  delta listOf
  apply Lean.Order.fix_induct
    (motive := fun (p : SPMF (List α)) => expect p (fun xs => (xs.length : ℝ≥0∞)) ≤ 1)
    _ ?admissible ?step
  case admissible => exact admissible_expect_le _ _
  case step =>
    intro listOf_rec ih
    rw [oneOfWith_eq, expect_oneOf]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil, expect_pure, Nat.cast_zero, add_zero, zero_add]
    rw [ENNReal.div_eq_inv_mul, ← one_div]
    have hinner : ∀ x : α,
        expect (listOf_rec >>= fun xs => Pure.pure (x :: xs))
          (fun xs => (xs.length : ℝ≥0∞)) ≤ 2 := by
      intro x
      rw [expect_bind]
      calc expect listOf_rec
            (fun xs => expect (Pure.pure (x :: xs) : SPMF (List α))
              (fun xs => (xs.length : ℝ≥0∞)))
          = expect listOf_rec (fun xs => (xs.length : ℝ≥0∞) + 1) := by
            refine expect_congr_support fun xs _ => ?_
            rw [expect_pure]
            push_cast [List.length_cons]
            ring
        _ = expect listOf_rec (fun xs => (xs.length : ℝ≥0∞))
              + expect listOf_rec (fun _ => 1) := expect_add _ _ _
        _ ≤ 1 + 1 := add_le_add ih (by rw [expect_one]; exact mass_le_one _)
        _ = 2 := by norm_num
    have half : ∀ E : ℝ≥0∞, E ≤ 2 → (1/2 : ℝ≥0∞) * E ≤ 1 := by
      intro E hE
      calc (1/2 : ℝ≥0∞) * E ≤ (1/2 : ℝ≥0∞) * 2 := mul_le_mul_right hE _
        _ = 1 := by
          rw [one_div]
          exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)
    apply half
    rw [expect_bind]
    refine le_trans (expect_mono fun x => hinner x) ?_
    rw [expect_const]
    calc g.mass * 2 ≤ 1 * 2 := mul_le_mul_left (mass_le_one g) _
      _ = 2 := by norm_num

end combinators

section suchThat

open Lean.Order

/-- One round of rejection sampling, with `z` for the retry. -/
theorem bind_reject_apply (g : SPMF α) (P : α → Bool) (z : SPMF α) (a : α) :
    (g >>= fun b => if P b then Pure.pure b else z) a
      = (if P a then g a else 0) + prob g {b | P b = false} * z a := by
  classical
  rw [bind_apply, prob_eq_tsum_ite, ← ENNReal.tsum_mul_right]
  have h : ∀ b, g b * (if P b = true then Pure.pure b else z) a
      = (if P b = true ∧ a = b then g b else 0)
        + (if b ∈ {b | P b = false} then g b else 0) * z a := by
    intro b
    by_cases hb : P b = true <;> by_cases hab : a = b <;> simp [hb, hab]
  rw [tsum_congr h, ENNReal.tsum_add]
  rw [tsum_eq_single a fun b hb => by simp [Ne.symm hb]]
  by_cases ha : P a = true <;> simp [ha]

/-- What `g` accepts and what it rejects add up to its mass. -/
theorem prob_accept_add_reject (g : SPMF α) (P : α → Bool) :
    prob g {b | P b = true} + prob g {b | P b = false} = g.mass := by
  classical
  rw [prob_eq_tsum_ite, prob_eq_tsum_ite, ← ENNReal.tsum_add, mass]
  refine tsum_congr fun b => ?_
  by_cases hb : P b = true <;> simp [hb]

private theorem accept_le (g : SPMF α) (P : α → Bool) (a : α) :
    (if P a then g a else 0) + prob g {b | P b = false} ≤ 1 := by
  classical
  refine le_trans ?_ ((prob_accept_add_reject g P).le.trans g.mass_le_one)
  gcongr
  rw [prob_eq_tsum_ite]
  refine le_trans ?_ (ENNReal.le_tsum a)
  by_cases ha : P a = true <;> simp [ha]

private theorem add_one_le_one {A : ℝ≥0∞} (h : A + 1 ≤ 1) : A = 0 :=
  nonpos_iff_eq_zero.1 ((ENNReal.add_le_add_iff_right ENNReal.one_ne_top).1 (by simpa using h))

/-- `A + R · A / (1 - R) = A / (1 - R)`: the closed form solves one round. -/
private theorem solve_round {A R : ℝ≥0∞} (hAR : A + R ≤ 1) :
    A + R * (A / (1 - R)) = A / (1 - R) := by
  rcases (le_trans le_add_self hAR).lt_or_eq with hR | rfl
  · have hD0 : 1 - R ≠ 0 := (tsub_pos_of_lt hR).ne'
    have hDtop : 1 - R ≠ ⊤ := ENNReal.sub_ne_top ENNReal.one_ne_top
    calc A + R * (A / (1 - R)) = A / (1 - R) * (1 - R) + A / (1 - R) * R := by
          rw [ENNReal.div_mul_cancel hD0 hDtop, mul_comm]
      _ = A / (1 - R) := by rw [← mul_add, tsub_add_cancel_of_le hR.le, mul_one]
  · obtain rfl : A = 0 := add_one_le_one hAR
    simp

/-- Pointwise upper bounds are admissible: the fixpoint induction behind every rejection loop. -/
theorem admissible_apply_le (c : α → ℝ≥0∞) : admissible fun μ : SPMF α => ∀ a, μ a ≤ c a :=
  admissible_iff.2 fun _ hc ih a => by
    rw [csup_apply hc]; exact iSup₂_le fun μ hμ => ih μ hμ a

/-- **A rejection loop's law.** A distribution `r` that keeps `A a` and retries with probability `R`
(`hfix`), and lies below every function closed under that round (`hlfp`, from fixpoint induction),
is `A a / (1 - R)`. -/
theorem rejection_loop_apply {r : SPMF α} {A : α → ℝ≥0∞} {R : ℝ≥0∞} (hAR : ∀ a, A a + R ≤ 1)
    (hfix : ∀ a, r a = A a + R * r a)
    (hlfp : ∀ c : α → ℝ≥0∞, (∀ a, A a + R * c a ≤ c a) → ∀ a, r a ≤ c a) (a : α) :
    r a = A a / (1 - R) := by
  refine le_antisymm (hlfp _ (fun b => (solve_round (hAR b)).le) a) ?_
  rcases (le_trans le_add_self (hAR a)).lt_or_eq with hR | hR
  · refine ENNReal.div_le_of_le_mul ?_
    have hRs : R * r a ≠ ⊤ :=
      ENNReal.mul_ne_top (ne_top_of_le_ne_top ENNReal.one_ne_top hR.le) (apply_ne_top _ _)
    rw [ENNReal.mul_sub (fun _ _ => apply_ne_top _ _), mul_one, mul_comm,
      ENNReal.eq_sub_of_add_eq hRs (hfix a).symm]
  · have := hAR a
    rw [hR] at this
    simp [add_one_le_one this]

/-- **The conditional law of rejection sampling.** It holds for every `g` and `P`. When `g` always
rejects, every accepted `g a` is `0` and `0 / 0 = 0`; that case is the one only the least fixed
point decides. -/
theorem suchThat_apply (g : SPMF α) (P : α → Bool) (a : α) :
    (suchThat g P : SPMF α) a
      = if P a then g a / (1 - prob g {b | P b = false}) else 0 := by
  have hite : (if P a then g a / (1 - prob g {b | P b = false}) else 0)
      = (if P a then g a else 0) / (1 - prob g {b | P b = false}) := by cases P a <;> simp
  rw [hite]
  refine rejection_loop_apply (accept_le g P) (fun b => ?_) (fun c hc => ?_) a
  · conv_lhs => rw [suchThat]
    exact bind_reject_apply g P _ b
  · refine suchThat.fixpoint_induct (G := SPMF) g P _ (admissible_apply_le c) fun z hz b => ?_
    rw [bind_reject_apply]
    exact le_trans (by gcongr; exact hz b) (hc b)

/-- A rejection loop that accepts with probability `0` is `⊥`. -/
theorem suchThat_eq_bot (g : SPMF α) (P : α → Bool) (hq : prob g {b | P b = true} = 0) :
    (suchThat g P : SPMF α) = Bot.bot := by
  classical
  ext a
  rw [suchThat_apply]
  split
  · have : g a = 0 := by
      rw [prob_eq_tsum_ite, ENNReal.tsum_eq_zero] at hq
      simpa [*] using hq a
    rw [this, ENNReal.zero_div]
    rfl
  · rfl

/-- When `g` terminates, the retry rate is `1 - q` and the law is `g a / q`. -/
theorem suchThat_apply_of_mass (g : SPMF α) (P : α → Bool) (hg : g.mass = 1) (a : α) :
    (suchThat g P : SPMF α) a = if P a then g a / prob g {b | P b = true} else 0 := by
  rw [suchThat_apply]
  have h := prob_accept_add_reject g P
  rw [hg] at h
  rw [← h, ENNReal.add_sub_cancel_right]
  exact (prob_le_mass _ _).trans_lt ((mass_le_one g).trans_lt ENNReal.one_lt_top) |>.ne

end suchThat

end SPMF
