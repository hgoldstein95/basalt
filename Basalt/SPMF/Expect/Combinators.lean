/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
module

public import Basalt.SPMF.Mass

/-!
# Expectations of the List Combinators

Event probabilities and expected lengths for `vectorOf` and `listOf`, and the distribution of
`suchThat`, by induction or fixpoint induction over the equations of `Basalt/SPMF/Expect/Obs.lean`.
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

/-- How often `g` draws a value that `p` rejects, as the expectation the walk's `suchThat` rules
bound. -/
theorem prob_reject_eq_expect (g : SPMF α) (p : α → Bool) :
    prob g {a | p a = false} = expect g fun a => if p a then 0 else 1 := by
  unfold prob
  congr 1
  funext a
  by_cases h : p a <;> simp [Set.indicator, h]

/-- How often `g` draws a value that `p` accepts. -/
theorem prob_accept_eq_expect (g : SPMF α) (p : α → Bool) :
    prob g {a | p a = true} = expect g fun a => if p a then 1 else 0 := by
  unfold prob
  congr 1
  funext a
  by_cases h : p a <;> simp [Set.indicator, h]

/-- Every value `g` draws is accepted or rejected. -/
theorem prob_accept_add_prob_reject (g : SPMF α) (p : α → Bool) :
    prob g {a | p a = true} + prob g {a | p a = false} = g.mass := by
  rw [prob_accept_eq_expect, prob_reject_eq_expect, ← expect_add, ← expect_one]
  congr 1
  funext a
  by_cases h : p a <;> simp [h]

/-- Rejection sampling is `g` conditioned on `p`: an accepted value keeps its weight under `g`,
divided by the chance of acceptance, and a rejected one has none. It needs no hypothesis: when `g`
never accepts, every accepted value has weight `0` and so does every value of the loop. -/
theorem suchThat_apply (g : SPMF α) (p : α → Bool) (a : α) :
    suchThat g p a = if p a then g a / (1 - prob g {b | p b = false}) else 0 := by
  classical
  set r := prob g {b | p b = false} with hr
  set c : ℝ≥0∞ := if p a then g a else 0 with hc
  have hsplit : ∀ x : ℝ≥0∞,
      (expect g fun b => (if p a then 1 else 0) * ({a} : Set α).indicator 1 b
        + x * {b | p b = false}.indicator 1 b) = c + r * x := by
    intro x
    rw [expect_add, expect_mul_left, expect_mul_left]
    change (if p a then 1 else 0) * prob g {a} + x * prob g _ = _
    rw [prob_singleton, mul_comm x]
    split <;> simp [*]
  have hstep : ∀ x : SPMF α,
      (g >>= fun b => if p b then Pure.pure b else x) a = c + r * x a := by
    intro x
    rw [← prob_singleton, prob_bind, ← hsplit]
    congr 1
    funext b
    by_cases hb : p b
    · rcases eq_or_ne b a with rfl | hba
      · simp [hb]
      · simp [hb, hba, hba.symm]
    · rcases eq_or_ne b a with rfl | hba
      · simp [hb]
      · simp [hb, hba]
  have hS : suchThat g p a = c + r * suchThat g p a := by
    conv_lhs => rw [suchThat]
    exact hstep _
  have hmass : c + r ≤ 1 := by
    rw [← mul_one r, ← hsplit]
    refine (expect_mono fun b => ?_).trans ((expect_one g).trans_le (mass_le_one g))
    rcases eq_or_ne b a with rfl | hba <;> by_cases hb : p b <;> simp [Set.indicator, *]
  have hgoal : (if p a then g a / (1 - r) else 0) = c / (1 - r) := by
    split <;> simp [*]
  rw [hgoal]
  rcases lt_or_ge r 1 with hr1 | hr1
  · have hfin : suchThat g p a ≠ ⊤ :=
      ne_top_of_le_ne_top one_ne_top ((prob_singleton _ a).symm.trans_le (prob_le_one _ _))
    have hc' : c = (1 - r) * suchThat g p a := by
      rw [ENNReal.sub_mul fun _ _ => hfin, one_mul]
      exact ENNReal.eq_sub_of_add_eq (ENNReal.mul_ne_top (ne_top_of_lt hr1) hfin) hS.symm
    rw [hc']
    exact (ENNReal.eq_div_iff (tsub_pos_of_lt hr1).ne' (ENNReal.sub_ne_top one_ne_top)).mpr rfl
  · have hc0 : c = 0 := by
      have := hmass.trans_eq (zero_add 1).symm
      exact nonpos_iff_eq_zero.mp (ENNReal.le_of_add_le_add_right one_ne_top
        (this.trans' (add_le_add_right hr1 c)))
    rw [hc0, ENNReal.zero_div, ← prob_singleton]
    refine nonpos_iff_eq_zero.mp (suchThat.fixpoint_induct g p (fun x => prob x {a} ≤ 0)
      (admissible_expect_le _ 0) fun x ih => ?_)
    rw [prob_singleton] at ih ⊢
    rw [hstep x, hc0, nonpos_iff_eq_zero.mp ih, mul_zero, add_zero]

end combinators

end SPMF
