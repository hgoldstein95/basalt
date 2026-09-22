/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt.SPMF.Mass

open RandomChoice NNReal ENNReal

/-!
# Expectations of the List Combinators

Event probabilities and expected lengths for `vectorOf` and `listOf`, by induction or fixpoint
induction over the equations of `Basalt/SPMF/Expect/Obs.lean`.
-/

namespace SPMF

section combinators

/-- A fixed-length draw lands entirely in `E` with probability `prob g E ^ n`. -/
theorem prob_vectorOf_all {g : SPMF α} (E : Set α) (n : Nat) :
    prob (vectorOf n g) {xs | ∀ x ∈ xs, x ∈ E} = prob g E ^ n := by
  classical
  induction n with
  | zero =>
    rw [show vectorOf 0 g = (Pure.pure [] : SPMF (List α)) from rfl, prob_pure,
      if_pos (by intro y hy; simp at hy), pow_zero]
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
theorem prob_listOf_length (g : SPMF α) (hg : IsPMF g) (k : Nat) :
    prob (listOf g) {xs | xs.length = k} = (1/2 : ℝ≥0∞) ^ (k + 1) := by
  induction k with
  | zero =>
    rw [listOf, prob_pick, prob_pure]
    simp only [Set.mem_ofPred_eq, List.length_nil]
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
    rw [listOf, prob_pick, prob_pure]
    simp only [Set.mem_ofPred_eq, List.length_nil]
    rw [if_neg (by omega)]
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
          · rw [if_neg (by simp; omega)]
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
    rw [hstep, mul_zero, zero_add, pow_succ]
    ring

/-- No `IsPMF` hypothesis: missing mass only lowers the expectation. -/
theorem expect_listOf_length_le (g : SPMF α) :
    expect (listOf g) (fun xs => (xs.length : ℝ≥0∞)) ≤ 1 := by
  delta listOf
  apply Lean.Order.fix_induct
    (motive := fun (p : SPMF (List α)) => expect p (fun xs => (xs.length : ℝ≥0∞)) ≤ 1)
    _ ?admissible ?step
  case admissible => exact admissible_expect_le _ _
  case step =>
    intro listOf_rec ih
    rw [expect_pick, expect_pure, expect_bind]
    simp only [List.length_nil, Nat.cast_zero, mul_zero, zero_add]
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
    refine le_trans (expect_mono fun x => hinner x) ?_
    rw [expect_const]
    calc g.mass * 2 ≤ 1 * 2 := mul_le_mul_left (mass_le_one g) _
      _ = 2 := by norm_num

end combinators

end SPMF
