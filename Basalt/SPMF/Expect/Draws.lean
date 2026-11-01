/-
Copyright (c) 2026 Harrison Goldstein & Ernest Ng. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein & Ernest Ng
-/
module

public import Basalt.SPMF.Expect.Combinators
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# How Many Draws Until a Shape Appears

`vectorOf N g` is `N` independent draws from `g`. If one draw has a shape `E` with probability at
least `q`, these bounds say how many draws a test needs to see `E`:

* `prob_vectorOf_miss_le` (the geometric bound): all `N` draws miss `E` with probability at most
  `(1 − q)ᴺ`, and `prob_vectorOf_miss_le_of_log_le` makes it at most `δ` once
  `N ≥ ln(1/δ) / q`.
* `tsum_prob_vectorOf_miss_le`: `∑ₙ P(n draws all miss E) ≤ 1 / q`.
* `prob_vectorOf_someMiss_le` (the coupon-collector bound): for events `E i`, `i ∈ s`, some event
  is missed by all `N` draws with probability at most `∑ᵢ (1 − qᵢ)ᴺ`, and at most `δ` once
  `N ≥ ln(|s|/δ) / q` for a common bound `q` (`prob_vectorOf_someMiss_le_of_log_le`).
* `tsum_prob_vectorOf_someMiss_le`: `∑ₙ P(after n draws some E i is missing) ≤ ∑ᵢ 1 / qᵢ`.

**Reading the sums as expected waiting times.** For a generator that terminates almost surely,
`∑ₙ P(the first n draws all miss E)` is the expected number of draws until the first draw in `E`,
by the tail-sum formula `E[T] = ∑ₙ P(T > n)`; the coupon-collector sum is likewise the expected
number of draws until every `E i` has appeared. This module proves the bounds on the sums and does
not define the waiting time `T` itself, so that reading is an interpretation, not a theorem here.

**What a draw is.** `vectorOf N g` draws `N` times from one generator at fixed arguments. That
models a test run of a generator with no size parameter. A runner that changes a size parameter
from one test to the next draws from a different generator each time, and these bounds do not
cover it directly.
-/

@[expose] public section

open RandomChoice NNReal ENNReal

namespace SPMF

section draws

variable {α : Type} (g : SPMF α)

theorem le_one_of_le_prob {E : Set α} {q : ℝ≥0∞} (hq : q ≤ prob g E) : q ≤ 1 :=
  hq.trans ((prob_le_mass g E).trans (mass_le_one g))

/-- **The geometric bound.** If one draw lands in `E` with probability at least `q`, then `N`
independent draws all miss `E` with probability at most `(1 − q)ᴺ`. -/
theorem prob_vectorOf_miss_le {E : Set α} {q : ℝ≥0∞} (hq : q ≤ prob g E) (N : Nat) :
    prob (vectorOf N g) {xs | ∀ x ∈ xs, x ∉ E} ≤ (1 - q) ^ N := by
  have h := prob_vectorOf_all (g := g) Eᶜ N
  simp only [Set.mem_compl_iff] at h
  rw [h]
  -- `E` and its complement split the mass, which is at most `1`.
  have hsplit : prob g Eᶜ + prob g E = g.mass := by
    unfold prob
    rw [← expect_add, ← expect_one]
    congr 1
    funext a
    by_cases h : a ∈ E <;> simp [Set.indicator, h]
  have hE : prob g E ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top
    ((prob_le_mass g E).trans (mass_le_one g))
  have hc : prob g Eᶜ ≤ 1 - q := by
    rw [ENNReal.eq_sub_of_add_eq hE hsplit]
    exact tsub_le_tsub (mass_le_one g) hq
  exact pow_le_pow_left₀ (by positivity) hc N

/-- If one draw lands in `E` with probability at least `q`, then `∑ₙ P(n draws all miss E) ≤ 1/q`.
Read the module docstring for why this sum is the expected number of draws until the first hit. -/
theorem tsum_prob_vectorOf_miss_le {E : Set α} {q : ℝ≥0∞} (hq : q ≤ prob g E) :
    ∑' N, prob (vectorOf N g) {xs | ∀ x ∈ xs, x ∉ E} ≤ q⁻¹ := by
  calc ∑' N, prob (vectorOf N g) {xs | ∀ x ∈ xs, x ∉ E}
      ≤ ∑' N, (1 - q) ^ N := ENNReal.tsum_le_tsum fun N => prob_vectorOf_miss_le g hq N
    _ = q⁻¹ := by
        rw [ENNReal.tsum_geometric,
          ENNReal.sub_sub_cancel ENNReal.one_ne_top (le_one_of_le_prob g hq)]

/-- **The coupon-collector bound.** If one draw lands in `E i` with probability at least `q i`, for
each `i ∈ s`, then after `N` independent draws some `E i` has been missed by every draw with
probability at most `∑ᵢ (1 − q i)ᴺ`. -/
theorem prob_vectorOf_someMiss_le {ι : Type} (s : Finset ι) (E : ι → Set α)
    (q : ι → ℝ≥0∞) (hq : ∀ i ∈ s, q i ≤ prob g (E i)) (N : Nat) :
    prob (vectorOf N g) {xs | ∃ i ∈ s, ∀ x ∈ xs, x ∉ E i}
      ≤ ∑ i ∈ s, (1 - q i) ^ N := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.notMem_empty, false_and, exists_false, Set.ofPred_false, Finset.sum_empty]
    exact le_of_eq ((prob_eq_zero_iff _ _).mpr fun _ _ h => h)
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    have hsub : {xs : List α | ∃ i ∈ insert a s, ∀ x ∈ xs, x ∉ E i}
        ⊆ {xs | ∀ x ∈ xs, x ∉ E a} ∪ {xs | ∃ i ∈ s, ∀ x ∈ xs, x ∉ E i} := by
      rintro xs ⟨i, hi, hxs⟩
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact Or.inl hxs
      · exact Or.inr ⟨i, hi, hxs⟩
    -- The union bound.
    have hunion : ∀ A B : Set (List α), prob (vectorOf N g) (A ∪ B)
        ≤ prob (vectorOf N g) A + prob (vectorOf N g) B := fun A B => by
      unfold prob
      rw [← expect_add]
      refine expect_mono fun a => ?_
      by_cases ha : a ∈ A <;> by_cases hb : a ∈ B <;> simp [Set.indicator, ha, hb]
    refine (prob_mono hsub).trans ((hunion _ _).trans (add_le_add ?_ ?_))
    · exact prob_vectorOf_miss_le g (hq a (Finset.mem_insert_self a s)) N
    · exact ih fun i hi => hq i (Finset.mem_insert_of_mem hi)

/-- If one draw lands in `E i` with probability at least `q i`, for each `i ∈ s`, then
`∑ₙ P(after n draws some E i is still missing) ≤ ∑ᵢ 1 / q i`. -/
theorem tsum_prob_vectorOf_someMiss_le {ι : Type} (s : Finset ι) (E : ι → Set α)
    (q : ι → ℝ≥0∞) (hq : ∀ i ∈ s, q i ≤ prob g (E i)) :
    ∑' N, prob (vectorOf N g) {xs | ∃ i ∈ s, ∀ x ∈ xs, x ∉ E i} ≤ ∑ i ∈ s, (q i)⁻¹ := by
  calc ∑' N, prob (vectorOf N g) {xs | ∃ i ∈ s, ∀ x ∈ xs, x ∉ E i}
      ≤ ∑' N, ∑ i ∈ s, (1 - q i) ^ N :=
        ENNReal.tsum_le_tsum fun N => prob_vectorOf_someMiss_le g s E q hq N
    _ = ∑ i ∈ s, ∑' N, (1 - q i) ^ N := Summable.tsum_finsetSum fun _ _ => ENNReal.summable
    _ = ∑ i ∈ s, (q i)⁻¹ := by
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [ENNReal.tsum_geometric,
          ENNReal.sub_sub_cancel ENNReal.one_ne_top (le_one_of_le_prob g (hq i hi))]

/-! ### Confidence bounds, through `1 − q ≤ e^{−q}` -/

/-- `(1 − q)ᴺ ≤ e^{−qN}`, through `1 − q ≤ e^{−q}`, for `q ≤ 1`. -/
theorem one_sub_coe_pow_le_exp {q : ℝ≥0} (hq1 : q ≤ 1) (N : Nat) :
    (1 - (q : ℝ≥0∞)) ^ N ≤ ENNReal.ofReal (Real.exp (-(q * N))) := by
  rw [← ENNReal.coe_one, ← ENNReal.coe_sub, ← ENNReal.coe_pow, ← ENNReal.ofReal_coe_nnreal]
  refine ENNReal.ofReal_le_ofReal ?_
  calc (((1 - q) ^ N : ℝ≥0) : ℝ) = (1 - (q : ℝ)) ^ N := by
        push_cast [NNReal.coe_sub hq1]; rfl
    _ ≤ Real.exp (-q) ^ N :=
        pow_le_pow_left₀ (by have : (q : ℝ) ≤ 1 := hq1; linarith)
          (Real.one_sub_le_exp_neg q) N
    _ = Real.exp (-(q * N)) := by rw [← Real.exp_nat_mul]; ring_nf

/-- `e^{−qN} ≤ δ` as soon as `ln(1/δ) ≤ qN`. -/
theorem exp_neg_le_of_log_le {q δ : ℝ} (hδ : 0 < δ) {N : Nat} (hN : Real.log (1 / δ) ≤ q * N) :
    Real.exp (-(q * N)) ≤ δ := by
  calc Real.exp (-(q * N)) ≤ Real.exp (Real.log δ) := by
        rw [Real.exp_le_exp]
        rw [one_div, Real.log_inv] at hN
        linarith
    _ = δ := Real.exp_log hδ

/-- **The number of draws for a confidence `1 − δ`.** If one draw lands in `E` with probability at
least `q`, then `N ≥ ln(1/δ) / q` draws all miss `E` with probability at most `δ`. -/
theorem prob_vectorOf_miss_le_of_log_le {E : Set α} {q δ : ℝ≥0} (hq : (q : ℝ≥0∞) ≤ prob g E)
    (hδ : 0 < δ) {N : Nat} (hN : Real.log (1 / δ) ≤ q * N) :
    prob (vectorOf N g) {xs | ∀ x ∈ xs, x ∉ E} ≤ δ := by
  refine ((prob_vectorOf_miss_le g hq N).trans
    (one_sub_coe_pow_le_exp (ENNReal.coe_le_one_iff.mp (le_one_of_le_prob g hq)) N)).trans ?_
  rw [← ENNReal.ofReal_coe_nnreal]
  exact ENNReal.ofReal_le_ofReal (exp_neg_le_of_log_le (by exact_mod_cast hδ) hN)

/-- **The number of draws to collect every coupon with confidence `1 − δ`.** If one draw lands in
each `E i`, `i ∈ s`, with probability at least `q`, then after `N ≥ ln(|s|/δ) / q` draws some
`E i` is still missing with probability at most `δ`. -/
theorem prob_vectorOf_someMiss_le_of_log_le {ι : Type} (s : Finset ι) (E : ι → Set α)
    {q δ : ℝ≥0} (hq : ∀ i ∈ s, (q : ℝ≥0∞) ≤ prob g (E i)) (hδ : 0 < δ) {N : Nat}
    (hN : Real.log (s.card / δ) ≤ q * N) :
    prob (vectorOf N g) {xs | ∃ i ∈ s, ∀ x ∈ xs, x ∉ E i} ≤ δ := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨i₀, hi₀⟩
  · refine le_of_eq_of_le ((prob_eq_zero_iff _ _).mpr ?_) (by positivity)
    rintro xs - ⟨i, hi, -⟩
    simp at hi
  have hc : (0 : ℝ) < s.card := by exact_mod_cast Finset.card_pos.mpr ⟨i₀, hi₀⟩
  refine ((prob_vectorOf_someMiss_le g s E (fun _ => (q : ℝ≥0∞)) hq N).trans
    (Finset.sum_le_sum fun i hi => one_sub_coe_pow_le_exp
      (ENNReal.coe_le_one_iff.mp (le_one_of_le_prob g (hq i hi))) N)).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_coe_nnreal]
  refine ENNReal.ofReal_le_ofReal ?_
  have h := exp_neg_le_of_log_le (q := q) (div_pos (by exact_mod_cast hδ) hc) (N := N)
    (by rwa [one_div, inv_div])
  calc (s.card : ℝ) * Real.exp (-(q * N)) ≤ s.card * (δ / s.card) :=
        mul_le_mul_of_nonneg_left h hc.le
    _ = δ := by field_simp

end draws

end SPMF
