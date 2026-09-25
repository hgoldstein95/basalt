/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt.SPMF.Basic

/-!
# Expected Values and Event Probabilities

`SPMF.expect` (the expected value of an `ℝ≥0∞`-valued function under a generator) and `SPMF.prob`
(the probability of an event): their monad equations, their order and support properties, and
continuity of `expect` along a chain. Every other fact about a distribution is read off these.
-/

open Lean.Order RandomChoice NNReal ENNReal

namespace SPMF

section expect

/-- The expected value of `f` under `p`. `mass` is the special case `f = 1`. -/
noncomputable def expect (p : SPMF α) (f : α → ℝ≥0∞) : ℝ≥0∞ := ∑' a, p a * f a

@[simp]
theorem expect_pure (a : α) (f : α → ℝ≥0∞) :
    expect (Pure.pure a : SPMF α) f = f a := by
  unfold expect
  rw [tsum_eq_single a]
  · simp
  · intro a' ha'
    simp [ha']

/-- The tower rule. -/
theorem expect_bind (x : SPMF α) (g : α → SPMF β) (f : β → ℝ≥0∞) :
    expect (x >>= g) f = expect x (fun a => expect (g a) f) := by
  unfold expect
  simp only [bind_apply]
  calc ∑' b, (∑' a, x a * g a b) * f b
      = ∑' b, ∑' a, x a * (g a b * f b) := by
        congr 1; ext b
        rw [← ENNReal.tsum_mul_right]
        congr 1; ext a
        rw [mul_assoc]
    _ = ∑' a, ∑' b, x a * (g a b * f b) := ENNReal.tsum_comm
    _ = ∑' a, x a * ∑' b, g a b * f b := by
        congr 1; ext a
        rw [ENNReal.tsum_mul_left]

theorem expect_map (x : SPMF α) (h : α → β) (f : β → ℝ≥0∞) :
    expect (h <$> x) f = expect x (f ∘ h) := by
  rw [← LawfulMonad.bind_pure_comp, expect_bind]
  simp only [expect_pure]
  rfl

@[simp]
theorem expect_one (p : SPMF α) : expect p (fun _ => 1) = p.mass := by
  unfold expect mass; simp

theorem expect_const (p : SPMF α) (c : ℝ≥0∞) :
    expect p (fun _ => c) = p.mass * c := by
  unfold expect mass
  rw [← ENNReal.tsum_mul_right]

theorem expect_mono {p : SPMF α} {f g : α → ℝ≥0∞} (h : ∀ a, f a ≤ g a) :
    expect p f ≤ expect p g :=
  ENNReal.tsum_le_tsum fun a => by gcongr; exact h a

theorem expect_mono_support {p : SPMF α} {f g : α → ℝ≥0∞}
    (h : ∀ a ∈ p.support, f a ≤ g a) : expect p f ≤ expect p g := by
  unfold expect
  refine ENNReal.tsum_le_tsum fun a => ?_
  by_cases ha : a ∈ p.support
  · exact mul_le_mul_right (h a ha) _
  · rw [(apply_eq_zero_iff p a).mpr ha]
    simp

theorem expect_add (p : SPMF α) (f g : α → ℝ≥0∞) :
    expect p (fun a => f a + g a) = expect p f + expect p g := by
  unfold expect
  rw [← ENNReal.tsum_add]
  congr 1; ext a; rw [mul_add]

theorem expect_mul_left (p : SPMF α) (c : ℝ≥0∞) (f : α → ℝ≥0∞) :
    expect p (fun a => c * f a) = c * expect p f := by
  unfold expect
  rw [← ENNReal.tsum_mul_left]
  congr 1; ext a; ring

/-- Off-support values of `f` don't matter, so a `sound_complete` law lets `f` be understood on
valid values only. -/
theorem expect_congr_support {p : SPMF α} {f g : α → ℝ≥0∞}
    (h : ∀ a ∈ p.support, f a = g a) : expect p f = expect p g := by
  unfold expect
  refine tsum_congr fun a => ?_
  by_cases ha : a ∈ p.support
  · rw [h a ha]
  · rw [(apply_eq_zero_iff p a).mpr ha, zero_mul, zero_mul]

theorem expect_le_of_support {p : SPMF α} {f : α → ℝ≥0∞} {c : ℝ≥0∞}
    (h : ∀ a ∈ p.support, f a ≤ c) : expect p f ≤ c :=
  calc expect p f ≤ expect p (fun _ => c) := expect_mono_support h
    _ = p.mass * c := expect_const p c
    _ ≤ 1 * c := mul_le_mul_left (mass_le_one p) c
    _ = c := one_mul c

/-- The transfer from expectations to supports. -/
theorem expect_pos_iff {p : SPMF α} {f : α → ℝ≥0∞} :
    0 < expect p f ↔ ∃ a ∈ p.support, 0 < f a := by
  unfold expect
  rw [pos_iff_ne_zero, ne_eq, ENNReal.tsum_eq_zero, not_forall]
  constructor
  · rintro ⟨a, ha⟩
    have := mul_ne_zero_iff.mp ha
    exact ⟨a, this.1, pos_iff_ne_zero.mpr this.2⟩
  · rintro ⟨a, ha, hf⟩
    exact ⟨a, mul_ne_zero ha hf.ne'⟩

end expect

section prob

/-- The probability that a draw from `p` lands in `E`. -/
noncomputable def prob (p : SPMF α) (E : Set α) : ℝ≥0∞ := expect p (E.indicator 1)

theorem prob_eq_tsum_ite (p : SPMF α) (E : Set α) [DecidablePred (· ∈ E)] :
    prob p E = ∑' a, if a ∈ E then p a else 0 := by
  unfold prob expect
  refine tsum_congr fun a => ?_
  by_cases h : a ∈ E <;> simp [Set.indicator, h]

@[simp]
theorem prob_singleton (p : SPMF α) (a : α) : prob p {a} = p a := by
  unfold prob expect
  rw [tsum_eq_single a]
  · simp [Set.indicator]
  · intro b hb
    simp [Set.indicator, hb]

theorem expect_ite_eq [DecidableEq α] (p : SPMF α) (a : α) :
    expect p (fun b => if b = a then 1 else 0) = p a := by
  unfold expect
  rw [tsum_eq_single a fun b hb => by simp [hb]]
  simp

/-- Distributions agree when their expectations do. -/
theorem ext_expect {p q : SPMF α} (h : ∀ f, expect p f = expect q f) : p = q := by
  ext a
  rw [← prob_singleton, ← prob_singleton]
  exact h _

theorem prob_pure (a : α) (E : Set α) [Decidable (a ∈ E)] :
    prob (Pure.pure a : SPMF α) E = if a ∈ E then 1 else 0 := by
  unfold prob
  rw [expect_pure]
  by_cases h : a ∈ E <;> simp [Set.indicator, h]

/-- The law of total probability. -/
theorem prob_bind (x : SPMF α) (g : α → SPMF β) (E : Set β) :
    prob (x >>= g) E = expect x (fun a => prob (g a) E) := by
  unfold prob
  rw [expect_bind]

theorem prob_le_mass (p : SPMF α) (E : Set α) : prob p E ≤ p.mass := by
  rw [← expect_one]
  refine expect_mono fun a => ?_
  by_cases h : a ∈ E <;> simp [Set.indicator, h]

theorem prob_mono {p : SPMF α} {E F : Set α} (h : E ⊆ F) : prob p E ≤ prob p F := by
  refine expect_mono fun a => ?_
  by_cases ha : a ∈ E
  · simp [Set.indicator, ha, h ha]
  · simp [Set.indicator, ha]

/-- Zero probability is a support statement, so the `mem_support_*_iff` lemmas discharge it. -/
theorem prob_eq_zero_iff (p : SPMF α) (E : Set α) :
    prob p E = 0 ↔ ∀ a ∈ p.support, a ∉ E := by
  unfold prob expect
  rw [ENNReal.tsum_eq_zero]
  constructor
  · intro h a ha hE
    have := h a
    rw [mul_eq_zero] at this
    rcases this with h0 | h0
    · exact ha h0
    · simp [Set.indicator, hE] at h0
  · intro h a
    by_cases ha : a ∈ p.support
    · simp [Set.indicator, h a ha]
    · rw [(apply_eq_zero_iff p a).mpr ha, zero_mul]

/-- Markov's inequality, product form. -/
theorem mul_prob_le_expect (p : SPMF α) (f : α → ℝ≥0∞) (c : ℝ≥0∞) :
    c * prob p {a | c ≤ f a} ≤ expect p f := by
  unfold prob
  rw [← expect_mul_left]
  refine expect_mono fun a => ?_
  by_cases h : c ≤ f a
  · simp [Set.indicator, h]
  · simp [Set.indicator, h]

/-- Markov's inequality, division form. -/
theorem prob_le_expect_div (p : SPMF α) (f : α → ℝ≥0∞) {c : ℝ≥0∞}
    (hc0 : c ≠ 0) (hct : c ≠ ⊤) :
    prob p {a | c ≤ f a} ≤ expect p f / c := by
  rw [ENNReal.le_div_iff_mul_le (Or.inl hc0) (Or.inl hct), mul_comm]
  exact mul_prob_le_expect p f c

theorem mem_support_iff_prob_pos {p : SPMF α} {a : α} : a ∈ p.support ↔ 0 < prob p {a} := by
  rw [prob_singleton]
  exact (apply_pos_iff p a).symm

end prob

section continuity

/-- `expect` is continuous along a chain. -/
theorem expect_csup {c : SPMF α → Prop} (hc : chain c) (f : α → ℝ≥0∞) :
    expect (CCPO.csup hc) f = ⨆ p, ⨆ (_ : c p), expect p f := by
  refine le_antisymm ?_ (iSup₂_le fun p hp => ENNReal.tsum_le_tsum fun a =>
    mul_le_mul_left (le_csup hc hp a) _)
  calc expect (CCPO.csup hc) f
      = ∑' a, (⨆ p, ⨆ (_ : c p), p a) * f a := by
        unfold expect
        exact tsum_congr fun a => by rw [csup_apply hc a]
    _ = ∑' a, ⨆ p, ⨆ (_ : c p), p a * f a := by
        refine tsum_congr fun a => ?_
        rw [ENNReal.iSup_mul]
        congr 1
        ext p
        rw [ENNReal.iSup_mul]
    _ = ⨆ s : Finset α, ∑ a ∈ s, ⨆ p, ⨆ (_ : c p), p a * f a := ENNReal.tsum_eq_iSup_sum
    _ ≤ ⨆ s : Finset α, ⨆ p, ⨆ (_ : c p), ∑ a ∈ s, p a * f a := by
        refine iSup_mono fun s => ?_
        simp_rw [iSup_subtype']
        rw [ENNReal.finsetSum_iSup]
        intro ⟨p, hp⟩ ⟨q, hq⟩
        rcases hc p q hp hq with h | h
        · exact ⟨⟨q, hq⟩, fun a => ⟨mul_le_mul_left (h a) _, le_rfl⟩⟩
        · exact ⟨⟨p, hp⟩, fun a => ⟨le_rfl, mul_le_mul_left (h a) _⟩⟩
    _ ≤ ⨆ p, ⨆ (_ : c p), expect p f := by
        refine iSup_le fun s => iSup₂_mono fun p hp => ?_
        exact ENNReal.sum_le_tsum s

/-- Only *upper* bounds on expectations are admissible: the fixpoint iteration starts at `⊥`,
where every expectation is `0`, so a lower bound cannot ride `fix_induct` — prove exact laws by
inducting on an index of the event instead (`prob_listOf_length`). -/
theorem admissible_expect_le (f : α → ℝ≥0∞) (B : ℝ≥0∞) :
    admissible (fun (p : SPMF α) => expect p f ≤ B) := by
  intro c hc ih
  rw [expect_csup]
  exact iSup₂_le ih

end continuity

end SPMF
