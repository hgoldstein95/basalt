/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt.Obs.Ordered
import Basalt.SPMF.Expect.Obs

/-!
# Bounding an Average

The walker's rules for the shapes of choice in `Mix.average`, in both directions: the average of
bounds bounds the average. They are shared by every judgment about an expectation, at either
interpretation.
-/

open ENNReal

instance : SPMF.expectObs.Monotone := ⟨fun _ _ _ h => SPMF.expect_mono h⟩

namespace Mix

theorem average_mix_mono {lo hi : Nat} {F F' : ULift.{u} {x : Nat // lo ≤ x ∧ x ≤ hi} → ℝ≥0∞}
    (h : ∀ a, F a ≤ F' a) : Mix.average.mix lo hi F ≤ Mix.average.mix lo hi F' :=
  ENNReal.tsum_le_tsum fun a => by gcongr; exact h a

private theorem binary_average' (c d : ℝ≥0∞) :
    Mix.average.mix.{u} 0 1 (fun a => if (a.down.val == 0) = true then c else d)
      = (1/2 : ℝ≥0∞) * c + (1/2 : ℝ≥0∞) * d :=
  (binary_average _).trans (by simp)

private theorem sum_weighted_le {γ : Type v} {F : γ → ℝ≥0∞} {cs gs}
    (h : Weighted (· ≤ ·) F cs gs) :
    (gs.map fun p => (p.1 : ℝ≥0∞) * F p.2).sum ≤ (cs.map fun p => (p.1 : ℝ≥0∞) * p.2).sum := by
  induction h with
  | nil => simp
  | cons hc _ ih => simpa using add_le_add (by gcongr) ih

private theorem le_sum_weighted {γ : Type v} {F : γ → ℝ≥0∞} {cs gs}
    (h : Weighted (· ≥ ·) F cs gs) :
    (cs.map fun p => (p.1 : ℝ≥0∞) * p.2).sum ≤ (gs.map fun p => (p.1 : ℝ≥0∞) * F p.2).sum := by
  induction h with
  | nil => simp
  | cons hc _ ih => simpa using add_le_add (by gcongr) ih

private theorem select_average' {γ : Type v} (l : List (Nat × γ))
    (hpos : 0 < (l.map Prod.fst).sum) (F : γ → ℝ≥0∞) (d : ℝ≥0∞) :
    (Mix.average.{u}).select l hpos F d
      = (l.map fun p => (p.1 : ℝ≥0∞) * F p.2).sum / (((l.map Prod.fst).sum : ℕ) : ℝ≥0∞) := by
  have h := select_average (l.map fun p : Nat × γ => (p.1, F p.2)) (T := (l.map Prod.fst).sum)
    (by simp [Function.comp_def]) hpos d
  rw [List.map_map] at h
  exact h

private theorem rangeInt_average {lo hi : ℤ} (h : lo ≤ hi) (d : ℤ → ℝ≥0∞) :
    (Mix.average.{0}).rangeInt lo hi h d
      = (∑ x ∈ Finset.Icc lo hi, d x) / (((hi - lo + 1).toNat : ℕ) : ℝ≥0∞) :=
  (congrFun (SPMF.expectObs.map_chooseInt lo hi h) d).symm.trans (SPMF.expect_chooseInt h d)

private theorem rangeInt_mono {lo hi : ℤ} {h : lo ≤ hi} {F d : ℤ → ℝ≥0∞}
    (hF : ∀ x, lo ≤ x ∧ x ≤ hi → F x ≤ d x) :
    (Mix.average.{0}).rangeInt lo hi h F ≤ (Mix.average.{0}).rangeInt lo hi h d :=
  average_mix_mono fun a => hF _ ⟨by omega, by have := a.down.property.2; omega⟩

private theorem average_const {lo hi : Nat} (h : lo ≤ hi) (d : ℝ≥0∞) :
    Mix.average.mix.{u} lo hi (fun _ => d) = d := by
  rw [range_average lo hi fun _ => d, Finset.sum_const, SPMF.card_Icc_eq lo hi h, nsmul_eq_mul,
    mul_comm, ENNReal.mul_div_cancel_right (by simp) (by simp)]

private theorem rangeInt_const {lo hi : ℤ} (h : lo ≤ hi) (d : ℝ≥0∞) :
    (Mix.average.{0}).rangeInt lo hi h (fun _ => d) = d :=
  average_const (Nat.zero_le _) d

private theorem element_const {γ : Type v} (l : List γ) (hne : l ≠ []) (d : ℝ≥0∞) :
    (Mix.average.{u}).element l hne (fun _ => d) = d :=
  average_const (Nat.zero_le _) d

/-! ## Upper bounds

A rule for a constant comes first: a draw whose postexpectation does not depend on the value drawn
has that bound, not an average of copies of it. It is stated for a postexpectation that is
syntactically constant, and not with a premise, so that it cannot capture a sub-generator's bound
that depends on the draw. -/

@[gen_rule]
theorem average_range_le_const {lo hi : Nat} {h : lo ≤ hi} {d : ℝ≥0∞} :
    (Mix.average.{u}).range lo hi h (fun _ => d) ≤ d := (average_const h d).le

@[gen_rule]
theorem average_range_le {lo hi : Nat} {h : lo ≤ hi}
    {F : ULift.{u} {x : Nat // lo ≤ x ∧ x ≤ hi} → ℝ≥0∞}
    {d : Nat → ℝ≥0∞} (hF : ∀ x (hx : lo ≤ x ∧ x ≤ hi), F ⟨⟨x, hx⟩⟩ ≤ d x) :
    Mix.average.range lo hi h F
      ≤ (∑ x ∈ Finset.Icc lo hi, d x) / ((hi - lo + 1 : ℕ) : ℝ≥0∞) :=
  (average_mix_mono fun a => hF a.down.val a.down.property).trans (range_average lo hi d).le

@[gen_rule]
theorem average_binary_le {t e c d : ℝ≥0∞} (ht : t ≤ c) (he : e ≤ d) :
    (Mix.average.{u}).binary t e ≤ (1/2 : ℝ≥0∞) * c + (1/2 : ℝ≥0∞) * d :=
  (average_mix_mono fun _ => by split <;> assumption).trans (binary_average' c d).le

@[gen_rule]
theorem average_threshold_le {d : Nat} {k : ℤ} {t e c c' : ℝ≥0∞} (hd : 0 < d) (h0 : 0 ≤ k)
    (hk : k ≤ d) (ht : t ≤ c) (he : e ≤ c') :
    (Mix.average.{u}).threshold d k t e
      ≤ (k.toNat : ℝ≥0∞) / (d : ℝ≥0∞) * c + ((d - k.toNat : ℕ) : ℝ≥0∞) / (d : ℝ≥0∞) * c' :=
  (average_mix_mono fun _ => by split <;> assumption).trans (threshold_average hd h0 hk c c').le

@[gen_rule]
theorem average_index_le {γ : Type v} {l : List γ} {hne : l ≠ []} {F : γ → ℝ≥0∞}
    {cs : List ℝ≥0∞} (h : List.Forall₂ (fun c g => F g ≤ c) cs l) :
    (Mix.average.{u}).index l hne F ≤ cs.sum / (cs.length : ℝ≥0∞) := by
  have hsum : (l.map F).sum ≤ cs.sum := by
    clear hne
    induction h with
    | nil => simp
    | cons hc _ ih => simpa using add_le_add hc ih
  rw [h.length_eq]
  exact (index_average l hne F).le.trans (ENNReal.div_le_div_right hsum _)

@[gen_rule]
theorem average_element_le_const {γ : Type v} {l : List γ} {hne : l ≠ []} {d : ℝ≥0∞} :
    (Mix.average.{u}).element l hne (fun _ => d) ≤ d := (element_const l hne d).le

@[gen_rule]
theorem average_element_le {γ : Type v} {l : List γ} {hne : l ≠ []} {F : γ → ℝ≥0∞} :
    (Mix.average.{u}).element l hne F ≤ (l.map F).sum / (l.length : ℝ≥0∞) :=
  (index_average l hne F).le

@[gen_rule]
theorem average_select_le {γ : Type v} {l : List (Nat × γ)} {hpos : 0 < (l.map Prod.fst).sum}
    {F : γ → ℝ≥0∞} {d : ℝ≥0∞} {cs : List (Nat × ℝ≥0∞)} (h : Weighted (· ≤ ·) F cs l) :
    (Mix.average.{u}).select l hpos F d
      ≤ (cs.map fun p => (p.1 : ℝ≥0∞) * p.2).sum / ((cs.map Prod.fst).sum : ℝ≥0∞) := by
  rw [h.weights, select_average']
  exact ENNReal.div_le_div_right (sum_weighted_le h) _

@[gen_rule]
theorem average_rangeInt_le_const {lo hi : ℤ} {h : lo ≤ hi} {d : ℝ≥0∞} :
    (Mix.average.{0}).rangeInt lo hi h (fun _ => d) ≤ d := (rangeInt_const h d).le

@[gen_rule]
theorem average_rangeInt_le {lo hi : ℤ} {h : lo ≤ hi} {F d : ℤ → ℝ≥0∞}
    (hF : ∀ x, lo ≤ x ∧ x ≤ hi → F x ≤ d x) :
    (Mix.average.{0}).rangeInt lo hi h F
      ≤ (∑ x ∈ Finset.Icc lo hi, d x) / (((hi - lo + 1).toNat : ℕ) : ℝ≥0∞) :=
  (rangeInt_mono hF).trans (rangeInt_average h d).le

/-! ## Lower bounds -/

@[gen_rule]
theorem le_average_range_const {lo hi : Nat} {h : lo ≤ hi} {d : ℝ≥0∞} :
    d ≤ (Mix.average.{u}).range lo hi h (fun _ => d) := (average_const h d).ge

@[gen_rule]
theorem le_average_range {lo hi : Nat} {h : lo ≤ hi}
    {F : ULift.{u} {x : Nat // lo ≤ x ∧ x ≤ hi} → ℝ≥0∞}
    {d : Nat → ℝ≥0∞} (hF : ∀ x (hx : lo ≤ x ∧ x ≤ hi), d x ≤ F ⟨⟨x, hx⟩⟩) :
    (∑ x ∈ Finset.Icc lo hi, d x) / ((hi - lo + 1 : ℕ) : ℝ≥0∞)
      ≤ Mix.average.range lo hi h F :=
  (range_average lo hi d).ge.trans (average_mix_mono fun a => hF a.down.val a.down.property)

@[gen_rule]
theorem le_average_binary {t e c d : ℝ≥0∞} (ht : c ≤ t) (he : d ≤ e) :
    (1/2 : ℝ≥0∞) * c + (1/2 : ℝ≥0∞) * d ≤ (Mix.average.{u}).binary t e :=
  (binary_average' c d).ge.trans (average_mix_mono fun _ => by split <;> assumption)

@[gen_rule]
theorem le_average_threshold {d : Nat} {k : ℤ} {t e c c' : ℝ≥0∞} (hd : 0 < d) (h0 : 0 ≤ k)
    (hk : k ≤ d) (ht : c ≤ t) (he : c' ≤ e) :
    (k.toNat : ℝ≥0∞) / (d : ℝ≥0∞) * c + ((d - k.toNat : ℕ) : ℝ≥0∞) / (d : ℝ≥0∞) * c'
      ≤ (Mix.average.{u}).threshold d k t e :=
  (threshold_average hd h0 hk c c').ge.trans (average_mix_mono fun _ => by split <;> assumption)

@[gen_rule]
theorem le_average_index {γ : Type v} {l : List γ} {hne : l ≠ []} {F : γ → ℝ≥0∞}
    {cs : List ℝ≥0∞} (h : List.Forall₂ (fun c g => c ≤ F g) cs l) :
    cs.sum / (cs.length : ℝ≥0∞) ≤ (Mix.average.{u}).index l hne F := by
  have hsum : cs.sum ≤ (l.map F).sum := by
    clear hne
    induction h with
    | nil => simp
    | cons hc _ ih => simpa using add_le_add hc ih
  rw [h.length_eq]
  exact (ENNReal.div_le_div_right hsum _).trans (index_average l hne F).ge

@[gen_rule]
theorem le_average_element_const {γ : Type v} {l : List γ} {hne : l ≠ []} {d : ℝ≥0∞} :
    d ≤ (Mix.average.{u}).element l hne (fun _ => d) := (element_const l hne d).ge

@[gen_rule]
theorem le_average_element {γ : Type v} {l : List γ} {hne : l ≠ []} {F : γ → ℝ≥0∞} :
    (l.map F).sum / (l.length : ℝ≥0∞) ≤ (Mix.average.{u}).element l hne F :=
  (index_average l hne F).ge

@[gen_rule]
theorem le_average_select {γ : Type v} {l : List (Nat × γ)} {hpos : 0 < (l.map Prod.fst).sum}
    {F : γ → ℝ≥0∞} {d : ℝ≥0∞} {cs : List (Nat × ℝ≥0∞)} (h : Weighted (· ≥ ·) F cs l) :
    (cs.map fun p => (p.1 : ℝ≥0∞) * p.2).sum / ((cs.map Prod.fst).sum : ℝ≥0∞)
      ≤ (Mix.average.{u}).select l hpos F d := by
  rw [h.weights, select_average']
  exact ENNReal.div_le_div_right (le_sum_weighted h) _

@[gen_rule]
theorem le_average_rangeInt_const {lo hi : ℤ} {h : lo ≤ hi} {d : ℝ≥0∞} :
    d ≤ (Mix.average.{0}).rangeInt lo hi h (fun _ => d) := (rangeInt_const h d).ge

@[gen_rule]
theorem le_average_rangeInt {lo hi : ℤ} {h : lo ≤ hi} {F d : ℤ → ℝ≥0∞}
    (hF : ∀ x, lo ≤ x ∧ x ≤ hi → d x ≤ F x) :
    (∑ x ∈ Finset.Icc lo hi, d x) / (((hi - lo + 1).toNat : ℕ) : ℝ≥0∞)
      ≤ (Mix.average.{0}).rangeInt lo hi h F :=
  (rangeInt_average h d).ge.trans (rangeInt_mono hF)

end Mix
