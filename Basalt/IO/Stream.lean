/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Mathlib.Probability.ProductMeasure
import Basalt.IO.Ideal
import Basalt.IO.Laws

/-!
# Streams of Uniform Words

An infinite stream of independent uniform words is an `IdealSource` (`WordStream.ideal`), so
`IsFaithful`, which quantifies over ideal sources, is not vacuous (`IsFaithful.wordStream`). `E` is
the lower Lebesgue integral, which has what `IdealSource` asks of every function, measurable or not.
-/

open MeasureTheory ENNReal

/-- An infinite stream of words, the state of the ideal source. -/
abbrev WordStream := ℕ → UInt64

namespace WordStream

instance : WordSource WordStream := ⟨fun s => (s 0, fun n => s (n + 1))⟩

local instance : MeasurableSpace UInt64 := ⊤

local instance : DiscreteMeasurableSpace UInt64 := ⟨fun _ => trivial⟩

/-- The law of one word: `uniformWord`, as a measure. -/
private noncomputable def wordLaw : Measure UInt64 :=
  Measure.sum fun w => SPMF.uniformWord w • Measure.dirac w

private instance : IsProbabilityMeasure wordLaw := ⟨by
  rw [wordLaw, Measure.sum_apply _ MeasurableSet.univ]
  simp only [Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  exact SPMF.mass_uniformWord⟩

/-- The law of the stream: every word independent and uniform. -/
private noncomputable def law : Measure WordStream := Measure.infinitePi fun _ : ℕ => wordLaw

private instance : IsProbabilityMeasure law :=
  inferInstanceAs (IsProbabilityMeasure (Measure.infinitePi _))

/-- A word, then a stream. -/
private def cons (p : UInt64 × WordStream) : WordStream
  | 0 => p.1
  | n + 1 => p.2 n

/-- Splitting off the first word. -/
private def consEquiv : UInt64 × WordStream ≃ᵐ WordStream where
  toFun := cons
  invFun s := (s 0, fun n => s (n + 1))
  left_inv _ := rfl
  right_inv s := funext fun n => by cases n <;> rfl
  measurable_toFun := measurable_pi_iff.mpr fun n => by
    cases n with
    | zero => exact measurable_fst
    | succ n => exact (measurable_pi_apply (X := fun _ : ℕ => UInt64) n).comp measurable_snd
  measurable_invFun := (measurable_pi_apply (X := fun _ : ℕ => UInt64) 0).prodMk
    (measurable_pi_iff.mpr fun n => measurable_pi_apply (X := fun _ : ℕ => UInt64) (n + 1))

private theorem measurableEmbedding_cons : MeasurableEmbedding cons := consEquiv.measurableEmbedding

private theorem preimage_cons_pi (s : Finset ℕ) (t : ℕ → Set UInt64) :
    cons ⁻¹' (Set.pi ↑s t) = (if 0 ∈ s then t 0 else Set.univ) ×ˢ
      Set.pi ↑(s.preimage Nat.succ Nat.succ_injective.injOn) fun n => t (n + 1) := by
  ext ⟨w, u⟩
  simp only [Set.mem_preimage, Set.mem_pi, Finset.mem_coe, Set.mem_prod, Finset.mem_preimage]
  constructor
  · intro h
    refine ⟨?_, fun n hn => h (n + 1) hn⟩
    split
    · exact h 0 ‹_›
    · trivial
  · rintro ⟨h0, h⟩ (_ | n) hn
    · simp only [hn, ite_true] at h0
      exact h0
    · exact h n hn

private theorem prod_split (s : Finset ℕ) (g : ℕ → ℝ≥0∞) :
    ∏ i ∈ s, g i = (if 0 ∈ s then g 0 else 1) *
      ∏ n ∈ s.preimage Nat.succ Nat.succ_injective.injOn, g (n + 1) := by
  classical
  rw [show (∏ n ∈ s.preimage Nat.succ Nat.succ_injective.injOn, g (n + 1))
      = ∏ n ∈ s.preimage Nat.succ Nat.succ_injective.injOn, g (Nat.succ n) from rfl,
    Finset.prod_preimage', ← Finset.prod_filter_mul_prod_filter_not s (· ∈ Set.range Nat.succ),
    mul_comm]
  congr 1
  have : s.filter (· ∉ Set.range Nat.succ) = s.filter (· = 0) := by
    ext x
    cases x <;> simp
  rw [this, Finset.filter_eq']
  split <;> simp

/-- The law of a stream is that of its first word and, independently, the rest. -/
private theorem map_cons : (wordLaw.prod law).map cons = law := by
  refine Measure.eq_infinitePi _ fun s t ht => ?_
  rw [Measure.map_apply measurableEmbedding_cons.measurable
      (MeasurableSet.pi s.countable_toSet fun i _ => ht i), preimage_cons_pi,
    Measure.prod_prod, law, Measure.infinitePi_pi _ fun i _ => ht (i + 1),
    prod_split s fun i => wordLaw (t i)]
  split <;> simp

/-- Streams of independent uniform words: the ideal source. -/
noncomputable def ideal : IdealSource WordStream where
  E f := ∫⁻ s, f s ∂law
  const c := by simp
  add_le f g := le_lintegral_add f g
  word F := by
    show ∫⁻ s, F (s 0) (fun n => s (n + 1)) ∂law = _
    conv_lhs => rw [← map_cons]
    rw [measurableEmbedding_cons.lintegral_map]
    change ∫⁻ p, F p.1 p.2 ∂(wordLaw.prod law) = _
    rw [wordLaw, Measure.prod_sum_left, lintegral_sum_measure]
    simp only [Measure.prod_smul_left, lintegral_smul_measure, Measure.dirac_prod,
      (measurableEmbedding_prodMk_left _).lintegral_map, smul_eq_mul]
    rfl

end WordStream

/-- A faithful generator, run on a stream of uniform words, has its `SPMF` distribution. -/
theorem IsFaithful.wordStream {α : Type} {gen : {G : Type → Type} → [Gen G] → G α}
    (h : IsFaithful gen) :
    WordStream.ideal.dist (gen (G := WordModel WordStream)) = gen (G := SPMF) :=
  h.dist WordStream.ideal
