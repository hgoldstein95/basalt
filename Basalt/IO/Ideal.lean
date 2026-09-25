/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt.GenRel
import Basalt.IO.SplitMix
import Basalt.SPMF.Expect.Obs
import Basalt.SPMF.Mass
import Basalt.Walk.Attr

/-!
# The Ideal PRNG

`IdealSource` is a source of words that are uniform and independent, and `src.Below y x` says that
`y` at `SPMF` expects no more of any continuation than `x` at `WordModel σ` delivers on it; for a
terminating `y` that makes `x`'s distribution `y`'s (`dist_eq`).
-/

open RandomChoice ENNReal

namespace SPMF

/-- The ideal PRNG: every word uniform. -/
noncomputable def uniformWord : SPMF UInt64 := Nat.toUInt64 <$> chooseNat 0 (2 ^ 64 - 1)

theorem expect_uniformWord (f : UInt64 → ℝ≥0∞) :
    expect uniformWord f = expect (chooseNat 0 (2 ^ 64 - 1)) (f ∘ Nat.toUInt64) :=
  expect_map _ _ _

theorem uniformWord_isPMF : uniformWord.IsPMF := by
  show uniformWord.mass = 1
  rw [← expect_one, expect_uniformWord, expect_chooseNat_zero (by positivity)]
  simp only [Function.comp_apply, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  exact ENNReal.div_self (by simp) (by simp)

end SPMF

/-! ## An ideal word source -/

/-- A word source whose words are ideal: `E` is the expectation over a random state, and from a
random state a word is uniform and the state it leaves is random again, independently of the word.
Of `E` only what the proofs below use is asked, which any lower integral has. A freshly seeded
`SplitMix` is not one; `IO` is read by modeling it as one (`idealized_faithful`). -/
structure IdealSource (σ : Type) [WordSource σ] where
  E : (σ → ℝ≥0∞) → ℝ≥0∞
  const : ∀ c, E (fun _ => c) = c
  add_le : ∀ f g, E f + E g ≤ E (fun s => f s + g s)
  word : ∀ F : UInt64 → σ → ℝ≥0∞,
    E (fun s => F (WordSource.next s).1 (WordSource.next s).2)
      = SPMF.expect SPMF.uniformWord fun w => E (F w)

/-- `x` run from `s`, `G` of the value and the state it leaves, and `0` where it diverges. -/
def WordModel.runE (x : WordModel σ α) (G : α → σ → ℝ≥0∞) (s : σ) : ℝ≥0∞ :=
  match x.run s with
  | some (a, s') => G a s'
  | none => 0

namespace IdealSource

open SPMF

variable {σ : Type} [WordSource σ] (src : IdealSource σ)

/-- Superadditivity gives monotonicity: `g` is `f` plus what is left. -/
theorem mono {f g : σ → ℝ≥0∞} (h : ∀ s, f s ≤ g s) : src.E f ≤ src.E g :=
  calc src.E f ≤ src.E f + src.E (fun s => g s - f s) := le_self_add
    _ ≤ src.E (fun s => f s + (g s - f s)) := src.add_le _ _
    _ = src.E g := congrArg src.E (funext fun s => add_tsub_cancel_of_le (h s))

/-- `y` expects no more of any continuation than `x` delivers on the ideal source. -/
def Below (y : SPMF α) (x : WordModel σ α) : Prop :=
  ∀ G : α → σ → ℝ≥0∞, expect y (fun a => src.E (G a)) ≤ src.E (x.runE G)

@[gen_rule]
theorem below_pure (a : α) : src.Below (Pure.pure a) (Pure.pure a) := fun G => by
  rw [expect_pure]
  rfl

@[gen_rule]
theorem below_bind {y : SPMF α} {x : WordModel σ α} {k' : α → SPMF β} {k : α → WordModel σ β}
    (hk : ∀ a, src.Below (k' a) (k a)) (hx : src.Below y x) : src.Below (y >>= k') (x >>= k) :=
  fun G => by
    rw [expect_bind]
    refine (expect_mono fun a => hk a G).trans ((hx fun a => (k a).runE G).trans (le_of_eq ?_))
    congr 1
    funext s
    simp only [WordModel.runE, StateT.run_bind]
    cases x.run s <;> rfl

@[gen_rule]
theorem below_map {y : SPMF α} {x : WordModel σ α} (f : α → β) (hx : src.Below y x) :
    src.Below (f <$> y) (f <$> x) := by
  rw [← bind_pure_comp, ← bind_pure_comp]
  exact src.below_bind (fun a => src.below_pure (f a)) hx

@[gen_rule]
theorem below_ite {p : Prop} [Decidable p] {y₁ y₂ : SPMF α} {x₁ x₂ : WordModel σ α}
    (h₁ : p → src.Below y₁ x₁) (h₂ : ¬p → src.Below y₂ x₂) :
    src.Below (if p then y₁ else y₂) (if p then x₁ else x₂) :=
  GenRel.ite h₁ h₂

@[gen_rule]
theorem below_dite {p : Prop} [Decidable p] {y₁ : p → SPMF α} {y₂ : ¬p → SPMF α}
    {x₁ : p → WordModel σ α} {x₂ : ¬p → WordModel σ α}
    (h₁ : ∀ h, src.Below (y₁ h) (x₁ h)) (h₂ : ∀ h, src.Below (y₂ h) (x₂ h)) :
    src.Below (if h : p then y₁ h else y₂ h) (if h : p then x₁ h else x₂ h) :=
  GenRel.dite h₁ h₂

@[gen_rule]
theorem below_default (x : WordModel σ α) : src.Below default x := fun G => by
  simp [expect, default_apply]

theorem below_word : src.Below uniformWord fun s => some (WordSource.next s) := fun G =>
  (src.word fun w s => G w s).ge

/-- Fixpoint induction on the `SPMF` side needs nothing of `E`: `expect` is continuous. -/
theorem admissible_below (x : WordModel σ α) :
    Lean.Order.admissible fun y : SPMF α => src.Below y x := by
  intro c hc ih G
  rw [expect_csup]
  exact iSup₂_le fun y hy => ih y hy G

/-- A terminating `y` below `x` is `x`'s distribution on the ideal source: the bound holds for `f`
and for `1 - f`, and on each side the two add up to at most, and to exactly, `1`. -/
theorem expect_eq_of_below {y : SPMF α} {x : WordModel σ α} (h : src.Below y x) (hy : y.IsPMF)
    {f : α → ℝ≥0∞} (hf : ∀ a, f a ≤ 1) : src.E (x.runE fun a _ => f a) = expect y f := by
  have hbelow (g : α → ℝ≥0∞) : expect y g ≤ src.E (x.runE fun a _ => g a) := by
    simpa only [src.const] using h fun a _ => g a
  have hx : src.E (x.runE fun a _ => f a) + src.E (x.runE fun a _ => 1 - f a) ≤ 1 := by
    refine (src.add_le _ _).trans ((src.mono fun s => ?_).trans (src.const 1).le)
    simp only [WordModel.runE]
    cases x.run s with
    | none => simp
    | some p => exact (add_tsub_cancel_of_le (hf p.1)).le
  have hy1 : expect y f + expect y (fun a => 1 - f a) = 1 := by
    rw [← expect_add]
    simp only [add_tsub_cancel_of_le (hf _), expect_one]
    exact hy
  refine le_antisymm ?_ (hbelow f)
  calc src.E (x.runE fun a _ => f a)
      ≤ 1 - src.E (x.runE fun a _ => 1 - f a) :=
        ENNReal.le_sub_of_add_le_right (ne_top_of_le_ne_top one_ne_top (le_of_add_le_right hx)) hx
    _ ≤ 1 - expect y (fun a => 1 - f a) := tsub_le_tsub_left (hbelow _) 1
    _ = expect y f := ENNReal.sub_eq_of_eq_add
        (ne_top_of_le_ne_top one_ne_top (le_of_add_le_right hy1.le)) hy1.symm

private theorem sum_le (s : Finset ι) (f : ι → σ → ℝ≥0∞) :
    ∑ i ∈ s, src.E (f i) ≤ src.E (fun st => ∑ i ∈ s, f i st) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (add_le_add_right ih _).trans (src.add_le _ _)

open Classical in
/-- The distribution of `x`'s value, run from the ideal source. Its mass is at most `1` by `E`'s
finite superadditivity alone, a total mass being the supremum of finite ones. -/
noncomputable def dist (x : WordModel σ α) : SPMF α :=
  ⟨fun a => src.E (x.runE fun b _ => if b = a then 1 else 0), by
    rw [ENNReal.tsum_eq_iSup_sum]
    refine iSup_le fun s => (src.sum_le s _).trans ((src.mono fun st => ?_).trans (src.const 1).le)
    simp only [WordModel.runE]
    cases x.run st with
    | none => simp
    | some p => simp only; rw [Finset.sum_ite_eq]; split <;> simp⟩

/-- On the ideal source, `x` has the distribution of a terminating `y` below it. -/
theorem dist_eq {y : SPMF α} {x : WordModel σ α} (h : src.Below y x) (hy : y.IsPMF) :
    src.dist x = y := by
  classical
  ext a
  refine (src.expect_eq_of_below h hy (f := fun b => if b = a then 1 else 0)
    fun b => by split <;> simp).trans ?_
  convert expect_ite_eq y a

end IdealSource