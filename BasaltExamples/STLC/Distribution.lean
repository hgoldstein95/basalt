/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt
import BasaltExamples.STLC.Cost
import BasaltExamples.STLC.GenTermSized

/-!
# Comparing `genTerm` and `genTermSized`

The two STLC generators' distributions, compared on two events a test suite wants rare: a *trivial*
term (a literal under abstractions) and a *vacuous* abstraction (one that ignores its argument).
Each bound holds at every size, context, and type it quantifies over; `genTerm.not_cost_bounded`
sets `genTermSized.cost_bounded` against the absence of any worst-case bound on `genTerm`.
-/

open RandomChoice
open scoped ENNReal

/-- A Boolean literal under zero or more abstractions: a term with no variable and no application,
and so a constant function of its arguments. `genZero` produces exactly these. -/
def Term.IsTrivial : Term → Prop
  | .Bool _ => True
  | .Abs _ e => e.IsTrivial
  | _ => False

/-- The event that a generated term is trivial. -/
def trivialTerms : Set Term := {e | e.IsTrivial}

/-! ## One branch at a time -/

theorem genZero.trivial : IsSoundFor (genZero Γ τ) Term.IsTrivial := by
  induction τ generalizing Γ with
  | Bool => rw [IsSoundFor.iff_obs, genZero]; walk <;> trivial
  | Fun τ1 τ2 _ ih2 => rw [IsSoundFor.iff_obs, genZero]; walk [ih2.obs]; simpa [Term.IsTrivial]

theorem genZero.prob_trivial : SPMF.prob (genZero Γ τ) trivialTerms = 1 := by
  rw [SPMF.prob_eq_mass_of_support (E := trivialTerms) fun e he => genZero.trivial e he]
  exact genZero.terminates

theorem genBool.prob_trivial : SPMF.prob (genBool : SPMF Term) trivialTerms = 1 := by
  have h := genZero.prob_trivial (Γ := []) (τ := .Bool)
  rwa [genZero] at h

theorem prob_trivial_app (x : SPMF Ty) (f g : Ty → SPMF Term) :
    SPMF.prob (x >>= fun a => f a >>= fun e1 => g a >>= fun e2 => pure (Term.App e1 e2))
      trivialTerms = 0 := by
  rw [SPMF.prob_eq_zero_iff]
  intro e he
  support_simp at he
  obtain ⟨_, _, _, _, _, _, rfl⟩ := he
  simp [trivialTerms, Term.IsTrivial]

theorem prob_trivial_elements (hne : varsWithType Γ τ ≠ []) :
    SPMF.prob (elements (varsWithType Γ τ) hne) trivialTerms = 0 := by
  refine (SPMF.prob_eq_zero_iff _ _).2 ((IsSoundFor.iff_obs (P := (· ∉ trivialTerms))).2 ?_)
  walk
  simp only [varsWithType, List.mem_filterMap] at *
  obtain ⟨⟨τ', i⟩, _, h⟩ := ‹∃ _, _›
  split at h <;> simp at h
  subst h
  simp [trivialTerms, Term.IsTrivial]

theorem prob_trivial_abs (x : SPMF Term) (τ : Ty) :
    SPMF.prob (x >>= fun e => pure (Term.Abs τ e)) trivialTerms = SPMF.prob x trivialTerms := by
  rw [SPMF.prob_bind]
  unfold SPMF.prob
  congr 1
  ext e
  rw [SPMF.expect_pure]
  by_cases h : e.IsTrivial <;> simp [trivialTerms, Set.indicator, Term.IsTrivial, h]

/-! ## `genTerm` -/

theorem genTerm.prob_trivial_bool (h : varsWithType Γ .Bool = []) :
    SPMF.prob (genTerm Γ .Bool) trivialTerms = 2 / 3 := by
  rw [genTerm]
  simp only [h, ne_eq, not_true_eq_false, ↓reduceDIte, oneOfWith_eq]
  rw [SPMF.prob_oneOf]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
    List.length_nil, genZero.prob_trivial, genBool.prob_trivial, prob_trivial_app]
  norm_num

theorem genTerm.prob_trivial_bool_of_var (h : varsWithType Γ .Bool ≠ []) :
    SPMF.prob (genTerm Γ .Bool) trivialTerms = 1 / 2 := by
  rw [genTerm]
  simp only [h, ne_eq, not_false_eq_true, ↓reduceDIte, oneOfWith_eq]
  rw [SPMF.prob_oneOf]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
    List.length_nil, genZero.prob_trivial, genBool.prob_trivial, prob_trivial_app,
    prob_trivial_elements]
  ennreal_to_real; norm_num

theorem genTerm.prob_trivial_closed_fun :
    SPMF.prob (genTerm [] (.Fun .Bool .Bool)) trivialTerms = 1 / 2 := by
  rw [genTerm]
  simp only [varsWithType, List.zipIdx_nil, List.filterMap_nil, ne_eq, not_true_eq_false,
    ↓reduceDIte, oneOfWith_eq]
  rw [SPMF.prob_oneOf]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
    List.length_nil, genZero.prob_trivial, prob_trivial_app, prob_trivial_abs,
    genTerm.prob_trivial_bool_of_var (Γ := [.Bool]) (by decide)]
  ennreal_to_real; norm_num

/-- At every context and type, a quarter of `genTerm`'s terms or more are trivial: its `genZero`
branch is always one of at most four. -/
theorem genTerm.quarter_le_prob_trivial : 1 / 4 ≤ SPMF.prob (genTerm Γ τ) trivialTerms := by
  cases τ <;> rw [genTerm] <;> split <;> simp only [oneOfWith_eq] <;>
    rw [SPMF.prob_oneOf] <;>
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil, genZero.prob_trivial] <;> norm_num
  all_goals rw [← one_div]; exact ENNReal.div_le_div le_self_add (by norm_num)

/-! ## `genTermSized` -/

theorem genTermSized.prob_trivial_bool (h : varsWithType Γ .Bool = []) :
    SPMF.prob (genTermSized (n + 1) Γ .Bool) trivialTerms = 1 / 5 := by
  rw [genTermSized]
  simp only [h, ne_eq, not_true_eq_false, ↓reduceDIte, frequencyWith_eq]
  rw [SPMF.prob_frequency]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, genBool.prob_trivial,
    prob_trivial_app]
  ennreal_to_real; norm_num

theorem genTermSized.prob_trivial_bool_of_var (h : varsWithType Γ .Bool ≠ []) :
    SPMF.prob (genTermSized (n + 1) Γ .Bool) trivialTerms = 1 / 7 := by
  rw [genTermSized]
  simp only [h, ne_eq, not_false_eq_true, ↓reduceDIte, frequencyWith_eq]
  rw [SPMF.prob_frequency]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, genBool.prob_trivial,
    prob_trivial_app, prob_trivial_elements]
  ennreal_to_real; norm_num

theorem genTermSized.prob_trivial_closed_fun :
    SPMF.prob (genTermSized (n + 2) [] (.Fun .Bool .Bool)) trivialTerms = 1 / 21 := by
  rw [genTermSized]
  simp only [varsWithType, List.zipIdx_nil, List.filterMap_nil, ne_eq, not_true_eq_false,
    ↓reduceDIte, frequencyWith_eq]
  rw [SPMF.prob_frequency]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, prob_trivial_app,
    prob_trivial_abs, genTermSized.prob_trivial_bool_of_var (Γ := [.Bool]) (by decide)]
  ennreal_to_real; norm_num

theorem genTermSized.prob_trivial_le_third :
    SPMF.prob (genTermSized (n + 1) Γ τ) trivialTerms ≤ 1 / 3 := by
  cases τ with
  | Bool =>
    by_cases h : varsWithType Γ .Bool = []
    · rw [genTermSized.prob_trivial_bool h]; ennreal_to_real; norm_num
    · rw [genTermSized.prob_trivial_bool_of_var h]; ennreal_to_real; norm_num
  | Fun τ1 τ2 =>
    have hq := SPMF.prob_le_one (genTermSized n (τ1 :: Γ) τ2) trivialTerms
    rw [genTermSized]
    split <;> simp only [frequencyWith_eq] <;> rw [SPMF.prob_frequency] <;>
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, prob_trivial_app,
        prob_trivial_abs, prob_trivial_elements]
    all_goals
      generalize SPMF.prob (genTermSized n (τ1 :: Γ) τ2) trivialTerms = q at hq ⊢
      have hq' := hq
      ennreal_to_real at hq'
      ennreal_to_real
      norm_num
      linarith

/-- From size `2` on, at most a fifth of `genTermSized`'s terms are trivial, at every context and
type: below `genTerm`'s quarter (`genTerm.quarter_le_prob_trivial`). -/
theorem genTermSized.prob_trivial_le :
    SPMF.prob (genTermSized (n + 2) Γ τ) trivialTerms ≤ 1 / 5 := by
  cases τ with
  | Bool =>
    by_cases h : varsWithType Γ .Bool = []
    · rw [genTermSized.prob_trivial_bool h]
    · rw [genTermSized.prob_trivial_bool_of_var h]; ennreal_to_real; norm_num
  | Fun τ1 τ2 =>
    have hq := genTermSized.prob_trivial_le_third (n := n) (Γ := τ1 :: Γ) (τ := τ2)
    rw [genTermSized]
    split <;> simp only [frequencyWith_eq] <;> rw [SPMF.prob_frequency] <;>
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, prob_trivial_app,
        prob_trivial_abs, prob_trivial_elements]
    all_goals
      generalize SPMF.prob (genTermSized (n + 1) (τ1 :: Γ) τ2) trivialTerms = q at hq ⊢
      have hq1 : q ≤ 1 := hq.trans (by norm_num)
      have hq' := hq
      ennreal_to_real at hq'
      ennreal_to_real
      norm_num
      linarith

/-! ## Vacuous abstractions -/

/-- Whether de Bruijn variable `i` occurs free in a term. -/
def Term.Mentions : Term → Nat → Prop
  | .Var j, i => j = i
  | .Bool _, _ => False
  | .App e1 e2, i => e1.Mentions i ∨ e2.Mentions i
  | .Abs _ e, i => e.Mentions (i + 1)

/-- An abstraction whose body never refers to its argument. -/
def Term.IsVacuousAbs : Term → Prop
  | .Abs _ e => ¬ e.Mentions 0
  | _ => False

/-- The event that a generated term is a vacuous abstraction. -/
def vacuousAbs : Set Term := {e | e.IsVacuousAbs}

theorem Term.IsTrivial.not_mentions {e : Term} (h : e.IsTrivial) (i : Nat) : ¬ e.Mentions i := by
  induction e generalizing i with
  | Bool => simp [Term.Mentions]
  | Abs _ e ih => exact ih h (i + 1)
  | Var | App => exact h.elim

theorem prob_vacuous_abs (x : SPMF Term) (τ : Ty) :
    SPMF.prob (x >>= fun e => pure (Term.Abs τ e)) vacuousAbs
      = SPMF.prob x {e | ¬ e.Mentions 0} := by
  rw [SPMF.prob_bind]
  unfold SPMF.prob
  congr 1
  ext e
  rw [SPMF.expect_pure]
  by_cases h : e.Mentions 0 <;> simp [vacuousAbs, Set.indicator, Term.IsVacuousAbs, h]

theorem prob_vacuous_app (x : SPMF Ty) (f g : Ty → SPMF Term) :
    SPMF.prob (x >>= fun a => f a >>= fun e1 => g a >>= fun e2 => pure (Term.App e1 e2))
      vacuousAbs = 0 := by
  rw [SPMF.prob_eq_zero_iff]
  intro e he
  support_simp at he
  obtain ⟨_, _, _, _, _, _, rfl⟩ := he
  simp [vacuousAbs, Term.IsVacuousAbs]

theorem prob_le_prob_not_mentions (x : SPMF Term) :
    SPMF.prob x trivialTerms ≤ SPMF.prob x {e | ¬ e.Mentions 0} :=
  SPMF.prob_mono fun _ h => Term.IsTrivial.not_mentions h 0

/-- At least half of `genTerm`'s closed functions on `Bool` are abstractions that ignore their
argument. -/
theorem genTerm.half_le_prob_vacuous :
    1 / 2 ≤ SPMF.prob (genTerm [] (.Fun .Bool .Bool)) vacuousAbs := by
  have hzero : 1 ≤ SPMF.prob (genZero [.Bool] .Bool) {e | ¬ e.Mentions 0} :=
    genZero.prob_trivial.symm.le.trans (prob_le_prob_not_mentions _)
  have hbody : 1 / 2 ≤ SPMF.prob (genTerm [.Bool] .Bool) {e | ¬ e.Mentions 0} :=
    (genTerm.prob_trivial_bool_of_var (by decide)).symm.le.trans (prob_le_prob_not_mentions _)
  rw [genTerm]
  simp only [varsWithType, List.zipIdx_nil, List.filterMap_nil, ne_eq, not_true_eq_false,
    ↓reduceDIte, oneOfWith_eq]
  rw [SPMF.prob_oneOf, genZero]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
    List.length_nil, prob_vacuous_app, prob_vacuous_abs, zero_add, add_zero]
  rw [show ((0 + 1 + 1 + 1 : ℕ) : ℝ≥0∞) = 3 by norm_num]
  calc (1 : ℝ≥0∞) / 2 = (1 + 1 / 2) / 3 := by ennreal_to_real; norm_num
    _ ≤ _ := by gcongr

theorem genTermSized.prob_not_mentions_le :
    SPMF.prob (genTermSized (n + 1) [.Bool] .Bool) {e | ¬ e.Mentions 0} ≤ 5 / 7 := by
  have hvar : SPMF.prob (elements (varsWithType [.Bool] .Bool) (by decide))
      {e | ¬ e.Mentions 0} = 0 := by
    refine (SPMF.prob_eq_zero_iff _ _).2 ((IsSoundFor.iff_obs (P := (· ∉ _))).2 ?_)
    walk
    simp_all [varsWithType, Term.Mentions]
  rw [genTermSized]
  simp only [show varsWithType [.Bool] .Bool ≠ [] by decide, ne_eq, not_false_eq_true,
    ↓reduceDIte, frequencyWith_eq]
  rw [SPMF.prob_frequency]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hvar]
  calc _ ≤ ((2 : ℕ) * 0 + ((4 : ℕ) * 1 + ((1 : ℕ) * 1 + 0)))
          / ((2 + (4 + (1 + 0)) : ℕ) : ℝ≥0∞) := by
        gcongr <;> exact SPMF.prob_le_one _ _
    _ = 5 / 7 := by norm_num

/-- At most `5/21` of `genTermSized`'s closed functions on `Bool` ignore their argument, against at
least half of `genTerm`'s (`genTerm.half_le_prob_vacuous`). -/
theorem genTermSized.prob_vacuous_le :
    SPMF.prob (genTermSized (n + 2) [] (.Fun .Bool .Bool)) vacuousAbs ≤ 5 / 21 := by
  have hbody := genTermSized.prob_not_mentions_le (n := n)
  rw [genTermSized]
  simp only [varsWithType, List.zipIdx_nil, List.filterMap_nil, ne_eq, not_true_eq_false,
    ↓reduceDIte, frequencyWith_eq]
  rw [SPMF.prob_frequency]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, prob_vacuous_app,
    prob_vacuous_abs]
  calc _ ≤ ((4 : ℕ) * 0 + ((2 : ℕ) * (5 / 7) + 0)) / ((4 + (2 + 0) : ℕ) : ℝ≥0∞) := by gcongr
    _ = 5 / 21 := by ennreal_to_real; norm_num

/-! ## Cost -/

/-- No number of choices bounds every run of `genTerm`: a bound would bound its expected cost too,
which has none (`genTerm.not_expected_cost_bounded`). Compare `genTermSized.cost_bounded`. -/
theorem genTerm.not_cost_bounded (N : Nat) : ¬ IsCostBounded (genTerm Γ τ) (fun _ => N) := by
  intro h
  refine genTerm.not_expected_cost_bounded (Γ := Γ) (τ := τ) (B := N) (by simp) ?_
  exact (IsExpectedCostBounded.of_costBounded genTerm.cost_faithful h).mono
    (SPMF.expect_le_of_support fun _ _ => le_rfl)
