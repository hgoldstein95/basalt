/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein, Ernest Ng
-/
module

public import Basalt
public import BasaltExamples.STLC.Termination

/-!
# How Many Tests Until `genTerm` Produces a Shape

This file bounds how often three shapes appear in one draw of `genTerm [] (Bool → Bool)`, and then
how many draws a test needs to see them, at most and at least. -/

@[expose] public section

open RandomChoice
open scoped ENNReal NNReal

namespace STLC

/-! ## Shapes of terms -/

/-- The number of uses of the de Bruijn variable `k` in a term. -/
def Term.uses (k : Nat) : Term → Nat
  | .Bool _ => 0
  | .Var n => if n = k then 1 else 0
  | .App a b => Term.uses k a + Term.uses k b
  | .Abs _ b => Term.uses (k + 1) b

/-- A term is **linear** when every variable that a lambda binds is used exactly once in that
lambda's body. Variables of the context are unconstrained. -/
def Term.isLinear : Term → _root_.Bool
  | .Bool _ => true
  | .Var _ => true
  | .App a b => Term.isLinear a && Term.isLinear b
  | .Abs _ b => Term.uses 0 b == 1 && Term.isLinear b

/-- The terms that use their bound variables linearly. -/
def IsLinear : Set Term := {t | t.isLinear = true}

/-- A lambda at the root that ignores its argument. -/
def DiscardsArg : Set Term := {t | ∃ τ b, t = .Abs τ b ∧ b.uses 0 = 0}

/-- An application at the root. -/
def IsApp : Set Term := {t | ∃ a b, t = .App a b}

/-! ## The per-draw bounds -/

/-- The per-draw lower bound for a linear term: the introduction branch (`1/3`) with the body `#0`
(`1/4`). -/
noncomputable def linearBound : ℝ≥0 := 1 / 12

/-- The per-draw lower bound for a lambda that ignores its argument: `genZero` (`1/3`), and half
of the introduction branch (`1/3 · 1/2`). -/
noncomputable def discardsArgBound : ℝ≥0 := 1 / 2

/-- The per-draw probability of an application: the application branch (`1/3`). -/
noncomputable def isAppBound : ℝ≥0 := 1 / 3

/-! ## One draw of `genTerm` -/

/-- A Boolean literal. -/
def IsBoolLit : Set Term := {t | ∃ b, t = .Bool b}

theorem genBool_prob_boolLit : SPMF.prob (genBool : SPMF Term) IsBoolLit = 1 := by
  have h : ∀ t ∈ SPMF.support (genBool : SPMF Term), t ∈ IsBoolLit := by
    intro t ht
    unfold genBool at ht
    simp only [SPMF.mem_support_map_iff] at ht
    obtain ⟨b, -, rfl⟩ := ht
    exact ⟨b, rfl⟩
  rw [SPMF.prob_eq_mass_of_subset h]
  exact (genZero.terminates (Γ := [Ty.Bool]) (τ := .Bool))

/-- The three branches of `genTerm [] (Bool → Bool)`, each with probability `1/3`. -/
theorem genTerm_fun_prob_eq (E : Set Term) :
    SPMF.prob (genTerm [] (.Fun .Bool .Bool)) E
      = (SPMF.prob (genZero [] (.Fun .Bool .Bool) : SPMF Term) E
        + (SPMF.prob (do
              let argTy ← genType
              let e1 ← genTerm [] (argTy.Fun (Ty.Bool.Fun Ty.Bool))
              let e2 ← genTerm [] argTy
              pure (e1.App e2) : SPMF Term) E
          + (SPMF.prob (do
                let e ← genTerm [Ty.Bool] Ty.Bool
                pure (Term.Abs Ty.Bool e) : SPMF Term) E + 0))) / 3 := by
  conv_lhs => rw [genTerm]
  simp only [show varsWithType [] (Ty.Fun .Bool .Bool) = [] from rfl, ne_eq, not_true_eq_false,
    dite_false, oneOfWith_eq, SPMF.prob_oneOf]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
    List.length_nil]
  norm_num

/-- **A linear term.** One draw of `genTerm [] (Bool → Bool)` is linear with probability at least
`1/12`: the introduction branch (`1/3`) with the body `#0` (`1/4`), which is `λx. x`. -/
theorem genTerm_prob_linear_ge :
    (linearBound : ℝ≥0∞) ≤ SPMF.prob (genTerm [] (.Fun .Bool .Bool)) IsLinear := by
  rw [show (linearBound : ℝ≥0∞) = 1 / 12 by
    rw [linearBound, ENNReal.coe_div (by norm_num)]; simp, genTerm_fun_prob_eq]
  have habs : (1 : ℝ≥0∞) / 4 ≤ SPMF.prob (do
      let e ← genTerm [Ty.Bool] Ty.Bool
      pure (Term.Abs Ty.Bool e) : SPMF Term) IsLinear := by
    refine le_trans ?_ (SPMF.prob_bind_ge {Term.Var 0} (d := 1) fun e he => ?_)
    · rw [mul_one]
      -- In the context `[Bool]` at `Bool`, `#0` is one branch of four.
      rw [genTerm]
      have hv : varsWithType [Ty.Bool] Ty.Bool = [Term.Var 0] := rfl
      simp only [hv, ne_eq, List.cons_ne_nil, not_false_eq_true, dite_true, oneOfWith_eq,
        SPMF.prob_oneOf]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
        List.length_nil]
      have h1 : SPMF.prob (elements [Term.Var 0] (List.cons_ne_nil _ _) : SPMF Term)
          {Term.Var 0} = 1 := by
        unfold SPMF.prob; rw [SPMF.expect_elements]; simp
      rw [h1, show ((0 + 1 + 1 + 1 + 1 : ℕ) : ℝ≥0∞) = 4 by norm_num]
      refine ENNReal.div_le_div_right ?_ _
      exact le_trans (le_add_right le_rfl) le_add_self
    · rw [Set.mem_singleton_iff.mp he, SPMF.prob_pure_of_mem]
      rfl
  calc (1 : ℝ≥0∞) / 12 = 1 / 4 / 3 := by
        simp only [div_eq_mul_inv, one_mul]
        rw [← ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num))]
        norm_num
    _ ≤ _ := ENNReal.div_le_div_right
        (le_add_left (le_add_left (by rw [add_zero]; exact habs))) _

/-- **A lambda that ignores its argument.** One draw of `genTerm [] (Bool → Bool)` is `λx. b` for
a literal `b` with probability at least `1/2`: always under `genZero` (`1/3`), and at least half
the time under the introduction branch (`1/3 · 1/2`). -/
theorem genTerm_prob_discardsArg_ge :
    (discardsArgBound : ℝ≥0∞) ≤ SPMF.prob (genTerm [] (.Fun .Bool .Bool)) DiscardsArg := by
  rw [show (discardsArgBound : ℝ≥0∞) = 1 / 2 by
    rw [discardsArgBound, ENNReal.coe_div (by norm_num)]; simp, genTerm_fun_prob_eq]
  have hlit : ∀ e ∈ IsBoolLit, (1 : ℝ≥0∞) ≤
      SPMF.prob (Pure.pure (Term.Abs Ty.Bool e) : SPMF Term) DiscardsArg := by
    rintro e ⟨b, rfl⟩
    rw [SPMF.prob_pure_of_mem (show Term.Abs Ty.Bool (.Bool b) ∈ DiscardsArg from
      ⟨Ty.Bool, _, rfl, rfl⟩)]
  have hzero : 1 ≤ SPMF.prob (genZero [] (.Fun .Bool .Bool) : SPMF Term) DiscardsArg := by
    rw [show (genZero [] (.Fun .Bool .Bool) : SPMF Term)
        = (do let e ← genZero [Ty.Bool] Ty.Bool; pure (Term.Abs Ty.Bool e)) from rfl]
    refine le_trans ?_ (SPMF.prob_bind_ge IsBoolLit hlit)
    rw [show genZero [Ty.Bool] Ty.Bool = (genBool : SPMF Term) from rfl, genBool_prob_boolLit,
      mul_one]
  have habs : (1 : ℝ≥0∞) / 2 ≤ SPMF.prob (do
      let e ← genTerm [Ty.Bool] Ty.Bool
      pure (Term.Abs Ty.Bool e) : SPMF Term) DiscardsArg := by
    refine le_trans ?_ (SPMF.prob_bind_ge IsBoolLit hlit)
    rw [mul_one]
    -- In the context `[Bool]` at `Bool`, two of the four branches are `genBool`.
    rw [genTerm]
    have hv : varsWithType [Ty.Bool] Ty.Bool = [Term.Var 0] := rfl
    simp only [hv, ne_eq, List.cons_ne_nil, not_false_eq_true, dite_true, oneOfWith_eq,
      SPMF.prob_oneOf]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil]
    rw [show genZero [Ty.Bool] Ty.Bool = (genBool : SPMF Term) from rfl, genBool_prob_boolLit,
      show ((0 + 1 + 1 + 1 + 1 : ℕ) : ℝ≥0∞) = 4 by norm_num]
    calc (1 : ℝ≥0∞) / 2 = (1 + 1) / 4 := by
          rw [ENNReal.div_eq_div_iff (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
          norm_num
      _ ≤ _ := by
          refine ENNReal.div_le_div_right (add_le_add le_rfl ?_) _
          exact le_add_left (le_add_left (by rw [add_zero]))
  calc (1 : ℝ≥0∞) / 2 = (1 + 1 / 2) / 3 := by
        rw [ENNReal.div_eq_div_iff (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
        rw [mul_add, mul_one, ENNReal.mul_div_cancel (by norm_num) (by norm_num)]
        norm_num
    _ ≤ _ := ENNReal.div_le_div_right
        (add_le_add hzero (le_add_left (by rw [add_zero]; exact habs))) _

/-- **An application, exactly.** One draw of `genTerm [] (Bool → Bool)` is an application with
probability exactly `isAppBound`: the application branch produces nothing else and terminates, and
the other two branches produce lambdas. -/
theorem genTerm_prob_isApp_eq :
    SPMF.prob (genTerm [] (.Fun .Bool .Bool)) IsApp = isAppBound := by
  -- Every draw of the application branch is an application, and the branch terminates.
  have happ :
    SPMF.prob (do
      let argTy ← genType
      let e1 ← genTerm [] (argTy.Fun (Ty.Bool.Fun Ty.Bool))
      let e2 ← genTerm [] argTy
      pure (e1.App e2) : SPMF Term) IsApp = 1 := by
    refine le_antisymm ((SPMF.prob_le_mass _ _).trans (SPMF.mass_le_one _)) ?_
    refine le_trans ?_ (SPMF.prob_bind_ge Set.univ (d := 1) fun argTy _ => ?_)
    · rw [SPMF.prob_univ, genType.terminates, mul_one]
    refine le_trans ?_ (SPMF.prob_bind_ge Set.univ (d := 1) fun e1 _ => ?_)
    · rw [SPMF.prob_univ, genTerm.terminates, mul_one]
    refine le_trans ?_ (SPMF.prob_bind_ge Set.univ (d := 1) fun e2 _ => ?_)
    · rw [SPMF.prob_univ, genTerm.terminates, mul_one]
    rw [SPMF.prob_pure_of_mem (show Term.App e1 e2 ∈ IsApp from ⟨e1, e2, rfl⟩)]
  rw [show (isAppBound : ℝ≥0∞) = 1 / 3 by
    rw [isAppBound, ENNReal.coe_div (by norm_num)]; simp, genTerm_fun_prob_eq, happ]
  have hzero : SPMF.prob (genZero [] (.Fun .Bool .Bool) : SPMF Term) IsApp = 0 := by
    rw [SPMF.prob_eq_zero_iff]
    intro t ht
    rw [show (genZero [] (.Fun .Bool .Bool) : SPMF Term)
        = (do let e ← genZero [Ty.Bool] Ty.Bool; pure (Term.Abs Ty.Bool e)) from rfl] at ht
    support_simp at ht
    obtain ⟨e, -, rfl⟩ := ht
    rintro ⟨a, b, h⟩
    cases h
  have habs : SPMF.prob (do
      let e ← genTerm [Ty.Bool] Ty.Bool
      pure (Term.Abs Ty.Bool e) : SPMF Term) IsApp = 0 := by
    rw [SPMF.prob_eq_zero_iff]
    intro t ht
    support_simp at ht
    obtain ⟨e, -, rfl⟩ := ht
    rintro ⟨a, b, h⟩
    cases h
  rw [hzero, habs]
  simp

/-! ## How many tests -/

/-- **Tests until a linear term, with confidence `1 − δ`**: `N ≥ ln(1/δ) / linearBound` draws of
`genTerm [] (Bool → Bool)` are all non-linear with probability at most `δ`. -/
theorem genTerm_linear_within {δ : ℝ≥0} (hδ : 0 < δ) {N : Nat}
    (hN : Real.log (1 / δ) ≤ linearBound * N) :
    SPMF.prob (vectorOf N (genTerm [] (.Fun .Bool .Bool) : SPMF Term))
      {ts | ∀ t ∈ ts, t ∉ IsLinear} ≤ δ :=
  SPMF.prob_vectorOf_miss_le_of_log_le _ genTerm_prob_linear_ge hδ hN

/-- **Expected tests until a linear term**: the sum that reads as the expected number of tests
(`Basalt.SPMF.Expect.Draws`) is at most `1 / linearBound`. -/
theorem genTerm_linear_expected_le :
    ∑' N, SPMF.prob (vectorOf N (genTerm [] (.Fun .Bool .Bool) : SPMF Term))
      {ts | ∀ t ∈ ts, t ∉ IsLinear} ≤ (linearBound : ℝ≥0∞)⁻¹ :=
  SPMF.tsum_prob_vectorOf_miss_le _ genTerm_prob_linear_ge

/-- The three shapes. -/
def shapes : Fin 3 → Set Term := ![IsLinear, DiscardsArg, IsApp]

/-- Their per-draw bounds. -/
noncomputable def shapeBounds : Fin 3 → ℝ≥0 := ![linearBound, discardsArgBound, isAppBound]

theorem shapeBounds_le (i : Fin 3) :
    (shapeBounds i : ℝ≥0∞) ≤ SPMF.prob (genTerm [] (.Fun .Bool .Bool)) (shapes i) := by
  fin_cases i
  · exact genTerm_prob_linear_ge
  · exact genTerm_prob_discardsArg_ge
  · exact genTerm_prob_isApp_eq.ge

/-- The event that some shape is missing from every term of a list. -/
def SomeShapeMissing : Set (List Term) := {ts | ∃ i, ∀ t ∈ ts, t ∉ shapes i}

theorem someShapeMissing_eq :
    SomeShapeMissing = {ts | ∃ i ∈ (Finset.univ : Finset (Fin 3)), ∀ t ∈ ts, t ∉ shapes i} := by
  ext ts; simp [SomeShapeMissing]

/-- **Tests until all three shapes, with confidence `1 − δ`**: after
`N ≥ ln(3/δ) / linearBound` draws of `genTerm [] (Bool → Bool)`, some shape is still missing with
probability at most `δ`. The `3` is the number of shapes. -/
theorem genTerm_all_shapes_within {δ : ℝ≥0} (hδ : 0 < δ) {N : Nat}
    (hN : Real.log (Fintype.card (Fin 3) / δ) ≤ linearBound * N) :
    SPMF.prob (vectorOf N (genTerm [] (.Fun .Bool .Bool) : SPMF Term)) SomeShapeMissing ≤ δ := by
  rw [someShapeMissing_eq]
  refine SPMF.prob_vectorOf_someMiss_le_of_log_le _ Finset.univ shapes
    (fun i _ => ?_) hδ (by rwa [Finset.card_univ])
  -- `linearBound` is the smallest of the three bounds, so it bounds every shape's probability.
  refine le_trans (ENNReal.coe_le_coe.mpr ?_) (shapeBounds_le i)
  fin_cases i <;> simp only [shapeBounds, linearBound, discardsArgBound, isAppBound] <;>
    first
    | exact le_rfl
    | (rw [← NNReal.coe_le_coe]; push_cast; norm_num)

/-- **Expected tests until all three shapes**: the sum that reads as the expected number of tests
(`Basalt.SPMF.Expect.Draws`) is at most `∑ᵢ 1 / shapeBounds i`. -/
theorem genTerm_all_shapes_expected_le :
    ∑' N, SPMF.prob (vectorOf N (genTerm [] (.Fun .Bool .Bool) : SPMF Term)) SomeShapeMissing
      ≤ ∑ i, (shapeBounds i : ℝ≥0∞)⁻¹ := by
  rw [someShapeMissing_eq]
  exact SPMF.tsum_prob_vectorOf_someMiss_le _ Finset.univ shapes _ (fun i _ => shapeBounds_le i)

/-! ## How many tests, at least -/

/-- The per-draw upper bound for a linear term: a lambda that ignores its argument is not linear. -/
noncomputable def linearUpperBound : ℝ≥0 := 1 - discardsArgBound

theorem disjoint_linear_discardsArg : Disjoint IsLinear DiscardsArg := by
  rw [Set.disjoint_left]
  rintro t ht ⟨τ, b, rfl, hb⟩
  simp [IsLinear, Term.isLinear, hb] at ht

theorem genTerm_prob_linear_le :
    SPMF.prob (genTerm [] (.Fun .Bool .Bool)) IsLinear ≤ linearUpperBound := by
  refine (SPMF.prob_le_one_sub_of_disjoint _ disjoint_linear_discardsArg).trans ?_
  rw [linearUpperBound, ENNReal.coe_sub, ENNReal.coe_one]
  exact tsub_le_tsub_left genTerm_prob_discardsArg_ge 1

theorem linearUpperBound_lt_one : linearUpperBound < 1 :=
  tsub_lt_self one_pos (by norm_num [discardsArgBound])

/-- **Tests a linear term needs, with confidence `p`**: `N` draws of `genTerm [] (Bool → Bool)`
include a linear term with probability at least `p` only when
`N ≥ ln(1/(1 − p)) / ln(1/(1 − linearUpperBound))`. -/
theorem genTerm_linear_needs {p : ℝ≥0} {N : Nat}
    (hp : (p : ℝ≥0∞) ≤ SPMF.prob (vectorOf N (genTerm [] (.Fun .Bool .Bool) : SPMF Term))
      {ts | ∃ t ∈ ts, t ∈ IsLinear}) :
    Real.log (1 / (1 - p)) ≤ N * Real.log (1 / (1 - linearUpperBound)) :=
  SPMF.log_le_of_le_prob_vectorOf_hit _ genTerm.terminates genTerm_prob_linear_le
    linearUpperBound_lt_one hp

/-- **Expected tests until a linear term, from below**: the sum that reads as the expected number
of tests (`Basalt.SPMF.Expect.Draws`) is at least `1 / linearUpperBound`. -/
theorem genTerm_linear_expected_ge :
    (linearUpperBound : ℝ≥0∞)⁻¹
      ≤ ∑' N, SPMF.prob (vectorOf N (genTerm [] (.Fun .Bool .Bool) : SPMF Term))
        {ts | ∀ t ∈ ts, t ∉ IsLinear} :=
  SPMF.inv_le_tsum_prob_vectorOf_miss _ genTerm.terminates genTerm_prob_linear_le

theorem isAppBound_lt_one : isAppBound < 1 := by
  rw [isAppBound, ← NNReal.coe_lt_coe]; push_cast; norm_num

/-- **Tests an application needs, with confidence `p`**: `N` draws of `genTerm [] (Bool → Bool)`
include an application with probability at least `p` only when
`N ≥ ln(1/(1 − p)) / ln(1/(1 − isAppBound))`. Since `isAppBound` is exact, so is this. -/
theorem genTerm_app_needs {p : ℝ≥0} {N : Nat}
    (hp : (p : ℝ≥0∞) ≤ SPMF.prob (vectorOf N (genTerm [] (.Fun .Bool .Bool) : SPMF Term))
      {ts | ∃ t ∈ ts, t ∈ IsApp}) :
    Real.log (1 / (1 - p)) ≤ N * Real.log (1 / (1 - isAppBound)) :=
  SPMF.log_le_of_le_prob_vectorOf_hit _ genTerm.terminates genTerm_prob_isApp_eq.le
    isAppBound_lt_one hp

/-- **Expected tests until an application, from below**: at least `1 / isAppBound`, which with
`genTerm_prob_isApp_eq` and `tsum_prob_vectorOf_miss_le` makes it exact. -/
theorem genTerm_app_expected_ge :
    (isAppBound : ℝ≥0∞)⁻¹
      ≤ ∑' N, SPMF.prob (vectorOf N (genTerm [] (.Fun .Bool .Bool) : SPMF Term))
        {ts | ∀ t ∈ ts, t ∉ IsApp} :=
  SPMF.inv_le_tsum_prob_vectorOf_miss _ genTerm.terminates genTerm_prob_isApp_eq.le

/-- The event that every shape appears in a list. -/
def AllShapesSeen : Set (List Term) := {ts | ∀ i, ∃ t ∈ ts, t ∈ shapes i}

/-- **Tests all three shapes need, with confidence `p`**: `N` draws of `genTerm [] (Bool → Bool)`
include every shape with probability at least `p` only when
`N ≥ ln(1/(1 − p)) / ln(1/(1 − isAppBound))`: they must at least include an application, the
shape with the smallest per-draw upper bound. -/
theorem genTerm_all_shapes_needs {p : ℝ≥0} {N : Nat}
    (hp : (p : ℝ≥0∞)
      ≤ SPMF.prob (vectorOf N (genTerm [] (.Fun .Bool .Bool) : SPMF Term)) AllShapesSeen) :
    Real.log (1 / (1 - p)) ≤ N * Real.log (1 / (1 - isAppBound)) := by
  refine SPMF.log_le_of_le_prob_vectorOf_allHit _ genTerm.terminates (s := Finset.univ)
    (E := shapes) (Finset.mem_univ 2) genTerm_prob_isApp_eq.le isAppBound_lt_one ?_
  convert hp using 2
  ext ts; simp [AllShapesSeen]

/-- **Expected tests until all three shapes, from below**: the sum that reads as the expected
number of tests (`Basalt.SPMF.Expect.Draws`) is at least `1 / isAppBound`. -/
theorem genTerm_all_shapes_expected_ge :
    (isAppBound : ℝ≥0∞)⁻¹
      ≤ ∑' N, SPMF.prob (vectorOf N (genTerm [] (.Fun .Bool .Bool) : SPMF Term))
        SomeShapeMissing := by
  rw [someShapeMissing_eq]
  exact SPMF.inv_le_tsum_prob_vectorOf_someMiss _ genTerm.terminates (Finset.mem_univ 2)
    genTerm_prob_isApp_eq.le

end STLC
