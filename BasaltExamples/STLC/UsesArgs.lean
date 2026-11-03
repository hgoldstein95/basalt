/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein, Ernest Ng
-/
module

public import Basalt
public import BasaltExamples.STLC.NumDraws

/-!
# How Many Tests Until `genTerm` Uses Its Arguments

This file bounds how often one draw of `genTerm` at `Bool → Bool` and at `Bool → Bool → Bool` is a
function whose body mentions every argument, and then how many draws a test needs to see one. -/

@[expose] public section

open RandomChoice
open scoped ENNReal NNReal

namespace STLC

/-! ## Functions that use their arguments -/

/-- `absN [τ₁, …, τₙ] b` is `λ:τ₁. … λ:τₙ. b`. -/
def Term.absN : List Ty → Term → Term
  | [], b => b
  | τ :: τs, b => .Abs τ (Term.absN τs b)

/-- An `n`-argument function that **uses its arguments**: `n` lambdas at the root whose body
mentions every variable they bind. This is the per-parameter usage of Frank, Quiring, and
Lampropoulos, "Generating Well-Typed Terms That Are Not 'Useless'" (POPL 2024), §4.2, demanded of
all `n` parameters. -/
def UsesArgs (n : Nat) : Set Term :=
  {t | ∃ τs b, τs.length = n ∧ t = Term.absN τs b ∧ ∀ k < n, 0 < b.uses k}

/-- The per-draw lower bound at `Bool → Bool`: the introduction branch (`1/3`) with the body `#0`
(`1/4`). -/
noncomputable def usesArgs1Bound : ℝ≥0 := 1 / 12

/-- The per-draw lower bound at `Bool → Bool → Bool`: two introduction branches (`1/3 · 1/3`), then
a body `(λy. #k) #j` that mentions both arguments: the application branch (`1/4`) at argument type
`Bool` (`1/2`), a function `λy. #1` or `λy. #2` (`1/3 · 1/4 · 2/3`), and the argument it lacks
(`1/4 · 1/2`). -/
noncomputable def usesArgs2Bound : ℝ≥0 := 1 / 10368

/-! ## The branches of `genTerm` -/

/-- With a variable of type `τ` in scope, `genTerm Γ τ` takes the variable branch a quarter of the
time. -/
theorem genTerm_prob_ge_var {Γ : Ctx} {τ : Ty} (h : varsWithType Γ τ ≠ []) (E : Set Term) :
    SPMF.prob (elements (varsWithType Γ τ) h : SPMF Term) E / 4 ≤ SPMF.prob (genTerm Γ τ) E := by
  conv_rhs => rw [genTerm.eq_def]
  simp only [ne_eq, h, not_false_eq_true, dite_true, oneOfWith_eq, SPMF.prob_oneOf]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
    List.length_nil, show ((0 + 1 + 1 + 1 + 1 : ℕ) : ℝ≥0∞) = 4 by norm_num]
  exact ENNReal.div_le_div_right (le_add_left (le_add_right le_rfl)) _

/-- With a variable of type `τ` in scope, `genTerm Γ τ` takes the application branch a quarter of
the time. -/
theorem genTerm_prob_ge_app {Γ : Ctx} {τ : Ty} (h : varsWithType Γ τ ≠ []) (E : Set Term) :
    SPMF.prob (do
        let argTy ← genType
        let e1 ← genTerm Γ (argTy.Fun τ)
        let e2 ← genTerm Γ argTy
        pure (e1.App e2) : SPMF Term) E / 4
      ≤ SPMF.prob (genTerm Γ τ) E := by
  conv_rhs => rw [genTerm.eq_def]
  simp only [ne_eq, h, not_false_eq_true, dite_true, oneOfWith_eq, SPMF.prob_oneOf]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
    List.length_nil, show ((0 + 1 + 1 + 1 + 1 : ℕ) : ℝ≥0∞) = 4 by norm_num]
  exact ENNReal.div_le_div_right (le_add_left (le_add_left (le_add_right le_rfl))) _

/-- With no variable of a function type in scope, `genTerm` takes the introduction branch a third of
the time. -/
theorem genTerm_prob_ge_abs {Γ : Ctx} {τ1 τ2 : Ty} (h : varsWithType Γ (.Fun τ1 τ2) = [])
    (E : Set Term) :
    SPMF.prob (do
        let e ← genTerm (τ1 :: Γ) τ2
        pure (Term.Abs τ1 e) : SPMF Term) E / 3
      ≤ SPMF.prob (genTerm Γ (.Fun τ1 τ2)) E := by
  conv_rhs => rw [genTerm]
  simp only [ne_eq, h, not_true_eq_false, dite_false, oneOfWith_eq, SPMF.prob_oneOf]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
    List.length_nil, show ((0 + 1 + 1 + 1 : ℕ) : ℝ≥0∞) = 3 by norm_num, add_zero]
  exact ENNReal.div_le_div_right (le_add_left le_add_self) _

/-- The introduction branch, read through the body: `λ:τ1. e` lands in `E` when `e` lands in `B`. -/
theorem prob_abs_ge {Γ : Ctx} {τ1 τ2 : Ty} {E B : Set Term} (hB : ∀ e ∈ B, Term.Abs τ1 e ∈ E) :
    SPMF.prob (genTerm (τ1 :: Γ) τ2) B
      ≤ SPMF.prob (do
          let e ← genTerm (τ1 :: Γ) τ2
          pure (Term.Abs τ1 e) : SPMF Term) E := by
  refine le_trans ?_ (SPMF.prob_bind_ge B (d := 1) fun e he => ?_)
  · rw [mul_one]
  · rw [SPMF.prob_pure_of_mem (hB e he)]

/-- `genType` is `Bool` at least half the time. -/
theorem genType_prob_bool_ge : (1 : ℝ≥0∞) / 2 ≤ SPMF.prob (genType : SPMF Ty) {Ty.Bool} := by
  rw [genType]
  simp only [oneOfWith_eq, SPMF.prob_oneOf, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, List.length_cons, List.length_nil,
    SPMF.prob_pure_of_mem (Set.mem_singleton Ty.Bool)]
  exact ENNReal.div_le_div (le_add_right le_rfl) (by norm_num)

/-! ## One draw of `genTerm` -/

/-- **`Bool → Bool`.** One draw of `genTerm [] (Bool → Bool)` uses its argument with probability
at least `usesArgs1Bound`: the introduction branch with the body `#0`, which is `λx. x`. -/
theorem genTerm_prob_usesArgs1_ge :
    (usesArgs1Bound : ℝ≥0∞) ≤ SPMF.prob (genTerm [] (.Fun .Bool .Bool)) (UsesArgs 1) := by
  have hvar : (1 : ℝ≥0∞) / 4 ≤ SPMF.prob (genTerm [Ty.Bool] Ty.Bool) {Term.Var 0} := by
    refine le_trans ?_ (genTerm_prob_ge_var (by decide) _)
    unfold SPMF.prob; rw [SPMF.expect_elements]
    simp [show varsWithType [Ty.Bool] Ty.Bool = [Term.Var 0] from rfl]
  have habs := prob_abs_ge (Γ := []) (τ2 := .Bool) (E := UsesArgs 1) (B := {Term.Var 0})
    (τ1 := .Bool) fun e he => by
      rw [Set.mem_singleton_iff.mp he]
      exact ⟨[Ty.Bool], .Var 0, rfl, rfl, fun k hk => by
        obtain rfl : k = 0 := by omega
        simp [Term.uses]⟩
  refine le_trans ?_ (genTerm_prob_ge_abs rfl _)
  rw [show (usesArgs1Bound : ℝ≥0∞) = 1 / 4 / 3 by
    rw [usesArgs1Bound, ENNReal.coe_div (by norm_num)]
    simp only [div_eq_mul_inv, one_mul, ENNReal.coe_one]
    rw [← ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num))]
    norm_num]
  exact ENNReal.div_le_div_right (hvar.trans habs) _

/-- A body over two Boolean arguments that mentions both. -/
def UsesBoth : Set Term := {b | 0 < b.uses 0 ∧ 0 < b.uses 1}

/-- **`Bool → Bool → Bool`.** One draw of `genTerm [] (Bool → Bool → Bool)` uses both arguments
with probability at least `usesArgs2Bound`: two introduction branches, then the body
`(λy. #1) #1` or `(λy. #2) #0`. -/
theorem genTerm_prob_usesArgs2_ge :
    (usesArgs2Bound : ℝ≥0∞)
      ≤ SPMF.prob (genTerm [] (.Fun .Bool (.Fun .Bool .Bool))) (UsesArgs 2) := by
  -- In the context `[Bool, Bool, Bool]` at `Bool`, two of the three variables are outer ones.
  have hinner : (2 : ℝ≥0∞) / 3 / 4
      ≤ SPMF.prob (genTerm [Ty.Bool, Ty.Bool, Ty.Bool] Ty.Bool) {Term.Var 1, Term.Var 2} := by
    refine le_trans ?_ (genTerm_prob_ge_var (by decide) _)
    unfold SPMF.prob; rw [SPMF.expect_elements]
    simp [show varsWithType [Ty.Bool, Ty.Bool, Ty.Bool] Ty.Bool
      = [Term.Var 0, Term.Var 1, Term.Var 2] from rfl, Set.indicator]
    norm_num
  -- The function `λy. #1` or `λy. #2`.
  have hfun : (2 : ℝ≥0∞) / 3 / 4 / 3 ≤ SPMF.prob (genTerm [Ty.Bool, Ty.Bool] (.Fun .Bool .Bool))
      {Term.Abs .Bool (.Var 1), Term.Abs .Bool (.Var 2)} := by
    refine le_trans ?_ (genTerm_prob_ge_abs rfl _)
    refine ENNReal.div_le_div_right (hinner.trans (prob_abs_ge fun e he => ?_)) _
    rcases he with rfl | rfl <;> simp
  -- In the context `[Bool, Bool]` at `Bool`, each variable is one branch of four, then one of two.
  have hvar : ∀ j ∈ ({0, 1} : Set Nat), (1 : ℝ≥0∞) / 2 / 4
      ≤ SPMF.prob (genTerm [Ty.Bool, Ty.Bool] Ty.Bool) {Term.Var j} := by
    intro j hj
    refine le_trans ?_ (genTerm_prob_ge_var (by decide) _)
    unfold SPMF.prob; rw [SPMF.expect_elements]
    rcases hj with rfl | rfl <;>
      simp [show varsWithType [Ty.Bool, Ty.Bool] Ty.Bool = [Term.Var 0, Term.Var 1] from rfl]
  -- The argument that the function lacks.
  have harg : ∀ e1 ∈ ({Term.Abs .Bool (.Var 1), Term.Abs .Bool (.Var 2)} : Set Term),
      (1 : ℝ≥0∞) / 2 / 4 ≤ SPMF.prob (do
        let e2 ← genTerm [Ty.Bool, Ty.Bool] Ty.Bool
        pure (e1.App e2) : SPMF Term) UsesBoth := by
    intro e1 he1
    obtain ⟨j, hj, hmem⟩ : ∃ j ∈ ({0, 1} : Set Nat), Term.App e1 (.Var j) ∈ UsesBoth := by
      rcases he1 with rfl | rfl
      · exact ⟨1, by simp, by simp [UsesBoth, Term.uses]⟩
      · exact ⟨0, by simp, by simp [UsesBoth, Term.uses]⟩
    refine le_trans ?_ (SPMF.prob_bind_ge {Term.Var j} (d := 1) fun e he => ?_)
    · rw [mul_one]; exact hvar j hj
    · rw [Set.mem_singleton_iff.mp he, SPMF.prob_pure_of_mem hmem]
  -- The application branch at argument type `Bool`.
  have happ : (1 : ℝ≥0∞) / 2 * (2 / 3 / 4 / 3 * (1 / 2 / 4)) ≤ SPMF.prob (do
      let argTy ← genType
      let e1 ← genTerm [Ty.Bool, Ty.Bool] (argTy.Fun Ty.Bool)
      let e2 ← genTerm [Ty.Bool, Ty.Bool] argTy
      pure (e1.App e2) : SPMF Term) UsesBoth := by
    refine le_trans ?_ (SPMF.prob_bind_ge {Ty.Bool} (d := 2 / 3 / 4 / 3 * (1 / 2 / 4))
      fun argTy hτ => ?_)
    · exact mul_le_mul_left genType_prob_bool_ge _
    rw [Set.mem_singleton_iff.mp hτ]
    exact le_trans (mul_le_mul_left hfun _) (SPMF.prob_bind_ge _ harg)
  have hbody := (ENNReal.div_le_div_right happ 4).trans (genTerm_prob_ge_app (by decide) _)
  have hmid := (ENNReal.div_le_div_right (hbody.trans (prob_abs_ge (τ1 := .Bool)
      (E := {e | ∃ b ∈ UsesBoth, e = Term.Abs .Bool b}) fun b hb => ⟨b, hb, rfl⟩)) 3).trans
    (genTerm_prob_ge_abs rfl _)
  refine le_trans ?_ ((ENNReal.div_le_div_right (hmid.trans (prob_abs_ge (τ1 := .Bool)
      (E := UsesArgs 2) ?_)) 3).trans (genTerm_prob_ge_abs rfl _))
  · rw [usesArgs2Bound, ENNReal.coe_div (by norm_num)]
    refine le_of_eq ?_
    rw [← ENNReal.toReal_eq_toReal_iff' (by simp)
      (by simp [ENNReal.div_eq_top, ENNReal.mul_eq_top])]
    simp [ENNReal.toReal_div, ENNReal.toReal_mul]
    norm_num
  · rintro e ⟨b, ⟨h0, h1⟩, rfl⟩
    refine ⟨[Ty.Bool, Ty.Bool], b, rfl, rfl, fun k hk => ?_⟩
    interval_cases k <;> assumption

/-! ## How many tests -/

/-- **Tests until `Bool → Bool` uses its argument, with confidence `1 − δ`**:
`N ≥ ln(1/δ) / usesArgs1Bound` draws of `genTerm [] (Bool → Bool)` all ignore their argument with
probability at most `δ`. -/
theorem genTerm_usesArgs1_within {δ : ℝ≥0} (hδ : 0 < δ) {N : Nat}
    (hN : Real.log (1 / δ) ≤ usesArgs1Bound * N) :
    SPMF.prob (vectorOf N (genTerm [] (.Fun .Bool .Bool) : SPMF Term))
      {ts | ∀ t ∈ ts, t ∉ UsesArgs 1} ≤ δ :=
  SPMF.prob_vectorOf_miss_le_of_log_le _ genTerm_prob_usesArgs1_ge hδ hN

/-- **Expected tests until `Bool → Bool` uses its argument**: the sum that reads as the expected
number of tests (`Basalt.SPMF.Expect.Draws`) is at most `1 / usesArgs1Bound`. -/
theorem genTerm_usesArgs1_expected_le :
    ∑' N, SPMF.prob (vectorOf N (genTerm [] (.Fun .Bool .Bool) : SPMF Term))
      {ts | ∀ t ∈ ts, t ∉ UsesArgs 1} ≤ (usesArgs1Bound : ℝ≥0∞)⁻¹ :=
  SPMF.tsum_prob_vectorOf_miss_le _ genTerm_prob_usesArgs1_ge

/-- **Tests until `Bool → Bool → Bool` uses both arguments, with confidence `1 − δ`**:
`N ≥ ln(1/δ) / usesArgs2Bound` draws of `genTerm [] (Bool → Bool → Bool)` all ignore some argument
with probability at most `δ`. -/
theorem genTerm_usesArgs2_within {δ : ℝ≥0} (hδ : 0 < δ) {N : Nat}
    (hN : Real.log (1 / δ) ≤ usesArgs2Bound * N) :
    SPMF.prob (vectorOf N (genTerm [] (.Fun .Bool (.Fun .Bool .Bool)) : SPMF Term))
      {ts | ∀ t ∈ ts, t ∉ UsesArgs 2} ≤ δ :=
  SPMF.prob_vectorOf_miss_le_of_log_le _ genTerm_prob_usesArgs2_ge hδ hN

/-- **Expected tests until `Bool → Bool → Bool` uses both arguments**: the sum that reads as the
expected number of tests (`Basalt.SPMF.Expect.Draws`) is at most `1 / usesArgs2Bound`. -/
theorem genTerm_usesArgs2_expected_le :
    ∑' N, SPMF.prob (vectorOf N (genTerm [] (.Fun .Bool (.Fun .Bool .Bool)) : SPMF Term))
      {ts | ∀ t ∈ ts, t ∉ UsesArgs 2} ≤ (usesArgs2Bound : ℝ≥0∞)⁻¹ :=
  SPMF.tsum_prob_vectorOf_miss_le _ genTerm_prob_usesArgs2_ge

end STLC
