/-
Copyright (c) 2026 Harrison Goldstein & Ernest Ng. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein & Ernest Ng
-/
import Basalt
import BasaltExamples.STLC.GenTerm
import BasaltExamples.STLC.Termination
import BasaltExamples.STLC.TypeCheck

/-!
# Cost Bounds for `genTerm`

`genTerm Γ τ` makes at most `Term.costInCtx Γ e` random choices to produce `e`. The bound needs the
context, and the proof carries well-typedness alongside the cost. Yet no finite bound holds of its
expected cost (`genTerm.not_expected_cost_bounded`).
-/

/-- The choices `genTerm Γ` makes to produce a term: one `oneOf` per node, one more for a literal or
a variable, and `argTy.size` for the argument type an application draws.

That type is not recorded in `.App e1 e2`, so no function of the term alone bounds the cost. Types
are unique in STLC, so it is recovered as the type of `e2` in `Γ`; the `getD` default is never
reached on a well-typed term (`typeCheck_getD_of_typing`). An `Abs` is charged the recursive
branch's cost, which dominates `genZero`'s single choice. -/
def Term.costInCtx (Γ : Ctx) (e : Term) : Nat :=
  match e with
  | .Bool _    => 2
  | .Var _     => 2
  | .Abs τ1 e  => 1 + Term.costInCtx (τ1 :: Γ) e
  | .App e1 e2 => 1 + ((typeCheck Γ e2).getD .Bool).size + Term.costInCtx Γ e1 + Term.costInCtx Γ e2

/-- If `Γ ⊢ e : τ`, then `Option.getD (typeCheck Γ e) default = τ`,
    i.e. the default argument supplied to `Option.getD` is never returned. -/
theorem typeCheck_getD_of_typing {default : Ty} (h : Typing Γ e τ) :
    (typeCheck Γ e).getD default = τ := by
  rw [typeCheck_complete h]; rfl

theorem Term.two_le_costInCtx (Γ : Ctx) (e : Term) : 2 ≤ Term.costInCtx Γ e := by
  induction e generalizing Γ with
  | Bool => simp [Term.costInCtx]
  | Var => simp [Term.costInCtx]
  | Abs τ1 e IH => simp only [Term.costInCtx]; have := IH (τ1 :: Γ); omega
  | App e1 e2 IH1 _ => simp only [Term.costInCtx]; have := IH1 Γ; omega

theorem genZero.cost_typed :
    SPMF.Cost.alwaysObs.spec (genZero Γ τ) (fun e n => Typing Γ e τ ∧ n ≤ 1) := by
  induction τ generalizing Γ with
  | Bool => rw [genZero]; walk <;> grind [Typing]
  | Fun τ1 τ2 _ ih2 => rw [genZero]; walk [ih2] <;> grind [Typing]

/-- The cost law with well-typedness carried alongside. Bounding an application's cost needs its
argument's type, which only the argument's typing fixes, so the induction must carry it. -/
theorem genTerm.cost_typed :
    SPMF.Cost.alwaysObs.spec (genTerm Γ τ) (fun e n => Typing Γ e τ ∧ n ≤ Term.costInCtx Γ e) := by
  walk fixpoint [genZero.cost_typed, genType.cost_bounded.obs]
  all_goals grind [Term.costInCtx, typeCheck_getD_of_typing, Term.two_le_costInCtx,
    varsWithType_sound, Typing]

theorem genTerm.cost_bounded : IsCostBounded (genTerm Γ τ) (Term.costInCtx Γ) :=
  fun p hp => (genTerm.cost_typed p hp).2

theorem genZero.cost_faithful : IsCostFaithful (genZero Γ τ) where
  erasedLe := by
    induction τ generalizing Γ with
    | Bool => unfold genZero; walk
    | Fun τ1 τ2 _ ih => unfold genZero; walk
  leErased := by
    induction τ generalizing Γ with
    | Bool => unfold genZero; walk
    | Fun τ1 τ2 _ ih => unfold genZero; walk

theorem genTerm.cost_faithful : IsCostFaithful (genTerm Γ τ) :=
  ⟨by walk fixpoint [genZero.cost_faithful.erasedLe, genType.cost_faithful.erasedLe],
    by walk fixpoint [genZero.cost_faithful.leErased, genType.cost_faithful.leErased]⟩

open scoped ENNReal in
/-- An application draws its argument type from `genType`, whose expected cost has no finite bound;
the branch is taken at every type, so one unfolding is enough. -/
theorem genTerm.not_expected_cost_bounded {B : ℝ≥0∞} (hB : B ≠ ⊤) :
    ¬ IsExpectedCostBounded (genTerm Γ τ : SPMF.Cost Term) B := by
  intro h
  have htype : ⊤ ≤ SPMF.Cost.expectObs.spec (genType : SPMF.Cost Ty) (fun _ n => (n : ℝ≥0∞)) := by
    by_contra hlt
    exact genType.not_expected_cost_bounded (lt_top_iff_ne_top.mp (not_le.mp hlt)) le_rfl
  have hty := genType.cost_faithful.one_le_mass genType.terminates
  have hm := fun Γ τ => (genTerm.cost_faithful (Γ := Γ) (τ := τ)).one_le_mass genTerm.terminates
  have hz := fun Γ τ => (genZero.cost_faithful (Γ := Γ) (τ := τ)).one_le_mass genZero.terminates
  have htop : ⊤ ≤ SPMF.Cost.expectObs.spec (genTerm Γ τ : SPMF.Cost Term)
      (fun _ n => (n : ℝ≥0∞)) := by
    rw [genTerm.eq_def]
    walk [SPMF.Cost.le_expect_add (x := genType) (h := fun _ n => (n : ℝ≥0∞)) hty htype,
      fun Γ τ => SPMF.Cost.le_expect_add (x := genTerm Γ τ) (h := fun _ n => (n : ℝ≥0∞))
        (hm Γ τ) zero_le,
      fun Γ τ => SPMF.Cost.le_expect_add (x := genZero Γ τ) (h := fun _ n => (n : ℝ≥0∞))
        (hz Γ τ) zero_le]
    all_goals split <;> simp [ENNReal.top_div_of_ne_top]
  exact hB (top_unique (htop.trans h))
