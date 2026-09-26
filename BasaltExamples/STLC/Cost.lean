/-
Copyright (c) 2026 Harrison Goldstein & Ernest Ng. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein & Ernest Ng
-/
import Basalt
import BasaltExamples.STLC.GenTerm
import BasaltExamples.STLC.TypeCheck

/-!
# Cost Bound for `genTerm`

`genTerm Γ τ` makes at most `Term.costInCtx Γ e` random choices to produce `e`. The bound needs the
context, and the proof carries well-typedness alongside the cost.
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
    SPMF.Cost.Always (genZero Γ τ) (fun e n => Typing Γ e τ ∧ n ≤ 1) := by
  induction τ generalizing Γ with
  | Bool => rw [genZero]; cost_bound <;> grind [Typing]
  | Fun τ1 τ2 _ ih2 => rw [genZero]; cost_bound [ih2] <;> grind [Typing]

/-- The cost law with well-typedness carried alongside. Bounding an application's cost needs its
argument's type, which only the argument's typing fixes, so the induction must carry it. -/
theorem genTerm.cost_typed :
    SPMF.Cost.Always (genTerm Γ τ) (fun e n => Typing Γ e τ ∧ n ≤ Term.costInCtx Γ e) := by
  cost_fixpoint [genZero.cost_typed, genType.cost_bounded]
  all_goals grind [Term.costInCtx, typeCheck_getD_of_typing, Term.two_le_costInCtx,
    varsWithType_sound, Typing]

theorem genTerm.cost_bounded : IsCostBounded (genTerm Γ τ) (Term.costInCtx Γ) :=
  fun p hp => (genTerm.cost_typed p hp).2
