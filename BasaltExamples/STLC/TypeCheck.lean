/-
Copyright (c) 2026 Harrison Goldstein & Ernest Ng. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein & Ernest Ng
-/
module

public import BasaltExamples.STLC.Syntax

/-!
# STLC typechecker

A STLC typechecker, proved sound and complete with respect to the `Typing` judgement.
-/

@[expose] public section

/-- Typechecks a term `e` in context `Γ`, return a type if typechecking succeeds.
    Adapted from the STLC typechecker in Software Foundations: https://softwarefoundations.cis.upenn.edu/plf-current/Typechecking.html -/
def typeCheck (Γ : Ctx) (e : Term) : Option Ty :=
  match e with
  | .Bool _ => some .Bool
  | .Var i => Γ[i]?
  | .Abs τ1 body => do
    let τ2 ← typeCheck (τ1 :: Γ) body
    some (.Fun τ1 τ2)
  | .App e1 e2 => do
    let fun_ty ← typeCheck Γ e1
    let τ2 ← typeCheck Γ e2
    match fun_ty with
    | .Fun argTy returnTy =>
      if argTy == τ2 then some returnTy
      else none
    | _ => none

/-- Typechecker is sound with respect to the typing relation -/
theorem typeCheck_sound : typeCheck Γ e = some τ → Typing Γ e τ := by
  induction e generalizing Γ τ with
  | Bool b => simp [typeCheck]; rintro rfl; exact .TBool ..
  | Var x => exact fun h => .TVar _ _ _ (getElem?_lookup h)
  | Abs τ1 body IH =>
    simp only [typeCheck, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq]
    rintro ⟨τ2, h, rfl⟩
    exact .TAbs _ _ _ _ (IH h)
  | App e1 e2 IH1 IH2 =>
    simp only [typeCheck, Option.bind_eq_bind, Option.bind_eq_some_iff]
    rintro ⟨τf, h1, τ2, h2, h⟩
    split at h
    · split at h <;> simp_all
      exact .TApp _ _ _ _ _ (IH2 h2) (IH1 h1)
    · contradiction

/-- Typechecker is complete with respect to the typing relation -/
theorem typeCheck_complete : Typing Γ e τ → typeCheck Γ e = some τ := by
  intro h
  induction h with
  | TVar _ _ _ hx => exact lookup_getElem? hx
  | _ => simp_all [typeCheck]
