/-
Copyright (c) 2026 Harrison Goldstein & Ernest Ng. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein & Ernest Ng
-/
import Basalt
import BasaltExamples.STLC.Syntax

open List

/-!
# A Typechecker for the STLC

A decidable typechecker `typeCheck` for the simply-typed lambda calculus, proved sound and complete
with respect to the `Typing` judgement (`BasaltExamples/STLC/Syntax.lean`).
-/

/-- Typechecks a term `e` in context `Γ`, return a type if typechecking succeeds -/
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
  intro h
  induction e generalizing Γ τ with
  | Bool b =>
    simp [typeCheck] at h
    subst h
    constructor
  | Var x =>
    simp [typeCheck] at h
    constructor
    apply getElem?_lookup
    assumption
  | Abs τ1 body IH =>
    cases hbody : typeCheck (τ1 :: Γ) body with
    | none =>
      rw [typeCheck, hbody] at h
      contradiction
    | some τ2 =>
      rw [typeCheck, hbody] at h
      simp at h
      subst h
      constructor
      apply IH
      assumption
  | App e1 e2 IH1 IH2 =>
    rw [typeCheck] at h
    simp at h
    cases h1 : typeCheck Γ e1 with
    | none =>
      rw [h1] at h
      dsimp at h
      contradiction
    | some τ1 =>
      rw [h1] at h
      simp at h
      cases h2 : typeCheck Γ e2 with
      | none =>
        rw [h2] at h
        dsimp at h
        contradiction
      | some τ2 =>
        rw [h2] at h
        dsimp at h
        cases τ1 with
        | Bool =>
          dsimp at h
          contradiction
        | Fun τ11 τ12 =>
          dsimp at h
          by_cases (τ11 = τ2)
          . simp at h
            obtain ⟨h1, h2⟩ := h
            rename_i h1
            constructor
            . apply IH2
              assumption
            . subst_vars
              apply IH1
              assumption
          . split at h <;> simp_all

/-- Typechecker is complete with respect to the typing relation -/
theorem typeCheck_complete : Typing Γ e τ → typeCheck Γ e = some τ := by
  intro h
  induction h with
  | TBool Γ b => rfl
  | TVar Γ x =>
    simp [typeCheck]
    apply lookup_getElem?
    assumption
  | TAbs Γ body τ1 τ2 hbody IH =>
    simp [typeCheck]
    rw [IH]
    rfl
  | TApp Γ e1 e2 τ1 τ2 h2 h1 IH2 IH1 =>
    simp [typeCheck]
    rw [IH2, IH1]
    simp
