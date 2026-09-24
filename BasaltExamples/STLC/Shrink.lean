/-
Copyright (c) 2026 Harrison Goldstein & Ernest Ng. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein & Ernest Ng
-/
import BasaltExamples.STLC.Syntax

/-!
# Shrinking STLC Terms

`shrinkTerm` proposes structurally smaller terms, each well-typed in the context of the term it
shrinks.
-/

/-- Produces structurally smaller terms. Each candidate stays well-typed in the
    same context, but its type may change (see `shrinkTerm_sound`). -/
def shrinkTerm (e : Term) : List Term :=
  match e with
  | .Bool _  => []
  | .Var _      => []
  | .App e1 e2  => [e1, e2]
  -- Shrink only the body but keep the binder
  | .Abs τ e    => (shrinkTerm e).map (Term.Abs τ ·)

/-- Every term produced by `shrinkTerm` is well-typed in the same context,
    though not necessarily at the same type. -/
theorem shrinkTerm_sound :
    Typing Γ e τ → e' ∈ shrinkTerm e → ∃ τ', Typing Γ e' τ' := by
  induction e generalizing Γ τ e' with
  | Bool b =>
    intro _ hmem
    simp [shrinkTerm] at hmem
  | Var x =>
    intro _ hmem
    simp [shrinkTerm] at hmem
  | App e1 e2 IH1 IH2 =>
    intro hty hmem
    cases hty with
    | TApp Γ e1 e2 τ1 τ2 h2 h1 =>
      simp [shrinkTerm] at hmem
      rcases hmem with rfl | rfl
      · -- e1 is the shrunken term, with type τ1 → τ
        exists .Fun τ1 τ
      · -- e2 is the shrunken term
        exists τ1
  | Abs τ body IH =>
    intro hty hmem
    cases hty with
    | TAbs Γ e τ1 τ2 hbody =>
      simp only [shrinkTerm, List.mem_map] at hmem
      obtain ⟨body', hb', rfl⟩ := hmem
      obtain ⟨τ2', hτ2'⟩ := IH hbody hb'
      exists .Fun τ τ2'
      apply Typing.TAbs
      assumption
