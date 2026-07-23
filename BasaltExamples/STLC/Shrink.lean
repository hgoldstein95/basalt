import Basalt
import Basalt.PlausibleGen
import BasaltExamples.STLC.Syntax
import BasaltExamples.STLC.GenType

open RandomChoice SPMF List

/-!
# A shrinker for well-typed STLC terms

`shrinkTerm` returns a list of structurally smaller terms. Every candidate is
well-typed in the same context (though possibly at a *different* type), which is
exactly what the property-based testing loop needs to keep shrinking a
counterexample while preserving the "is well-typed" precondition.
-/

/-- Produces structurally smaller terms. Each candidate stays well-typed in the
    same context, but its type may change (see `shrinkTerm_sound`). -/
def shrinkTerm : Term → List Term
  | .Bool _  => []
  | .Var _      => []
  -- An application can be replaced by either well-typed subterm.
  -- (We do *not* shrink `e1`/`e2` in place: the function/argument positions are
  -- type-constrained, so a type-changing shrink there would be ill-typed.)
  | .App e1 e2  => [e1, e2]
  -- A lambda can collapse to a constant, or we can shrink the body in place.
  -- Shrinking the body is safe: re-wrapping in `.Abs τ` gives `.Fun τ _` for
  -- whatever type the shrunk body has.
  | .Abs τ e    => (Term.Abs τ ·) <$> shrinkTerm e

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
      simp [shrinkTerm] at hmem
      obtain ⟨body', hb', rfl⟩ := hmem
      obtain ⟨τ2', hτ2'⟩ := IH hbody hb'
      exists .Fun τ τ2'
      apply Typing.TAbs
      assumption
