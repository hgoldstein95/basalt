import Basalt.Gen
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Data.Real.Basic

open RandomChoice

def genMonoid [Gen G] : G (Σ (α : Type), Monoid α) :=
  pick (fun () => pure ⟨ℕ, Nat.instMonoid⟩) (fun () => pure ⟨ℝ, Real.instMonoid⟩)
