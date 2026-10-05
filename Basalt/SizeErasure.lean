/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Lean.Meta.Tactic.Simp.Simproc
import Basalt.GenHom

/-!
# Evaluating at a Size

Running a `WithSize G` generator at a size is a homomorphism into `G`, so `simp only [size_erasure]`
turns `g.run n` into a generator that reads no size: `sized` and `resize` are evaluated, and every
other construct and combinator is natural.
-/

open Lean.Order

namespace WithSize

variable {G : Type → Type} [Gen G] {α : Type} (n : Nat)

/-- `g.run n`, as a homomorphism in `g`. -/
def atSize : GenHom (WithSize G) G where
  map g := g.run n
  map_pure _ := rfl
  map_bind _ _ := rfl
  map_map _ _ := rfl
  map_default := rfl
  map_choose _ _ _ := rfl
  admissible x := admissible_apply (fun _ y => y ⊑ x) n fun _ hc h => csup_le hc h

@[size_erasure]
theorem run_eq_map (g : WithSize G α) : g.run n = (atSize n).map g := rfl

@[size_erasure]
theorem map_sized (f : Nat → WithSize G α) :
    (atSize n).map (Sized.sized f) = (atSize n).map (f n) := rfl

@[size_erasure]
theorem map_resize (m : Nat) (g : WithSize G α) :
    (atSize n).map (Sized.resize m g) = (atSize m).map g := rfl

@[size_erasure]
theorem map_getSize : (atSize n).map (getSize : WithSize G Nat) = Pure.pure n := rfl

@[size_erasure]
theorem map_lift (g : G α) : (atSize n).map (WithSize.lift g) = g := rfl

@[size_erasure]
theorem map_monadLift (g : G α) : (atSize n).map (MonadLiftT.monadLift g) = g := rfl

open Lean Meta in
/-- A generator nothing here evaluates stays `g.run n`. Stated as a lemma this loops with
`run_eq_map`, and every `simp only [size_erasure]` fails at its recursion limit; a simproc ends the
term's simplification instead. -/
dsimproc [size_erasure] mapAtSize (GenHom.map (atSize _) _) := fun e => do
  let_expr GenHom.map _ _ _ _ φ _ g := e | return .continue
  let_expr atSize _ _ n := φ | return .continue
  return .done (← mkAppM ``WithSize.run #[g, n])

end WithSize
