/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Segev Elazar-Mittelman
-/
module

public import Basalt.Backtrack

/-!
# Weighted Choice Without Retry

`pick` runs one branch, drawn with probability proportional to its weight, and fails if that branch
does: `frequency` for a generator that can fail. It is a class for the reason `Backtrack` is: an
enumeration reads it as the union of its branches, where enumerating the draw would repeat each
branch once per unit of weight.
-/

@[expose] public section

namespace Basalt

/-- One branch, drawn with probability proportional to its weight, run without retry; `fail` if
every weight is `0`. -/
class Pick (G : Type → Type) where
  pick {α : Type} : List (Nat × (Unit → G α)) → G α

namespace Pick

open Backtrack RandomChoice

variable {G : Type → Type} {α : Type}

/-- The draw, with failure observed as `none`. -/
def draw [Monad G] [RandomChoice G] (gs : List (Nat × (Unit → OptionT G α))) : OptionT G α :=
  OptionT.mk do
    let n ← choose 0 (sumWeights gs - 1) (Nat.zero_le _)
    match pickDrop gs n.down.val with
    | none => pure none
    | some (_, g, _) => (g ()).run

/-- Where failure is `none`, the draw itself. -/
instance instOptionT [Monad G] [RandomChoice G] : Pick (OptionT G) := ⟨draw⟩

/-- At an enumeration, the branches of positive weight, side by side: what `backtrack` is there. -/
instance instFinite : Pick Finite := ⟨fun gs => Backtrack.backtrack gs⟩

/-- At every size, the choice among the branches at that size. -/
instance instWithSize [Pick G] : Pick (WithSize G) where
  pick gs n := Pick.pick (gs.map fun p => (p.1, fun _ : Unit => (p.2 ()).run n))

end Pick

/-! ## Monotonicity -/

section monotonicity

open Lean.Order Backtrack

attribute [local instance] List.instPartialOrderPointwise instPartialOrderConstFst

/-- The monotonicity `pick` must satisfy for a recursive generator that uses it to be definable by
`partial_fixpoint`, branches related as `frequency`'s are. -/
class MonoPick (G : Type → Type) [Pick G] [∀ α, PartialOrder (G α)] where
  pick_mono {α : Type} {gs₁ gs₂ : List (Nat × (Unit → G α))} :
    gs₁ ⊑ gs₂ → Pick.pick gs₁ ⊑ Pick.pick gs₂

@[partial_fixpoint_monotone]
theorem monotone_pick {G : Type → Type} [Pick G] [∀ α, PartialOrder (G α)] [MonoPick G]
    {α : Type} {γ : Sort w} [PartialOrder γ]
    (gs : γ → List (Nat × (Unit → G α))) (hgs : monotone gs) :
    monotone fun x => Pick.pick (gs x) :=
  fun x y hxy => MonoPick.pick_mono (hgs x y hxy)

namespace Pick

instance instMonoFinite : MonoPick Finite where
  pick_mono h := MonoBacktrack.backtrack_mono (G := Finite) h

instance instMonoOptionT {G : Type → Type} [Gen G] : MonoPick (OptionT G) where
  pick_mono {_ gs₁ gs₂} h := by
    show draw gs₁ ⊑ draw gs₂
    unfold draw
    refine choose_bind_mono (G := G) (by rw [sumWeights_eq_of_rel h]) fun n _ _ => ?_
    rcases pickDrop_rel h n with ⟨h₁, h₂⟩ | ⟨k, g₁, g₂, r₁, r₂, h₁, h₂, hg, _⟩
    · simp only [h₁, h₂]
      exact PartialOrder.rel_refl
    · simp only [h₁, h₂]
      exact hg ()

instance instMonoWithSize {G : Type → Type} [Gen G] [Pick G] [MonoPick G] :
    MonoPick (WithSize G) where
  pick_mono h n := MonoPick.pick_mono (G := G) (map_run_rel n h)

end Pick

end monotonicity

end Basalt
