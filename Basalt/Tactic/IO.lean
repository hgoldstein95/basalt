/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Mathlib.Data.List.Forall2
import Basalt.GenRel
import Basalt.IO.Approx
import Basalt.Walk.Entry

/-!
# Walking `IO` Against `IOModel`

`io_fixpoint` proves `IOModel.Approx (gen …) (gen …)`, a generator at `IOModel` run by the same
generator at `IO`: it inducts over the `IOModel` side's fixpoint, unfolds the other side one step,
and walks the two together (`io_bound`).
-/

open Lean Meta Elab Tactic Basalt.Walk

namespace Basalt.IOBound

/-- `io_bound` proves `IOModel.Approx m x`, for `m` and `x` one generator term at `IOModel` and at
`IO`, by walking the two together: a bind, a map, a conditional, and a choice on each side are
related by their rules, a combinator with none is unfolded on both, and a leaf is a hypothesis or a
fact passed as `io_bound [h]`, such as a callee's `.faithful` law. -/
syntax (name := ioBoundTac) "io_bound" (walkFacts)? : tactic

elab_rules : tactic
  | `(tactic| io_bound $[$fs]?) => withMainContext do
    replaceMainGoal (← walkRel "io_bound" ``IOModel.Approx (walkFacts.terms fs)
      (← getMainGoal))

/-- `io_fixpoint` proves `IOModel.Approx (gen a₁ … aₙ) (gen a₁ … aₙ)`. It inducts with
`gen.fixpoint_induct` on the `IOModel` side, admissible because `toIO` is continuous, unfolds the
`IO` side one step, and runs `io_bound`, where a recursive call is closed by `ih`. A `gen` that is
not recursive is unfolded on both sides and walked. -/
syntax (name := ioFixpointTac) "io_fixpoint" (walkFacts)? : tactic

elab_rules : tactic
  | `(tactic| io_fixpoint $[$fs]?) => withMainContext do
    replaceMainGoal (← relFixpoint "io_fixpoint" "io_bound" ``IOModel.Approx
      (fun args => mkAppM ``IOModel.admissible_approx #[args.back!])
      (walkFacts.terms fs) (← getMainGoal))

end Basalt.IOBound

/-! ## Combinators the walk does not enter

`Approx` is a `GenRel`, so each combinator's rule is `GenRel`'s. -/

namespace IOModel

theorem genRel : GenRel IOModel IO @Approx where
  pure := approx_pure
  bind := approx_bind
  map := approx_map
  default := approx_default
  choose := approx_choose
  admissible := admissible_approx

@[gen_rule]
theorem approx_elements (xs : List α) (hne : xs ≠ []) :
    Approx (elements xs hne) (elements xs hne) :=
  genRel.elements xs hne

@[gen_rule]
theorem approx_vectorOf {g' : IOModel α} {g : IO α} (n : Nat) (hg : Approx g' g) :
    Approx (vectorOf n g') (vectorOf n g) :=
  genRel.vectorOf n hg

@[gen_rule]
theorem approx_listOf {g' : IOModel α} {g : IO α} (hg : Approx g' g) :
    Approx (listOf g') (listOf g) :=
  genRel.listOf hg

@[gen_rule]
theorem approx_nonEmptyListOf {g' : IOModel α} {g : IO α} (hg : Approx g' g) :
    Approx (nonEmptyListOf g') (nonEmptyListOf g) :=
  genRel.nonEmptyListOf hg

@[gen_rule]
theorem approx_permutationOf (xs : List α) : Approx (permutationOf xs) (permutationOf xs) :=
  genRel.permutationOf xs

@[gen_rule]
theorem approx_oneOf {gs' : List (Unit → IOModel α)} {gs : List (Unit → IO α)}
    {hne' : gs' ≠ []} {hne : gs ≠ []}
    (h : List.Forall₂ (fun g' g => Approx (g' ()) (g ())) gs' gs) :
    Approx (oneOf gs' hne') (oneOf gs hne) :=
  genRel.oneOf h

@[gen_rule]
theorem approx_frequency {gs' : List (Nat × (Unit → IOModel α))}
    {gs : List (Nat × (Unit → IO α))} {h' : 0 < (gs'.map Prod.fst).sum}
    {h : 0 < (gs.map Prod.fst).sum} (hgs : GenRel.Weighted @Approx gs' gs) :
    Approx (frequency gs' h') (frequency gs h) :=
  genRel.frequency hgs

end IOModel
