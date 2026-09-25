/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt.GenRel
import Basalt.IO.Choose
import Basalt.IO.Ideal
import Basalt.Walk.Entry

/-!
# Walking the Ideal Source

`ideal_fixpoint` proves `src.Below (gen …) (gen …)`, a generator at `SPMF` below the same generator
at `WordModel σ`: it inducts over the `SPMF` side's fixpoint, unfolds the other side one step, and
walks the two together (`ideal_bound`).
-/

open Lean Meta Elab Tactic Basalt.Walk

namespace Basalt.IdealBound

/-- `ideal_bound` proves `src.Below y x`, for `y` and `x` one generator term at `SPMF` and at
`WordModel σ`, by walking the two together: a bind, a map, a conditional, and a choice on each side
are related by their rules, a combinator with none is unfolded on both, and a leaf is a hypothesis,
a fact passed as `ideal_bound [h]`, or a callee's `.faithful` law or `.ideal` fact. -/
syntax (name := idealBoundTac) "ideal_bound" (walkFacts)? : tactic

elab_rules : tactic
  | `(tactic| ideal_bound $[$fs]?) => withMainContext do
    replaceMainGoal (← walkRel "ideal_bound" ``IdealSource.Below (walkFacts.terms fs)
      (← getMainGoal))

/-- `ideal_fixpoint` proves `src.Below (gen a₁ … aₙ) (gen a₁ … aₙ)`. It inducts with
`gen.fixpoint_induct` on the `SPMF` side, admissible because `expect` is continuous, unfolds the
`WordModel σ` side one step, and runs `ideal_bound`, where a recursive call is closed by `ih`. A
`gen` that is not recursive is unfolded on both sides and walked. -/
syntax (name := idealFixpointTac) "ideal_fixpoint" (walkFacts)? : tactic

elab_rules : tactic
  | `(tactic| ideal_fixpoint $[$fs]?) => withMainContext do
    replaceMainGoal (← relFixpoint "ideal_fixpoint" "ideal_bound" ``IdealSource.Below
      (fun args => mkAppM ``IdealSource.admissible_below #[args[2]!, args.back!])
      (walkFacts.terms fs) (← getMainGoal))

end Basalt.IdealBound

/-! ## Combinators the walk does not enter

`Below` is a `GenRel`, so each combinator's rule is `GenRel`'s. -/

namespace IdealSource

variable {σ : Type} [WordSource σ] (src : IdealSource σ)

theorem genRel : GenRel SPMF (WordModel σ) (@IdealSource.Below σ _ src) where
  pure := src.below_pure
  bind := src.below_bind
  map := src.below_map
  default := src.below_default
  choose := src.below_choose
  admissible := src.admissible_below

@[gen_rule]
theorem below_elements (xs : List α) (hne : xs ≠ []) :
    src.Below (elements xs hne) (elements xs hne) :=
  src.genRel.elements xs hne

@[gen_rule]
theorem below_vectorOf {g' : SPMF α} {g : WordModel σ α} (n : Nat) (hg : src.Below g' g) :
    src.Below (vectorOf n g') (vectorOf n g) :=
  src.genRel.vectorOf n hg

@[gen_rule]
theorem below_listOf {g' : SPMF α} {g : WordModel σ α} (hg : src.Below g' g) :
    src.Below (listOf g') (listOf g) :=
  src.genRel.listOf hg

@[gen_rule]
theorem below_nonEmptyListOf {g' : SPMF α} {g : WordModel σ α} (hg : src.Below g' g) :
    src.Below (nonEmptyListOf g') (nonEmptyListOf g) :=
  src.genRel.nonEmptyListOf hg

@[gen_rule]
theorem below_permutationOf (xs : List α) : src.Below (permutationOf xs) (permutationOf xs) :=
  src.genRel.permutationOf xs

@[gen_rule]
theorem below_oneOf {gs' : List (Unit → SPMF α)} {gs : List (Unit → WordModel σ α)}
    {hne' : gs' ≠ []} {hne : gs ≠ []}
    (h : List.Forall₂ (fun g' g => src.Below (g' ()) (g ())) gs' gs) :
    src.Below (oneOf gs' hne') (oneOf gs hne) :=
  src.genRel.oneOf h

@[gen_rule]
theorem below_frequency {gs' : List (Nat × (Unit → SPMF α))}
    {gs : List (Nat × (Unit → WordModel σ α))} {h' : 0 < (gs'.map Prod.fst).sum}
    {h : 0 < (gs.map Prod.fst).sum} (hgs : GenRel.Weighted (@IdealSource.Below σ _ src) gs' gs) :
    src.Below (frequency gs' h') (frequency gs h) :=
  src.genRel.frequency hgs

end IdealSource
