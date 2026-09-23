/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt.Laws
import Basalt.Walk.Entry

/-!
# Walking Soundness

The structural half of a soundness proof. `IsSound g P` is a lower bound, by `True`, on
`SPMF.alwaysObs` in the demonic algebra, so `sound_bound` computes the weakest precondition of `P`
and splits it into one goal per path, as `cost_bound` does at the cost interpretation;
`sound_fixpoint` first inducts over a recursive generator's fixpoint.
-/

open RandomChoice Lean Meta Elab Tactic Basalt.Walk

namespace SPMF

open Lean.Order in
theorem admissible_isSound (P : α → Prop) : admissible fun x : SPMF α => IsSound x P := by
  intro c hc ih a ha
  rw [mem_support_csup hc] at ha
  obtain ⟨x, hxc, hxa⟩ := ha
  exact ih x hxc a hxa

/-! ## Leaves

A fact about a sub-generator is used under the postcondition the walk arrives with: what it has to
imply is the bound. -/

@[obs_leaf]
theorem le_always_of_isSound {x : SPMF α} {R p : α → Prop} (hx : IsSound x R) :
    (∀ a, R a → p a) ≤ alwaysObs.spec x p := fun h a ha => h a (hx a ha)

@[obs_leaf]
theorem le_always_of_isSoundAndComplete {x : SPMF α} {R p : α → Prop}
    (hx : IsSoundAndComplete x R) : (∀ a, R a → p a) ≤ alwaysObs.spec x p :=
  le_always_of_isSound hx.sound

/-! ## The combinators that take a generator

They ask for the soundness of the generator, for a predicate the list's postcondition says nothing
about: a fact or a law supplies it. Each bridges the combinator's support law. -/

section generatorArgument

variable {α : Type} {g : SPMF α} {R : α → Prop} {p : List α → Prop}

@[gen_rule]
theorem le_always_vectorOf {n : Nat} (hg : IsSound g R) :
    (∀ xs, (xs.length = n ∧ ∀ x ∈ xs, R x) → p xs) ≤ alwaysObs.spec (vectorOf n g) p :=
  fun h xs hxs =>
    have hxs := mem_support_vectorOf_iff.mp hxs
    h xs ⟨hxs.1, fun x hx => hg x (hxs.2 x hx)⟩

@[gen_rule]
theorem le_always_listOfMaxLength {n : Nat} (hg : IsSound g R) :
    (∀ xs, (xs.length ≤ n ∧ ∀ x ∈ xs, R x) → p xs) ≤ alwaysObs.spec (listOfMaxLength n g) p :=
  fun h xs hxs =>
    have hxs := mem_support_listOfMaxLength_iff.mp hxs
    h xs ⟨hxs.1, fun x hx => hg x (hxs.2 x hx)⟩

@[gen_rule]
theorem le_always_listOf (hg : IsSound g R) :
    (∀ xs, (∀ x ∈ xs, R x) → p xs) ≤ alwaysObs.spec (listOf g) p :=
  fun h xs hxs => h xs fun x hx => hg x (mem_support_listOf.mp hxs x hx)

@[gen_rule]
theorem le_always_nonEmptyListOf (hg : IsSound g R) :
    (∀ xs, (xs ≠ [] ∧ ∀ x ∈ xs, R x) → p xs) ≤ alwaysObs.spec (nonEmptyListOf g) p :=
  fun h xs hxs =>
    have hxs := mem_support_nonEmptylistOf.mp hxs
    h xs ⟨hxs.1, fun x hx => hg x (hxs.2 x hx)⟩

end generatorArgument

end SPMF

namespace Basalt.SoundBound

open Basalt.Walk

/-- `goal`, which must be `IsSound (gen …) P`: the value type, the generator, and the predicate.
`tac` is the caller, for the error. -/
def parseSound (tac : String) (goal : MVarId) : MetaM (Expr × Expr × Expr) := do
  let ty ← whnfR (← instantiateMVars (← goal.getType))
  unless ty.isAppOfArity ``IsSound 3 do
    let hint := if ty.isAppOf ``IsSoundAndComplete then
      m!"\nSplit the law into its halves first: `refine .intro ?sound ?complete`." else m!""
    throwError "{tac}: expected a goal `IsSound (gen …) P`, got{indentExpr ty}{hint}"
  let #[α, g, P] := ty.getAppArgs | unreachable!
  return (α, g, P)

/-- Walk `goal` (see `sound_bound`), returning the tidied residual goals. `tac` is the caller, for
the errors. -/
partial def walkSound (tac : String) (extras : Array Term) (goal : MVarId) :
    TermElabM (List MVarId) := goal.withContext do
  let (α, g, P) ← parseSound tac goal
  if let some cases ← splitMatch? goal g then return ← cases.flatMapM (walkSound tac extras)
  -- A predicate that is not a lambda is given a binder, for the walk to name a last draw after.
  let post ← if P.isLambda then pure P else
    withLocalDeclD `v α fun v => mkLambdaFVars #[v] (mkApp P v)
  pathsBound extras ``SPMF.alwaysObs g post goal

/-- `sound_bound` proves `IsSound (gen …) P` up to what `P` says: it walks `gen`'s syntax, pushing
`P` into each sub-generator, and leaves one goal per path through `gen`, which is `P` of the value
that path built. Recursive occurrences are closed from the local context, callees from their
`.sound_complete` or `.sound` law; any other soundness fact can be passed as `sound_bound [h₁, h₂]`.

In a residual goal, a value drawn by `let x ← …` is `x✝` and what is known about it `h_x✝`
(`Basalt/Walk/Names.lean`); name them with `next x h_x =>`. -/
syntax (name := soundBoundTac) "sound_bound" (walkFacts)? : tactic

elab_rules : tactic
  | `(tactic| sound_bound $[$fs]?) => withMainContext do
    replaceMainGoal (← walkSound "sound_bound" (walkFacts.terms fs) (← getMainGoal))

/-- `sound_fixpoint` proves `IsSound (gen a₁ … aₙ) P` up to what `P` says. It inducts with
`gen.fixpoint_induct` over the arguments some recursive call of `gen` changes, admissible because
support is continuous, unfolds one step, and runs `sound_bound` (extra facts go in
`sound_fixpoint [h₁, h₂]`). In each residual goal the recursive function is named after `gen`, the
soundness of its every call is `ih`, and the changing arguments keep their names. A `gen` that is not
recursive is unfolded and walked. -/
syntax (name := soundFixpointTac) "sound_fixpoint" (walkFacts)? : tactic

elab_rules : tactic
  | `(tactic| sound_fixpoint $[$fs]?) => withMainContext do
    let goal ← getMainGoal
    let (_, g, P) ← parseSound "sound_fixpoint" goal
    let adm ← mkAppM ``SPMF.admissible_isSound #[P]
    replaceMainGoal (← walkSound "sound_fixpoint" (walkFacts.terms fs)
      (← fixpointStep "sound_fixpoint" "sound_bound" g adm goal))

end Basalt.SoundBound
