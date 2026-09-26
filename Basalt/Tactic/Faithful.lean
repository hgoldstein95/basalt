/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt.IO.Laws
import Basalt.Tactic.IO
import Basalt.Tactic.Ideal

/-!
# Proving a Generator Faithful

`faithful_fixpoint` proves `IsFaithful (gen …)` field by field: termination by a fact passed to it,
and the two relations by `ideal_fixpoint` and `io_fixpoint`.
-/

open Lean Meta Elab Tactic Basalt.Walk

namespace Basalt.FaithfulFixpoint

/-- `faithful_fixpoint [h₁, h₂]` proves `IsFaithful (gen a₁ … aₙ)`: `terminates` by the first of the
facts that applies, its explicit premises closed by hypotheses, and `below` and `approx` by
`ideal_fixpoint [h₁, h₂]` and `io_fixpoint [h₁, h₂]`. With no fact that applies, the termination
goal is left. -/
syntax (name := faithfulFixpointTac) "faithful_fixpoint" (walkFacts)? : tactic

elab_rules : tactic
  | `(tactic| faithful_fixpoint $[$fs]?) => withMainContext do
    let goal ← getMainGoal
    let ty ← whnfR (← instantiateMVars (← goal.getType))
    unless ty.isAppOfArity ``IsFaithful 2 do
      throwError "faithful_fixpoint: expected a goal `IsFaithful (gen …)`, got{indentExpr ty}"
    let [t, b, a] ← goal.apply (← mkConstWithFreshMVarLevels ``IsFaithful.mk)
      | throwError "faithful_fixpoint: could not split{indentExpr ty}"
    let mut ts := [t]
    for stx in walkFacts.terms fs do
      let closed ← t.withContext <| observing? do
        let e ← Term.withoutErrToSorry do
          let e ← Term.elabTerm stx none
          Term.synthesizeSyntheticMVarsNoPostponing
          instantiateMVars e
        (← t.apply e).forM fun g => g.assumption
      if closed.isSome then
        ts := []
        break
    let (_, b) ← b.introN 3
    let bs ← Lean.Elab.Tactic.run b (evalTactic (← `(tactic| ideal_fixpoint $[$fs]?)))
    let as ← Lean.Elab.Tactic.run a (evalTactic (← `(tactic| io_fixpoint $[$fs]?)))
    replaceMainGoal (ts ++ bs ++ as)

end Basalt.FaithfulFixpoint
