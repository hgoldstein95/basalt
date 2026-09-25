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

`faithful_fixpoint` proves `IsFaithful (gen …)` field by field: termination by the generator's
`.terminates` law, and the two relations by `ideal_fixpoint` and `io_fixpoint`.
-/

open Lean Meta Elab Tactic Basalt.Walk

namespace Basalt.FaithfulFixpoint

/-- `faithful_fixpoint` proves `IsFaithful (gen a₁ … aₙ)`: `terminates` by `gen.terminates`, whose
explicit premises are hypotheses, and `below` and `approx` by `ideal_fixpoint` and `io_fixpoint`,
each passed the facts in `faithful_fixpoint [h]`. A generator with no `.terminates` law, or one that
does not apply, is left its termination goal. -/
syntax (name := faithfulFixpointTac) "faithful_fixpoint" (walkFacts)? : tactic

elab_rules : tactic
  | `(tactic| faithful_fixpoint $[$fs]?) => withMainContext do
    let goal ← getMainGoal
    let ty ← whnfR (← instantiateMVars (← goal.getType))
    unless ty.isAppOfArity ``IsFaithful 2 do
      throwError "faithful_fixpoint: expected a goal `IsFaithful (gen …)`, got{indentExpr ty}"
    let head ← lambdaTelescope ty.appArg! fun _ body => pure body.getAppFn.constName?
    let [t, b, a] ← goal.apply (← mkConstWithFreshMVarLevels ``IsFaithful.mk)
      | throwError "faithful_fixpoint: could not split{indentExpr ty}"
    let law := head.map (· ++ `terminates)
    let closed ← match law with
      | some law =>
        if (← getEnv).contains law then
          observing? do
            let gs ← t.apply (← mkConstWithFreshMVarLevels law)
            gs.forM fun g => g.assumption
        else pure none
      | none => pure none
    let ts := if closed.isSome then [] else [t]
    let (_, b) ← b.introN 3
    let bs ← Lean.Elab.Tactic.run b (evalTactic (← `(tactic| ideal_fixpoint $[$fs]?)))
    let as ← Lean.Elab.Tactic.run a (evalTactic (← `(tactic| io_fixpoint $[$fs]?)))
    replaceMainGoal (ts ++ bs ++ as)

end Basalt.FaithfulFixpoint
