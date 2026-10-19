/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
module

public import Basalt.IO.Approx
public import Basalt.IO.Choose
public import Basalt.IO.Laws
public import Basalt.Walk.Entry

/-!
# Proving a Generator Faithful

`faithful_fixpoint` proves `IsFaithful (gen …)` field by field: termination by a fact passed to it,
and the two relations by `walk fixpoint`.
-/

@[expose] public section

open Lean Meta Elab Tactic Basalt.Walk

namespace Basalt.FaithfulFixpoint

/-- Proves `IsFaithful (gen …)`. `faithful_fixpoint [gen.terminates, callee.faithful, …]` closes the
`terminates` field with the generator's termination law and proves the other two with
`walk fixpoint`, using each callee's `.faithful` law. Without a termination law, that goal is
left. -/
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
    let mut rel : Array Term := #[]
    for stx in walkFacts.terms fs do
      -- `some n` for a fact `∀ x₁ … xₙ, IsFaithful (gen …)` with `n` explicit binders, `none` for
      -- one that closed the termination goal.
      let used ← t.withContext <| observing? do
        let e ← elabFact stx
        let faithful? ← forallTelescope (← inferType e) fun xs concl => do
          unless (← whnfR concl).isAppOf ``IsFaithful do return none
          some <$> xs.foldlM (init := 0) fun n x => return if (← x.fvarId!.getBinderInfo).isExplicit
            then n + 1 else n
        if faithful?.isNone then
          if ts.isEmpty then failure
          (← t.apply e).forM fun g => g.assumption
        return faithful?
      match used with
      | some (some n) =>
        let xs ← (Array.range n).mapM fun _ => return mkIdent (← mkFreshUserName `x)
        rel := rel ++ (← [`below, `approx].toArray.mapM fun f => do
          let field := mkIdent f
          if xs.isEmpty then `(($stx).$field) else `(fun $xs* => ($stx $xs*).$field))
      | some none => ts := []
      | none => rel := rel.push stx
    let (_, b) ← b.introN 3
    let bs ← walkFixpoint rel b
    let as ← walkFixpoint rel a
    replaceMainGoal (ts ++ bs ++ as)

end Basalt.FaithfulFixpoint
