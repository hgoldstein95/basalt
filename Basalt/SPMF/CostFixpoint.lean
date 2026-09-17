/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt.SPMF.CostBound

/-!
# The `cost_fixpoint` Tactic

`cost_fixpoint` reduces a `.cost_bounded` law to one step of the generator: fixpoint induction over
the arguments its recursive calls change, then `cost_bound`.
-/

open Lean Meta Elab Tactic Lean.Order

namespace Basalt.CostFixpoint

open Basalt.Walk Basalt.CostBound

/-- `admissible fun g => ∀ ys, Always (g ys) (post ys)`, over the binders of `gTy`: one
`admissible_pi_apply` per binder, each with its predicate given, since unification cannot find
it. -/
private partial def mkAdmissible (gTy : Expr) (post : Array Expr → MetaM Expr)
    (ys : Array Expr := #[]) : MetaM Expr := do
  match ← whnf gTy with
  | .forallE n d b _ =>
    withLocalDeclD n d fun y => do
      let inner ← mkAdmissible (b.instantiate1 y) post (ys.push y)
      let P ← mkLambdaFVars #[y] (← whnfR (← inferType inner)).appArg!
      mkAppOptM ``admissible_pi_apply
        #[d, ← mkLambdaFVars #[y] (b.instantiate1 y), none, P, ← mkLambdaFVars #[y] inner]
  | _ => mkAppM ``SPMF.Cost.admissible_Always #[← post ys]

/-- `cost_fixpoint` proves `IsCostBounded (gen a₁ … aₙ) c` (or `IsBounded`, or
`SPMF.Cost.Always`) up to arithmetic. It inducts with `gen.fixpoint_induct` over the arguments some
recursive call of `gen` changes, unfolds one step, and runs `cost_bound` (extra cost bounds go in
`cost_fixpoint [h₁, h₂]`). In each residual goal the recursive function is named after `gen`, the
bound on its every call is `ih`, and the changing arguments keep their names. A `gen` that is not
recursive is unfolded and walked. -/
syntax (name := costFixpointTac) "cost_fixpoint" (" [" term,* "]")? : tactic

elab_rules : tactic
  | `(tactic| cost_fixpoint $[[$extras,*]]?) => withMainContext do
    let extras := (extras.map (·.getElems)).getD #[]
    let goal ← toAlways (← getMainGoal)
    goal.withContext do
    let ty ← instantiateMVars (← goal.getType)
    let #[_, x, post] := ty.getAppArgs | throwError "cost_fixpoint: internal error"
    let some gen := x.getAppFn.constName?
      | throwError "cost_fixpoint: expected a generator applied to its arguments, got{indentExpr x}"
    if isCombinator (← getEnv) gen then
      throwError "cost_fixpoint: `{gen}` is a combinator, not a generator definition; prove a \
        bound on a combinator term with `cost_bound`"
    let some indName ← observing? (realizeGlobalConstNoOverload (mkIdent (gen ++ `fixpoint_induct)))
      | let [goal] ← Lean.Elab.Tactic.run goal (evalTactic (← `(tactic| unfold $(mkIdent gen))))
          | throwError "cost_fixpoint: could not unfold `{gen}`"
        replaceMainGoal (← run extras goal)
        return
    let ind ← mkConstWithFreshMVarLevels indName
    let (xs, _, concl) ← forallMetaTelescope (← inferType ind)
    let some step := xs.back? | throwError "cost_fixpoint: internal error"
    let adm := xs[xs.size - 2]!
    let F := concl.appArg!
    let fTy ← whnf (← inferType F)
    -- The seed: the positions of `gen`'s arguments that `F` abstracts. Matching `F`'s body against
    -- the goal fixes the others.
    let args := x.getAppArgs
    let seed ← forallTelescope fTy fun ys _ => do
      let body := (mkAppN F ys).headBeta
      let seed ← ys.mapM fun y => do
        let some k := body.getAppArgs.findIdx? (· == y)
          | throwError "cost_fixpoint: `{gen}`'s fixpoint abstracts something other than an argument"
        pure k
      let target := (seed.zip ys).foldl (fun as (k, y) => as.set! k y) args
      unless ← isDefEq body (mkAppN x.getAppFn target) do
        throwError "cost_fixpoint: could not match{indentExpr x}\nagainst `{gen}`'s fixpoint"
      pure seed
    let seedArgs := seed.map (args[·]!)
    let seedFVars := seedArgs.filter (·.isFVar)
    let postAt (ys : Array Expr) : MetaM Expr := do
      let ys := (seedArgs.zip ys).filterMap fun (a, y) => if a.isFVar then some y else none
      instantiateMVars (post.replaceFVars seedFVars ys)
    let gTy ← inferType F
    let motive ← withLocalDeclD `g gTy fun g => do
      mkLambdaFVars #[g] (← forallTelescope fTy fun ys _ => do
        mkForallFVars ys (← mkAppM ``SPMF.Cost.Always #[mkAppN g ys, ← postAt ys]))
    unless ← isDefEq concl.appFn! motive do
      throwError "cost_fixpoint: could not state the induction motive{indentExpr motive}"
    unless ← isDefEq adm (← mkAdmissible gTy postAt) do
      throwError "cost_fixpoint: could not prove the motive admissible"
    let pf := mkAppN (mkAppN ind xs) seedArgs
    unless ← isDefEq (← inferType pf) ty do
      throwError "cost_fixpoint: the induction does not prove{indentExpr ty}"
    goal.assign pf
    -- One step: the recursive function, `ih`, the seed.
    let recName ← forallBoundedTelescope (← inferType step) (some 1) fun rs _ =>
      rs[0]!.fvarId!.getUserName
    let (_, s) ← step.mvarId!.introN 2 [recName.eraseMacroScopes, `ih]
    let (_, s) ← s.introN seed.size (← seed.mapM (binderName gen ·)).toList
    let s ← s.tryClearMany (seedFVars.map (·.fvarId!))
    let s ← s.withContext do s.replaceTargetDefEq (← Core.betaReduce (← instantiateMVars (← s.getType)))
    replaceMainGoal (← run extras s)

end Basalt.CostFixpoint
