/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt.SPMF.ExpectBound

/-!
# The `expect_fixpoint` Tactic

`expect_fixpoint` reduces an upper bound on a recursive generator's expectation to one step of the
generator: fixpoint induction over the arguments its recursive calls change, admissible because
`SPMF.expect` is continuous, then `expect_bound`.
-/

open Lean Meta Elab Tactic Lean.Order

namespace Basalt.ExpectFixpoint

open Basalt.Walk Basalt.ExpectBound

/-- `admissible fun g => ∀ ys, SPMF.expect (g ys) (f ys) ≤ B ys`, over the binders of `gTy`: one
`admissible_pi_apply` per binder, each with its predicate given, since unification cannot find
it. -/
private partial def mkAdmissible (gTy : Expr) (bound : Array Expr → MetaM (Expr × Expr))
    (ys : Array Expr := #[]) : MetaM Expr := do
  match ← whnf gTy with
  | .forallE n d b _ =>
    withLocalDeclD n d fun y => do
      let inner ← mkAdmissible (b.instantiate1 y) bound (ys.push y)
      let P ← mkLambdaFVars #[y] (← whnfR (← inferType inner)).appArg!
      mkAppOptM ``admissible_pi_apply
        #[d, ← mkLambdaFVars #[y] (b.instantiate1 y), none, P, ← mkLambdaFVars #[y] inner]
  | _ =>
    let (f, B) ← bound ys
    mkAppM ``SPMF.admissible_expect_le #[f, B]

/-- `expect_fixpoint` proves `SPMF.expect (gen a₁ … aₙ) f ≤ B`, at `SPMF` or `SPMF.Cost`, up to
arithmetic. It inducts with `gen.fixpoint_induct` over the arguments some recursive call of `gen`
changes, unfolds one step, and runs `expect_bound` (extra facts go in `expect_fixpoint [h₁, h₂]`).
The first goal is the arithmetic one; in it the recursive function is named after `gen`, the bound
on its every call is `ih`, and the changing arguments keep their names. Only an upper bound can be
proved this way. -/
syntax (name := expectFixpointTac) "expect_fixpoint" (" [" term,* "]")? : tactic

elab_rules : tactic
  | `(tactic| expect_fixpoint $[[$extras,*]]?) => withMainContext do
    let extras := (extras.map (·.getElems)).getD #[]
    let goal ← getMainGoal
    let ty ← whnfR (← instantiateMVars (← goal.getType))
    let bad := m!"expect_fixpoint: expected a goal `SPMF.expect (gen …) f ≤ B`, got{indentExpr ty}"
    unless ty.isAppOfArity ``LE.le 4 do throwError bad
    let mut lhs := ty.getArg! 2
    if lhs.isAppOf ``SPMF.Cost.expectedCost then
      lhs := ((← unfoldDefinition? lhs).getD lhs).headBeta
    unless lhs.isAppOfArity ``SPMF.expect 3 do throwError bad
    let le := ty.appFn!.appFn!
    let ty := mkApp2 le lhs (ty.getArg! 3)
    let goal ← goal.change ty
    goal.withContext do
    let x := lhs.getArg! 1
    let f := lhs.getArg! 2
    let B := ty.getArg! 3
    let some gen := x.getAppFn.constName? | throwError bad
    let some (indName, seed) ← fixpointSeed? gen
      | throwError "expect_fixpoint: `{gen}` is not a `partial_fixpoint`; unfold it and use \
          `expect_bound`"
    let ind ← mkConstWithFreshMVarLevels indName
    let (xs, _, concl) ← forallMetaTelescope (← inferType ind)
    let some step := xs.back? | throwError "expect_fixpoint: internal error"
    let adm := xs[xs.size - 2]!
    let F := concl.appArg!
    let fTy ← whnf (← inferType F)
    let args := x.getAppArgs
    forallTelescope fTy fun ys _ => do
      let target := (seed.zip ys).foldl (fun as (k, y) => as.set! k y) args
      unless ← isDefEq (mkAppN F ys).headBeta (mkAppN x.getAppFn target) do
        throwError "expect_fixpoint: could not match{indentExpr x}\nagainst `{gen}`'s fixpoint"
    let seedArgs := seed.map (args[·]!)
    let seedFVars := seedArgs.filter (·.isFVar)
    let boundAt (ys : Array Expr) : MetaM (Expr × Expr) := do
      let ys := (seedArgs.zip ys).filterMap fun (a, y) => if a.isFVar then some y else none
      return (← instantiateMVars (f.replaceFVars seedFVars ys),
        ← instantiateMVars (B.replaceFVars seedFVars ys))
    let gTy ← inferType F
    let motive ← withLocalDeclD `g gTy fun g => do
      mkLambdaFVars #[g] (← forallTelescope fTy fun ys _ => do
        let (f, B) ← boundAt ys
        mkForallFVars ys (mkApp2 le (← mkAppM ``SPMF.expect #[mkAppN g ys, f]) B))
    unless ← isDefEq concl.appFn! motive do
      throwError "expect_fixpoint: could not state the induction motive{indentExpr motive}"
    unless ← isDefEq adm (← mkAdmissible gTy boundAt) do
      throwError "expect_fixpoint: could not prove the motive admissible"
    let pf := mkAppN (mkAppN ind xs) seedArgs
    unless ← isDefEq (← inferType pf) ty do
      throwError "expect_fixpoint: the induction does not prove{indentExpr ty}"
    goal.assign pf
    let recName ← forallBoundedTelescope (← inferType step) (some 1) fun rs _ =>
      rs[0]!.fvarId!.getUserName
    let (_, s) ← step.mvarId!.introN 2 [recName.eraseMacroScopes, `ih]
    let (_, s) ← s.introN seed.size (← seed.mapM (binderName gen ·)).toList
    let s ← s.tryClearMany (seedFVars.map (·.fvarId!))
    let s ← s.withContext do s.replaceTargetDefEq (← Core.betaReduce (← instantiateMVars (← s.getType)))
    replaceMainGoal (← walkExpect extras s)

end Basalt.ExpectFixpoint
