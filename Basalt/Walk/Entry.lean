/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Lean.Meta.Tactic.Split
import Mathlib.Data.Int.Cast.Basic
import Mathlib.Order.PropInstances
import Basalt.Obs.Presentation
import Basalt.Walk.Basic

/-!
# The Walker's Entry Points

Shared pieces of the `_bound` and `_fixpoint` tactics. A `_bound` tactic restates its goal as a
bound on an observation, runs the walk with `computeBound`, and turns the result into goals for the
user: `pathsBound` gives one goal per path of a demonic precondition, `prunePaths` simplifies an
angelic precondition, and `arithBound` gives one inequality to close by arithmetic. A `_fixpoint`
tactic takes one induction step with `fixpointStep` and then runs its `_bound` tactic. A relational
judgment, one generator at two monads, walks with `walkRel`, and takes its step with `relFixpoint`.
-/
open Lean Meta Elab Tactic Lean.Order

namespace Basalt.Walk

/-- The facts a caller passes a walk, `[h₁, h₂]`: each is tried at every leaf. -/
syntax walkFacts := " [" term,* "]"

/-- The terms of `walkFacts`, none when they are absent. -/
def walkFacts.terms : Option (TSyntax ``walkFacts) → Array Term
  | some stx => match stx with
    | `(walkFacts| [$ts,*]) => ts.getElems
    | _ => #[]
  | none => #[]

/-! ## Introducing a conditional precondition -/

theorem ite_intro {p : Prop} [Decidable p] {c d : Prop} (hc : ∀ _h : p, c) (hd : ∀ _h : ¬p, d) :
    if p then c else d := by split <;> simp_all

theorem dite_intro {p : Prop} [Decidable p] {c : p → Prop} {d : ¬p → Prop} (hc : ∀ h, c h)
    (hd : ∀ h, d h) : if h : p then c h else d h := by split <;> simp_all

theorem dite_const {p : Prop} [Decidable p] {c : Prop} : (if _h : p then c else c) = c := by
  split <;> rfl

/-! ## Computing a bound -/

/-- `b ≤ O.spec g post` when `lower`, and `O.spec g post ≤ b` otherwise, walked: the bound `b` it
computed, the proof of the inequality, and the goals the walk left. `O` is the observation `obs`. -/
def computeBound (extras : Array Term) (obs : Name) (lower : Bool) (g post : Expr) :
    TermElabM (Expr × Expr × List MVarId) := do
  let gTy ← instantiateMVars (← inferType g)
  let spec := mkApp (← mkAppOptM ``Obs.spec #[none, none, none, none, none, none,
    some (mkConst obs [← getDecLevel gTy]), none, some g]) post
  let b ← mkFreshExprMVar (← inferType spec)
  let pf ← mkFreshExprMVar (← if lower then mkAppM ``LE.le #[b, spec] else mkAppM ``LE.le #[spec, b])
  let rest ← walk extras pf.mvarId!
  return (← instantiateMVars b, pf, rest)

/-- `admissible fun g => ∀ ys, P ys (g ys)`, over the binders of `gTy`, from `leaf ys`, a proof of
`admissible (P ys)`: one `admissible_pi_apply` per binder, each with its predicate given, since
unification cannot find it. -/
private partial def mkAdmissible (gTy : Expr) (leaf : Array Expr → MetaM Expr)
    (ys : Array Expr := #[]) : MetaM Expr := do
  -- `whnfR`, here and for `fTy` in `fixpointStep`: `whnf` unfolds `IOModel α` to a function type.
  -- A generator with no arguments then fails `io_fixpoint` on an `admissible_pi_apply` mismatch.
  match ← whnfR gTy with
  | .forallE n d b _ =>
    withLocalDeclD n d fun y => do
      let inner ← mkAdmissible (b.instantiate1 y) leaf (ys.push y)
      let P ← mkLambdaFVars #[y] (← whnfR (← inferType inner)).appArg!
      mkAppOptM ``admissible_pi_apply
        #[d, ← mkLambdaFVars #[y] (b.instantiate1 y), none, P, ← mkLambdaFVars #[y] inner]
  | _ => leaf ys

/-- One step of `gen.fixpoint_induct` on `goal`, a statement `P (gen a₁ … aₙ)` about the generator
application `x`: the induction is over the arguments some recursive call of `gen` changes, and the
goal returned has the recursive function (named after `gen`), `ih`, and those arguments introduced.
`adm` proves `admissible P`; the motive is read off it, generalized over the changing arguments. A
`gen` that is not recursive is unfolded instead. `tac` is the caller, and `boundTac` the tactic it
runs on the goal returned, for the errors. -/
def fixpointStep (tac boundTac : String) (x adm : Expr) (goal : MVarId) : TermElabM MVarId :=
  goal.withContext do
  let ty ← instantiateMVars (← goal.getType)
  let some gen := x.getAppFn.constName?
    | throwError "{tac}: expected a generator applied to its arguments, got{indentExpr x}"
  if isCombinator (← getEnv) gen then
    throwError "{tac}: `{gen}` is a combinator, not a generator definition; prove a bound on a \
      combinator term with `{boundTac}`"
  let some (indName, seed) ← fixpointSeed? gen
    | if ← isRecursiveDefinition gen then
        throwError "{tac}: `{gen}` is recursive but not a `partial_fixpoint`; induct on its \
          decreasing argument, unfold it, and apply `{boundTac}`"
      let [goal] ← Lean.Elab.Tactic.run goal (evalTactic (← `(tactic| unfold $(mkIdent gen))))
        | throwError "{tac}: could not unfold `{gen}`"
      return goal
  let ind ← mkConstWithFreshMVarLevels indName
  let (xs, _, concl) ← forallMetaTelescope (← inferType ind)
  let some step := xs.back? | throwError "{tac}: internal error"
  let admGoal := xs[xs.size - 2]!
  let F := concl.appArg!
  let fTy ← whnfR (← inferType F)
  -- Matching `F`'s body against the goal fixes the arguments outside the seed.
  let args := x.getAppArgs
  forallTelescope fTy fun ys _ => do
    let target := (seed.zip ys).foldl (fun as (k, y) => as.set! k y) args
    unless ← isDefEq (mkAppN F ys).headBeta (mkAppN x.getAppFn target) do
      throwError "{tac}: could not match{indentExpr x}\nagainst `{gen}`'s fixpoint"
  let seedArgs := seed.map (args[·]!)
  let seedFVars := seedArgs.filter (·.isFVar)
  let adm ← instantiateMVars adm
  let admAt (ys : Array Expr) : MetaM Expr := do
    let ys := (seedArgs.zip ys).filterMap fun (a, y) => if a.isFVar then some y else none
    return adm.replaceFVars seedFVars ys
  let gTy ← inferType F
  let motive ← withLocalDeclD `g gTy fun g => do
    mkLambdaFVars #[g] (← forallTelescope fTy fun ys _ => do
      let P := (← whnfR (← inferType (← admAt ys))).appArg!
      mkForallFVars ys (mkApp P (mkAppN g ys)).headBeta)
  unless ← isDefEq concl.appFn! motive do
    throwError "{tac}: could not state the induction motive{indentExpr motive}"
  unless ← isDefEq admGoal (← mkAdmissible gTy admAt) do
    throwError "{tac}: could not prove the motive admissible"
  let pf := mkAppN (mkAppN ind xs) seedArgs
  unless ← isDefEq (← inferType pf) ty do
    throwError "{tac}: the induction does not prove{indentExpr ty}"
  goal.assign pf
  -- One step: the recursive function, `ih`, the seed.
  let recName ← forallBoundedTelescope (← inferType step) (some 1) fun rs _ =>
    rs[0]!.fvarId!.getUserName
  let (_, s) ← step.mvarId!.introN 2 [recName.eraseMacroScopes, `ih]
  let (_, s) ← s.introN seed.size (← seed.mapM (binderName gen ·)).toList
  let s ← s.tryClearMany (seedFVars.map (·.fvarId!))
  s.withContext do s.replaceTargetDefEq (← Core.betaReduce (← instantiateMVars (← s.getType)))

/-- The sub-generators of `g` that are a `match` on something in the context, outermost first: a
`match` with no loose bound variable, whose discriminants are therefore not drawn values. -/
private partial def ctxMatches (env : Environment) (e : Expr) : Array Expr :=
  let here := if !e.hasLooseBVars && isMatcherAppCore env e then #[e] else #[]
  here ++ match e with
  | .app f a => ctxMatches env f ++ ctxMatches env a
  | .lam _ t b _ | .forallE _ t b _ => ctxMatches env t ++ ctxMatches env b
  | .letE _ t v b _ => ctxMatches env t ++ ctxMatches env v ++ ctxMatches env b
  | .mdata _ b | .proj _ _ b => ctxMatches env b
  | _ => #[]

/-- The cases of `goal`, a statement about the generator `g`, when `g` contains a sub-generator that
is a `match` on something in the context (a generator defined by cases on its seed): `split`'s, one
per alternative. The walk itself does not enter a `match`, and this has to happen before a bound is
a metavariable. -/
def splitMatch? (goal : MVarId) (g : Expr) : MetaM (Option (List MVarId)) := do
  let g ← instantiateMVars g
  let gHead := (← inferType g).getAppFn
  -- A `match` that reduces is the walk's: only a stuck one is split. One that is not a generator
  -- (inside a proof or a value) is not the walk's concern.
  let some m ← (ctxMatches (← getEnv) g).findM? fun m => do
      pure ((← whnfCore m) == m) <&&> (return (← inferType m).getAppFn == gHead)
    | return none
  let some cases ← observing? (Split.splitMatch goal m) | return none
  let old := (← goal.getDecl).lctx
  -- A pattern's variables are the alternative's, under its names.
  let named ← cases.mapM fun (c : MVarId) => c.withContext do
    let mut c := c
    for d in ← getLCtx do
      if !old.contains d.fvarId && d.userName.hasMacroScopes then
        c ← c.rename d.fvarId ((← c.getDecl).lctx.getUnusedName d.userName.eraseMacroScopes)
    pure c
  return some named

/-- `goal`, a residual goal of a walk begun in `lctx`, with its metavariables instantiated and
`tidyExpr` applied, in the target and every hypothesis, and each hypothesis the walk introduced made
inaccessible under the name it was given. A fact passed to the walk can mention a drawn value by
name; the residual goal cannot. -/
def tidy (lctx : LocalContext) (goal : MVarId) : MetaM MVarId := goal.withContext do
  goal.setTag .anonymous
  let mut goal := goal
  for d in ← getLCtx do
    unless d.isImplementationDetail do
      let t ← tidyExpr d.type
      if t != d.type then goal ← goal.replaceLocalDeclDefEq d.fvarId t
      unless lctx.contains d.fvarId do
        goal ← goal.rename d.fvarId (← mkFreshUserName d.userName.eraseMacroScopes)
  goal.withContext do goal.replaceTargetDefEq (← tidyExpr (← goal.getType))

/-! ## Relating one generator at two monads -/

/-- The arguments of `goal`, which must be `rel … y x`: the relation's own first, then `y` and `x`,
the last two. `tac` is the caller, for the error. -/
def parseRel (tac : String) (rel : Name) (goal : MVarId) : MetaM (Array Expr) := do
  let ty ← whnfR (← instantiateMVars (← goal.getType))
  unless ty.isAppOf rel && 2 ≤ ty.getAppNumArgs do
    throwError "{tac}: expected a goal `{.ofConstName rel} … (gen …) (gen …)`, got{indentExpr ty}"
  return ty.getAppArgs

/-- Walk `goal`, a `rel … y x`, splitting a `match` on the generator's arguments first. -/
partial def walkRel (tac : String) (rel : Name) (extras : Array Term) (goal : MVarId) :
    TermElabM (List MVarId) := goal.withContext do
  let args ← parseRel tac rel goal
  if let some cases ← splitMatch? goal args[args.size - 2]! then
    return ← cases.flatMapM (walkRel tac rel extras)
  let lctx := (← goal.getDecl).lctx
  (← walk extras goal).mapM fun g => tidy lctx g

/-- `rel … (gen a₁ … aₙ) (gen a₁ … aₙ)`: one step of `gen.fixpoint_induct` on `y`'s side, admissible
by `adm` of the goal's arguments, `x`'s side unfolded one step, and the two walked together
(`walkRel`). A `gen` that is not recursive is unfolded on both sides and walked. -/
def relFixpoint (tac boundTac : String) (rel : Name) (adm : Array Expr → MetaM Expr)
    (extras : Array Term) (goal : MVarId) : TermElabM (List MVarId) := goal.withContext do
  let args ← parseRel tac rel goal
  let y := args[args.size - 2]!
  let some gen := y.getAppFn.constName?
    | throwError "{tac}: expected a generator applied to its arguments, got{indentExpr y}"
  let step ← fixpointStep tac boundTac y (← adm args) goal
  -- `eq_def`, not the equation lemmas: a generator defined by cases has one per case.
  let step ← if (← fixpointSeed? gen).isSome then
      match ← Lean.Elab.Tactic.run step
          (evalTactic (← `(tactic| rw [$(mkCIdent (gen ++ `eq_def)):ident]))) with
      | [g] => pure g
      | _ => throwError "{tac}: could not unfold `{gen}`"
    else pure step
  walkRel tac rel extras step

/-- One goal per path through a computed demonic precondition: its `∀` and `→` introduced, its `∧`
and `if` split. Only a connective that is there syntactically is split, so that a postcondition
defined as a conjunction stays folded. -/
partial def splitPaths (g : MVarId) : MetaM (List MVarId) := g.withContext do
  let ty := (← reduceCtorProjs (← g.getType)).consumeMData
  if ty.isConstOf ``True then
    g.assign (mkConst ``True.intro)
    return []
  if ty.isForall then
    let (_, g) ← g.intro1P
    return ← splitPaths g
  if ty.isAppOf ``List.foldr then
    return ← splitPaths (← g.replaceTargetDefEq (← whnf ty))
  for (head, arity, lem) in [(``And, 2, ``And.intro), (``dite, 5, ``dite_intro),
      (``ite, 5, ``ite_intro)] do
    if ty.isAppOfArity head arity then
      if let some gs ← observing? (applyExact g (← mkConstWithFreshMVarLevels lem)) then
        return ← gs.flatMapM splitPaths
  return [g]

/-- The computed angelic precondition `g`, pruned: its `List.foldr Or False` and `List.map` over a
literal list of branches reduced to a disjunction, then the disjuncts that are refuted outright
removed (a constructor clash, a closed weight that is `0`), the trivial conjuncts dropped, and a
draw that is the value itself eliminated. It
never picks between disjuncts that survive, and closes the goal when nothing is left to choose. -/
def prunePaths (g : MVarId) : TermElabM (List MVarId) := g.withContext do
  let ty ← Meta.transform (← instantiateMVars (← g.getType)) (pre := fun e => do
    unless e.isAppOf ``List.foldr do return .continue
    let e' ← whnf e
    return if e' == e then .continue else .visit e')
  let g ← g.replaceTargetDefEq (← tidyExpr (← Core.betaReduce ty))
  let pruned ← observing? <| Lean.Elab.Tactic.run g <| evalTactic (← `(tactic|
    simp only [reduceCtorEq, Nat.lt_irrefl, Nat.reduceLT, Int.reduceLT, Nat.cast_ofNat,
      Pi.top_apply, Prop.top_eq_true, false_or, or_false, true_or, or_true, true_and, and_true,
      false_and, and_false, exists_false, exists_prop, exists_eq_right, ite_self,
      Basalt.Walk.dite_const]))
  return pruned.getD [g]


/-- Prove `goal`, which is `O.spec g post` for `O` the observation `obs` into `Prop`, by the walk of
a lower bound: one goal per path through the precondition it computed (`splitPaths`), then whatever
else the walk left, tidied. -/
def pathsBound (extras : Array Term) (obs : Name) (g post : Expr) (goal : MVarId) :
    TermElabM (List MVarId) := do
  let lctx := (← goal.getDecl).lctx
  let (pre, structural, rest) ← computeBound extras obs true g post
  let paths ← mkFreshExprMVar pre
  goal.assign (mkApp structural paths)
  ((← splitPaths paths.mvarId!) ++ rest).mapM fun g => tidy lctx g

/-- Prove `goal`, which is `other ≤ O.spec g post` when `lower` and `O.spec g post ≤ other`
otherwise, for `O` the observation `obs`: the arithmetic goal relating `other` to the bound the walk
computed, then whatever else the walk left, tidied. -/
def arithBound (extras : Array Term) (obs : Name) (lower : Bool) (g post other : Expr)
    (goal : MVarId) : TermElabM (List MVarId) := do
  let lctx := (← goal.getDecl).lctx
  let (b, structural, rest) ← computeBound extras obs lower g post
  let arith ← mkFreshExprMVar (← if lower then mkAppM ``LE.le #[other, b]
    else mkAppM ``LE.le #[b, other])
  goal.assign (← if lower then mkAppM ``le_trans #[arith, structural]
    else mkAppM ``le_trans #[structural, arith])
  (arith.mvarId! :: rest).mapM fun g => tidy lctx g

end Basalt.Walk
