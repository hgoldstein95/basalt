/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
module

public meta import Lean.Meta.Tactic.Split
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Order.PropInstances
public import Basalt.Obs.Presentation
import Basalt.GenRel.Basic
public meta import Basalt.Walk.Basic

/-!
# The Walker's Entry Points

The `walk` tactic, and the pieces a specialized tactic builds on. `computeBound` walks a statement
on an observation, and `walkRel` a relation between one generator at two monads; the observation's
algebra turns the result into goals (`preconditionBound`, `arithBound`).
-/

public meta section

open Lean Meta Elab Tactic Lean.Order

namespace Basalt.Walk

/-- The facts a caller passes a walk, `[h₁, h₂]`: each is tried at every leaf. A callee's law
reaches the walk only this way, stated on an observation (`h.obs`). -/
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
  -- An observation over a monad of fixed universe has no universe parameter of its own.
  let lvls ← if (← getConstInfo obs).levelParams.isEmpty then pure [] else pure [← getDecLevel gTy]
  let spec := mkApp (← mkAppOptM ``Obs.spec #[none, none, none, none, none, none,
    some (mkConst obs lvls), none, some g]) post
  let b ← mkFreshExprMVar (← inferType spec)
  let pf ← mkFreshExprMVar (← if lower then mkAppM ``LE.le #[b, spec] else mkAppM ``LE.le #[spec, b])
  walkTimes.set {}
  let tw0 ← IO.monoMsNow
  let rest ← walk extras pf.mvarId!
  let tw1 ← IO.monoMsNow
  if basalt.walk.profile.get (← getOptions) then logInfo m!"walk itself: {tw1 - tw0} ms"
  let ts ← walkTimes.get
  let sorted := ts.toArray.qsort (fun a b => a.2.1 > b.2.1)
  let line := sorted.toList.map fun (k, (ns, n)) => k ++ "=" ++ toString (ns / 1000000) ++ "ms/" ++ toString n
  if basalt.walk.profile.get (← getOptions) then logInfo m!"walk ops: {line}"
  let t0 ← IO.monoMsNow
  let r ← instantiateMVars b
  let t1 ← IO.monoMsNow
  if basalt.walk.profile.get (← getOptions) then logInfo m!"walk final instantiateMVars of the bound: {t1 - t0} ms"
  return (r, pf, rest)

/-- `admissible fun g => ∀ ys, P ys (g ys)`, over the binders of `gTy`, from `leaf ys`, a proof of
`admissible (P ys)`: one `admissible_pi_apply` per binder, each with its predicate given, since
unification cannot find it. -/
private partial def mkAdmissible (gTy : Expr) (leaf : Array Expr → MetaM Expr)
    (ys : Array Expr := #[]) : MetaM Expr := do
  -- `whnfR`, here and for `fTy` in `fixpointStep`: `whnf` unfolds `IOModel α` to a function type.
  -- A generator with no arguments then fails `walk fixpoint` on an `admissible_pi_apply` mismatch.
  match ← whnfR gTy with
  | .forallE n d b _ =>
    withLocalDeclD n d fun y => do
      let inner ← mkAdmissible (b.instantiate1 y) leaf (ys.push y)
      let P ← mkLambdaFVars #[y] (← whnfR (← inferType inner)).appArg!
      mkAppOptM ``admissible_pi_apply
        #[d, ← mkLambdaFVars #[y] (b.instantiate1 y), none, P, ← mkLambdaFVars #[y] inner]
  | _ => leaf ys

/-- The generator definition that `x` applies, and its `fixpointSeed?`: `none` when it is not
recursive. The statement to prove about `x` is of judgment `j`, on the observation `obs?` for a
bound, which must not already know `x`'s head (`Judgment.knows`). `tac` is the caller,
`combinatorHint` how to prove the statement about a combinator term, and `recursiveHint` how to
prove it about a recursive generator that is not a `partial_fixpoint` once inducted on, for the
errors. -/
def fixpointGen (tac combinatorHint recursiveHint : String) (j : Judgment) (obs? : Option Name)
    (x : Expr) : MetaM (Name × Option (Name × Array Nat)) := do
  let some gen := x.getAppFn.constName?
    | throwError "{tac}: expected a generator applied to its arguments, got{indentExpr x}"
  if ← j.knows obs? x then
    throwError "{tac}: `{gen}` is a combinator, not a generator definition; prove {combinatorHint}"
  let seed? ← fixpointSeed? gen
  if seed?.isNone && (← isRecursiveDefinition gen) then
    throwError "{tac}: `{gen}` is recursive but not a `partial_fixpoint`; induct on its decreasing \
      argument, {recursiveHint}"
  return (gen, seed?)

/-- One step of `gen.fixpoint_induct` on `goal`, a statement `P (gen a₁ … aₙ)` of judgment `j`
(on the observation `obs?`, for a bound) about the generator application `x`: the induction is over
the arguments some recursive call of `gen` changes, and the goal returned has the recursive function
(named after `gen`), `ih`, and those arguments introduced. `adm` proves `admissible P`; the motive is
read off it, generalized over the changing arguments. A `gen` that is not recursive is unfolded
instead, which the `Bool` returned says. `tac` is the caller, and `boundTac` the tactic it runs on
the goal returned, for the errors. -/
def fixpointStep (tac boundTac : String) (j : Judgment) (obs? : Option Name) (x adm : Expr)
    (goal : MVarId) : TermElabM (MVarId × Bool) := goal.withContext do
  let ty ← instantiateMVars (← goal.getType)
  let (gen, seed?) ← fixpointGen tac s!"a bound on a combinator term with `{boundTac}`"
    s!"unfold it, and apply `{boundTac}`" j obs? x
  let some (indName, seed) := seed?
    | let [goal] ← Lean.Elab.Tactic.run goal (evalTactic (← `(tactic| unfold $(mkIdent gen))))
        | throwError "{tac}: could not unfold `{gen}`"
      return (goal, false)
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
  let s ← s.withContext do
    s.replaceTargetDefEq (← Core.betaReduce (← instantiateMVars (← s.getType)))
  return (s, true)

/-- `goal`, a residual goal of a walk begun in `lctx`, with its metavariables instantiated and
`tidyExpr` applied, in the target and every hypothesis, a `match` of one value in the target
collapsed, and each hypothesis the walk introduced made inaccessible under the name it was given. A
fact passed to the walk can mention a drawn value by name; the residual goal cannot. -/
def tidy (lctx : LocalContext) (goal : MVarId) : MetaM MVarId := goal.withContext do
  goal.setTag .anonymous
  let mut goal := goal
  for d in ← getLCtx do
    -- A hypothesis the walk began with is the caller's, and no draw of the walk is in it: only
    -- those the walk introduced are tidied (and renamed).
    unless d.isImplementationDetail || lctx.contains d.fvarId do
      let t ← tidyExpr d.type
      if t != d.type then goal ← goal.replaceLocalDeclDefEq d.fvarId t
      goal ← goal.rename d.fvarId (← mkFreshUserName d.userName.eraseMacroScopes)
  goal ← goal.withContext do goal.replaceTargetDefEq (← tidyExpr (← goal.getType))
  goal.withContext do
    let ty ← goal.getType
    applySimpResultToTarget goal ty (← collapseMatches ty)

/-! ## Relating one generator at two monads -/

/-- The arguments of `goal`, which must be `rel … y x`: the relation's own first, then `y` and `x`,
the last two. `tac` is the caller, for the error. -/
def parseRel (tac : String) (rel : Name) (goal : MVarId) : MetaM (Array Expr) := do
  let ty ← whnfR (← instantiateMVars (← goal.getType))
  unless ty.isAppOf rel && 2 ≤ ty.getAppNumArgs do
    throwError "{tac}: expected a goal `{.ofConstName rel} … (gen …) (gen …)`, got{indentExpr ty}"
  return ty.getAppArgs

/-- Walk `goal`, a `rel … y x`. -/
def walkRel (tac : String) (rel : Name) (extras : Array Term) (goal : MVarId) :
    TermElabM (List MVarId) := goal.withContext do
  discard <| parseRel tac rel goal
  let lctx := (← goal.getDecl).lctx
  (← walk extras goal).mapM fun g => tidy lctx g

/-- The `admissible` field of `genRel`, the proof that `rel` is a `GenRel`, instantiated to the
motive `fun y => rel … y x` of the goal `rel … y x` whose arguments are `args`. `tac` is the caller,
for the error. -/
private def relAdmissible (tac : String) (rel genRel : Name) (args : Array Expr) : MetaM Expr := do
  let w ← mkConstWithFreshMVarLevels genRel
  let (xs, bis, _) ← forallMetaTelescope (← inferType w)
  let adm ← applyBridge ``GenRel.admissible (mkAppN w xs)
  let (ys, _, concl) ← forallMetaTelescope (← inferType adm)
  let i := args.size - 2
  let P ← withLocalDeclD `y (← inferType args[i]!) fun y => do
    mkLambdaFVars #[y] (← mkAppOptM rel ((args.set! i y).map some))
  unless ← isDefEq concl.appArg! P do
    throwError "{tac}: `{.ofConstName genRel}` does not prove{indentExpr P}\nadmissible"
  synthInstMVars xs bis
  instantiateMVars (mkAppN adm ys)

/-- `rel … (gen a₁ … aₙ) (gen a₁ … aₙ)`: one step of `gen.fixpoint_induct` on `y`'s side, admissible
by the `admissible` field of `genRel`, the proof that `rel` is a `GenRel`, `x`'s side unfolded one
step, and the two walked together (`walkRel`). A `gen` that is not recursive is unfolded on both
sides and walked. -/
def relFixpoint (tac boundTac : String) (rel genRel : Name) (extras : Array Term)
    (goal : MVarId) : TermElabM (List MVarId) := goal.withContext do
  let args ← parseRel tac rel goal
  let y := args[args.size - 2]!
  let some gen := y.getAppFn.constName?
    | throwError "{tac}: expected a generator applied to its arguments, got{indentExpr y}"
  let (step, inducted) ← fixpointStep tac boundTac (.rel rel genRel) none y
    (← relAdmissible tac rel genRel args) goal
  -- `eq_def`, not the equation lemmas: a generator defined by cases has one per case.
  let step ← if inducted then
      unless (← getEnv).contains (gen ++ `eq_def) do executeReservedNameAction (gen ++ `eq_def)
      match ← Lean.Elab.Tactic.run step
          (evalTactic (← `(tactic| rw [$(mkCIdent (gen ++ `eq_def)):ident]))) with
      | [g] => pure g
      | _ => throwError "{tac}: could not unfold `{gen}`"
    else pure step
  walkRel tac rel extras step

/-- `g`, one case of a `split` begun in `old`, with the equations `split` introduced solved: each
that is between constructors by `injection`, which closes a case that is a clash, each with a
variable side by `subst`. Then the variables it introduced that nothing mentions are cleared; a
hypothesis it introduced (an earlier pattern that did not match) stays. -/
private partial def solveSplitEqs (old : LocalContext) (g : MVarId) : MetaM (Option MVarId) :=
  g.withContext do
  for d in ← getLCtx do
    if old.contains d.fvarId || !d.userName.hasMacroScopes || !d.type.isEq then continue
    if let some g' ← subst? g d.fvarId then return ← solveSplitEqs old g'
    if let some r ← observing? (injection g d.fvarId) then
      match r with
      | .solved => return none
      | .subgoal g' .. => return ← solveSplitEqs old g'
  let fresh ← (← getLCtx).foldlM (init := #[]) fun acc d => do
    if old.contains d.fvarId || !d.userName.hasMacroScopes || (← isProp d.type) then return acc
    return acc.push d.fvarId
  some <$> g.tryClearMany fresh

/-- The cases of `g` by the first `match` in `part` of its target on something in the context, each
with its equations solved (`solveSplitEqs`); `none` when there is no such `match`. -/
private def splitCtxMatch? (part : Expr → Expr) (g : MVarId) : MetaM (Option (List MVarId)) :=
  g.withContext do
  let ty ← instantiateMVars (← g.getType)
  -- the matches the caller decides itself (`basalt.walk.keepMatchesOn`)
  let keep := ((basalt.walk.keepMatchesOn.get (← getOptions)).splitOn ",").filter (· ≠ "") |>.map String.toName
  let mut except : ExprSet := {}
  unless keep.isEmpty do
    let found ← IO.mkRef (#[] : Array Expr)
    Meta.forEachExpr (part ty) fun e => do
      if let some m ← matchMatcherApp? e then
        if m.discrs.any (fun d => (d.find? fun x => keep.any (x.isConstOf ·)).isSome) then
          found.modify (·.push e)
    for e in ← found.get do except := except.insert e
  let some m ← findSplit? (part ty) .match except | return none
  let old ← getLCtx
  let some gs ← observing? (Split.splitMatch g m) | return none
  some <$> gs.filterMapM fun g => do
    g.setTag .anonymous
    solveSplitEqs old g

/-- `g`, an inequality whose `i`-th argument is a computed bound, one goal per case of each `match`
in the bound on something in the context. -/
partial def splitBoundMatches (i : Nat) (g : MVarId) : MetaM (List MVarId) := do
  let some gs ← splitCtxMatch? (·.getArg! i) g | return [g]
  gs.flatMapM (splitBoundMatches i)

/-- One goal per path through a computed demonic precondition: its `∀` and `→` introduced, its `∧`,
`if` and `match` split. Only a connective that is there syntactically is split, so that a
postcondition defined as a conjunction stays folded. -/
partial def splitPaths (g : MVarId) (reduced : Bool := false) : MetaM (List MVarId) := g.withContext do
  -- The projections out of constructors are reduced once, in the goal itself: an `intro` or a split
  -- of `∧`, `if` or `dite` leaves subterms of an already reduced statement, and only unfolding a
  -- `foldr` or splitting a `match` can make new ones. Reducing the whole remaining precondition at
  -- every step is quadratic in its size.
  let g ← if reduced then pure g else g.replaceTargetDefEq (← reduceCtorProjs (← g.getType))
  let ty := (← instantiateMVars (← g.getType)).consumeMData
  if ty.isConstOf ``True then
    g.assign (mkConst ``True.intro)
    return []
  if ty.isForall then
    let (_, g) ← g.intro1P
    return ← splitPaths g true
  if ty.isAppOf ``List.foldr then
    return ← splitPaths (← g.replaceTargetDefEq (← whnf ty))
  if (← matchMatcherApp? ty).isSome then
    if let some ty' ← reduceRecMatcher? ty then
      return ← splitPaths (← g.replaceTargetDefEq ty'.headBeta)
    let r ← collapseMatches ty
    if r.expr != ty then return ← splitPaths (← applySimpResultToTarget g ty r)
    let old ← getLCtx
    if let some gs ← observing? (Split.splitMatch g ty) then
      return ← gs.flatMapM fun g => do
        let some g ← solveSplitEqs old g | return []
        splitPaths g
  for (head, arity, lem) in [(``And, 2, ``And.intro), (``dite, 5, ``dite_intro),
      (``ite, 5, ``ite_intro)] do
    if ty.isAppOfArity head arity then
      if let some gs ← observing? (applyExact g (← mkConstWithFreshMVarLevels lem)) then
        return ← gs.flatMapM (splitPaths · true)
  return [g]

/-- Two terms that differ in a constructor or a literal where both have one: never equal. -/
private partial def clashes (a b : Expr) : MetaM Bool := do
  let a ← instantiateMVars a
  let b ← instantiateMVars b
  match a, b with
  | .lit l₁, .lit l₂ => return l₁ != l₂
  | _, _ =>
    let env ← getEnv
    let some f := a.getAppFn.constName? | return false
    let some g := b.getAppFn.constName? | return false
    let some (.ctorInfo c) := env.find? f | return false
    let some (.ctorInfo _) := env.find? g | return false
    if f != g then return true
    let as := a.getAppArgs; let bs := b.getAppArgs
    unless as.size == bs.size do return false
    for i in [c.numParams:as.size] do
      if ← clashes as[i]! bs[i]! then return true
    return false

/-- `e` with the disjuncts no choice can satisfy dropped (a conjunct equating clashing
constructors, under any `∃`): `none` when none is left, else the smaller proposition and, unless it
is `e` itself, a proof that it implies `e`. Dropping a disjunct only strengthens the goal. -/
private partial def dropClashing (e : Expr) : MetaM (Option (Expr × Option Expr)) := do
  let e ← instantiateMVars e
  if e.isConstOf ``False then return none
  if e.isAppOfArity ``Or 2 then
    let a := e.getArg! 0; let b := e.getArg! 1
    let ra ← dropClashing a
    let rb ← dropClashing b
    match ra, rb with
    | none, none => return none
    | some (a', pa), none =>
      let inl ← withLocalDeclD `h a' fun h => do
        let ha := match pa with | some p => mkApp p h | none => h
        mkLambdaFVars #[h] (← mkAppOptM ``Or.inl #[a, b, ha])
      return some (a', some inl)
    | none, some (b', pb) =>
      let inr ← withLocalDeclD `h b' fun h => do
        let hb := match pb with | some p => mkApp p h | none => h
        mkLambdaFVars #[h] (← mkAppOptM ``Or.inr #[a, b, hb])
      return some (b', some inr)
    | some (a', pa), some (b', pb) =>
      if pa.isNone && pb.isNone then return some (e, none)
      let pa := pa.getD (← withLocalDeclD `h a fun h => mkLambdaFVars #[h] h)
      let pb := pb.getD (← withLocalDeclD `h b fun h => mkLambdaFVars #[h] h)
      -- `Or.imp : (a' → a) → (b' → b) → a' ∨ b' → a ∨ b`
      return some (← mkAppM ``Or #[a', b'], some (← mkAppM ``Or.imp #[pa, pb]))
  if e.isAppOfArity ``And 2 then
    let a := e.getArg! 0; let b := e.getArg! 1
    let some (a', pa) ← dropClashing a | return none
    let some (b', pb) ← dropClashing b | return none
    if pa.isNone && pb.isNone then return some (e, none)
    let pa := pa.getD (← withLocalDeclD `h a fun h => mkLambdaFVars #[h] h)
    let pb := pb.getD (← withLocalDeclD `h b fun h => mkLambdaFVars #[h] h)
    return some (← mkAppM ``And #[a', b'], some (← mkAppM ``And.imp #[pa, pb]))
  if e.isAppOfArity ``Exists 2 then
    let p := e.getArg! 1
    let .lam n ty body bi := p | return some (e, none)
    let r ← withLocalDecl n bi ty fun x => do
      let some (b', pb) ← dropClashing (body.instantiate1 x) | return none
      match pb with
      | none => return some none
      | some pb => return some (some (← mkLambdaFVars #[x] b', ← mkLambdaFVars #[x] pb))
    match r with
    | none => return none
    | some none => return some (e, none)
    | some (some (q, h)) =>
      -- `Exists.imp : (∀ a, q a → p a) → (∃ a, q a) → ∃ a, p a`
      return some (← mkAppM ``Exists #[q], some (← mkAppM ``Exists.imp #[h]))
  if let some (_, a, b) := e.eq? then
    if ← clashes a b then return none
  return some (e, none)

/-- The computed angelic precondition `g`, pruned: its `List.foldr Or False` and `List.map` over a
literal list of branches reduced to a disjunction, a `match` of one value collapsed, then the
disjuncts that are refuted outright removed (a constructor clash, a closed weight that is `0`), the
trivial conjuncts dropped, and a draw that is the value itself eliminated. It never picks between
disjuncts that survive, and closes the goal when nothing is left to choose. -/
private def prune (g : MVarId) : TermElabM (List MVarId) := g.withContext do
  let ty ← timeIt "prune.transform" <| Meta.transform (← instantiateMVars (← g.getType)) (pre := fun e => do
    unless e.isAppOf ``List.foldr do return .continue
    let e' ← whnf e
    return if e' == e then .continue else .visit e')
  let g ← timeIt "prune.tidy" do g.replaceTargetDefEq (← tidyExpr (← Core.betaReduce ty))
  -- the `match`es on constructors reduced, definitionally, before `simp` (whose reduction of them is
  -- most of its time) goes through them (`basalt.walk.pruneReduceMatch`)
  let g ← if !basalt.walk.pruneReduceMatch.get (← getOptions) then pure g else timeIt "prune.iota" do
    let ty ← instantiateMVars (← g.getType)
    let ty' ← Meta.transform ty (post := fun e => do
      unless e.isApp do return .done e
      -- (only a guard's `match`, to `true` or `false`: a branch's code is left as it is)
      match ← Meta.reduceMatcher? e with
      | Meta.ReduceMatcherResult.reduced e' =>
        let r ← whnfR e'.headBeta
        if r.isConstOf ``Bool.true || r.isConstOf ``Bool.false then return .done r
        return .done e
      | _ => return .done e)
    if ty' == ty then pure g else g.replaceTargetDefEq ty'
  -- the branches whose constructor clashes with the value, dropped before `simp` goes through them
  -- (`basalt.walk.pruneDropClashing`)
  let g ← if !basalt.walk.pruneDropClashing.get (← getOptions) then pure g else timeIt "prune.drop" do
    let ty ← instantiateMVars (← g.getType)
    match ← dropClashing ty with
    | some (ty', some pf) =>
      let g' ← mkFreshExprSyntheticOpaqueMVar ty' (← g.getTag)
      g.assign (mkApp pf g')
      pure g'.mvarId!
    | _ => pure g
  -- (`basalt.walk.pruneDischarge` false: no side conditions discharged)
  let tac ← if !basalt.walk.pruneDischarge.get (← getOptions) then
      `(tactic| simp (config := { maxDischargeDepth := 0 }) only [reduceCtorEq, Nat.lt_irrefl, Nat.reduceLT, Int.reduceLT, Nat.cast_ofNat,
      Pi.top_apply, Prop.top_eq_true, false_or, or_false, true_or, or_true, true_and, and_true,
      false_and, and_false, exists_false, exists_prop, exists_eq_right, ite_self,
      Basalt.Walk.dite_const, Basalt.Walk.matchConst])
    else
      `(tactic| simp only [reduceCtorEq, Nat.lt_irrefl, Nat.reduceLT, Int.reduceLT, Nat.cast_ofNat,
      Pi.top_apply, Prop.top_eq_true, false_or, or_false, true_or, or_true, true_and, and_true,
      false_and, and_false, exists_false, exists_prop, exists_eq_right, ite_self,
      Basalt.Walk.dite_const, Basalt.Walk.matchConst])
  let pruned ← timeIt "prune.simp" <| observing? <| Lean.Elab.Tactic.run g <| evalTactic tac
  return pruned.getD [g]

/-- The computed angelic precondition `g`, pruned (`prune`), then one goal per case of each `match`
in it on something in the context, each pruned again. A case split on the context picks no
disjunct. -/
partial def prunePaths (g : MVarId) : TermElabM (List MVarId) := do
  (← prune g).flatMapM fun g => do
    let some gs ← timeIt "prune.split" (splitCtxMatch? id g) | return [g]
    gs.flatMapM prunePaths

/-- Prove `goal`, which is `O.spec g post` for `O` the observation `obs` into `Prop`, by the walk of
a lower bound: the precondition it computed, turned into goals by `finish`, which is given the
context the walk began in, then whatever else the walk left, tidied. -/
def preconditionBound (finish : LocalContext → MVarId → TermElabM (List MVarId))
    (extras : Array Term) (obs : Name) (g post : Expr) (goal : MVarId) :
    TermElabM (List MVarId) := do
  let lctx := (← goal.getDecl).lctx
  let t0 ← IO.monoMsNow
  let (pre, structural, rest) ← computeBound extras obs true g post
  let t1 ← IO.monoMsNow
  let paths ← mkFreshExprMVar pre
  goal.assign (mkApp structural paths)
  let fin ← finish lctx paths.mvarId!
  let t2 ← IO.monoMsNow
  let rest' ← rest.mapM fun g => tidy lctx g
  let t3 ← IO.monoMsNow
  if basalt.walk.profile.get (← getOptions) then logInfo m!"walk timing: computeBound {t1 - t0} ms, finish {t2 - t1} ms ({fin.length} goals), tidy rest {t3 - t2} ms ({rest.length} goals); precondition size {(← instantiateMVars pre).approxDepth}"
  return fin ++ rest'

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
  let ariths ← splitBoundMatches (if lower then 3 else 2) (← tidy lctx arith.mvarId!)
  return ariths ++ (← rest.mapM fun g => tidy lctx g)

/-! ## The `walk` tactic -/

/-- A statement on an observation: `O.spec g post` for an observation into `Prop` (`bound` is
`none`), or a bound `b ≤ O.spec g post` (`bound` is `(b, true)`) or `O.spec g post ≤ b`. -/
structure SpecGoal extends SpecParts where
  /-- The observation's name: `O` is a constant applied to its parameters. -/
  obs : Name
  bound : Option (Expr × Bool)

/-- `ty` as a statement on an observation. -/
def specGoal? (ty : Expr) : Option SpecGoal :=
  let spec (e : Expr) (bound : Option (Expr × Bool)) : Option SpecGoal := do
    let s ← specParts? e
    return { s with obs := ← s.O.getAppFn.constName?, bound }
  spec ty none <|> if ty.isAppOfArity ``LE.le 4 then
      spec (ty.getArg! 3) (some (ty.getArg! 2, true)) <|>
        spec (ty.getArg! 2) (some (ty.getArg! 3, false))
    else none

/-- Whether the observation `O` is into an angelic algebra: its specification monad is `WP` or `WPC`
of `Mix.angelic`. -/
private def isAngelic (O : Expr) : MetaM Bool := do
  let ty ← whnfR (← inferType O)
  unless ty.isAppOf ``Obs && 2 ≤ ty.getAppNumArgs do return false
  let W := ty.getArg! 1
  return W.isApp && W.appArg!.getAppFn.isConstOf ``Mix.angelic

/-- The error for a goal `walk` does not take, with the rewrite that would restate it when its head
has one. -/
private def notASpec (ty : Expr) : MetaM MessageData := do
  let hint ← match ty.getAppFn.constName? with
    | some `IsSoundAndComplete =>
      pure m!"\nSplit the law into its halves first: `refine .intro ?sound ?complete`."
    | some L =>
      if (← getEnv).contains (L ++ `iff_obs) then
        pure m!"\nRestate it on its observation first: `rw [{.ofConstName (L ++ `iff_obs)}]`."
      else pure m!""
    | none => pure m!""
  return m!"walk: expected a statement on an observation, `O.spec (gen …) post`, \
    `b ≤ O.spec (gen …) post`, or `O.spec (gen …) post ≤ b`, or a relation registered by \
    `@[walk_rel]`, got{indentExpr ty}{hint}"

/-- `e` with its leading lambda binders renamed `ns`, in order. -/
private def nameLambdas : Expr → List Name → Expr
  | .lam _ d b bi, n :: ns => .lam n d (nameLambdas b ns) bi
  | e, _ => e

/-- `post`, a postcondition, as a lambda: one that is not is given binders, for the walk to name
the last value drawn after. -/
private def etaPost (post : Expr) : MetaM Expr := do
  if post.isLambda then return post
  return nameLambdas (← etaExpand post) [`v, `n_v]

/-- `goal`'s statement, reduced only as far as it takes to show a statement on an observation: to
`whnfR` a bare `O.spec g post` is the stuck projection `O.1 g post`. -/
def goalStatement (goal : MVarId) : MetaM Expr := do
  let ty ← Core.betaReduce (← instantiateMVars (← goal.getType)).consumeMData
  if (specGoal? ty).isSome then return ty
  Core.betaReduce (← whnfR ty)

/-- Walk `goal`, a statement on an observation or a relation (see `walk`). -/
partial def walkGoal (extras : Array Term) (goal : MVarId) : TermElabM (List MVarId) :=
  goal.withContext do
  let ty ← goalStatement goal
  if let some rel := ty.getAppFn.constName? then
    if (relJudgment? (← getEnv) rel).isSome then return ← walkRel "walk" rel extras goal
  let some sg := specGoal? ty | throwError (← notASpec ty)
  let goal ← goal.replaceTargetDefEq ty
  match sg.bound with
  | some (b, lower) => arithBound extras sg.obs lower sg.g sg.post b goal
  | none =>
    let post ← etaPost sg.post
    if ← isAngelic sg.O then preconditionBound (fun _ => prunePaths) extras sg.obs sg.g post goal
    else
      preconditionBound (fun lctx g => do
          let t0 ← IO.monoMsNow
          let gs ← splitPaths g
          let t1 ← IO.monoMsNow
          let gs ← gs.mapM (tidy lctx ·)
          let t2 ← IO.monoMsNow
          if basalt.walk.profile.get (← getOptions) then logInfo m!"walk timing: splitPaths {t1 - t0} ms ({gs.length} paths), tidy {t2 - t1} ms"
          return gs) extras sg.obs sg.g
        post goal

/-- The admissibility of `sg`'s statement, for fixpoint induction on its generator: `O.admissible`
for an observation into `Prop`, `O.admissible_le` for an upper bound. -/
private def specAdmissible (sg : SpecGoal) : MetaM Expr := do
  -- In an angelic algebra, a statement by itself is a lower bound too: some run reaches it.
  let lower ← match sg.bound with
    | some (_, lower) => pure lower
    | none => isAngelic sg.O
  if lower then
    throwError "walk fixpoint: a lower bound on `{.ofConstName sg.obs}` is false of the generator \
      that never returns, so fixpoint induction cannot prove it. Induct yourself \
      (`IsCompleteFor.of_measure`), or certify termination (`mass_fixpoint`), and then `walk`."
  let (lemName, args) := match sg.bound with
    | some (b, _) => (sg.obs ++ `admissible_le, #[sg.post, b])
    | none => (sg.obs ++ `admissible, #[sg.post])
  unless (← getEnv).contains lemName do
    throwError "walk fixpoint: no `{.ofConstName lemName}`: fixpoint induction needs the statement \
      admissible"
  mkAppM lemName args

/-- `walk fixpoint`: one step of `gen.fixpoint_induct` on `goal`, then `walkGoal`. -/
def walkFixpoint (extras : Array Term) (goal : MVarId) : TermElabM (List MVarId) :=
  goal.withContext do
  let ty ← goalStatement goal
  if let some rel := ty.getAppFn.constName? then
    if let some (.rel _ genRel) := relJudgment? (← getEnv) rel then
      return ← relFixpoint "walk fixpoint" "walk" rel genRel extras goal
  let some sg := specGoal? ty | throwError (← notASpec ty)
  let goal ← goal.replaceTargetDefEq ty
  -- A statement by itself is walked as a lower bound (`preconditionBound`).
  let j := .spec (sg.bound.any fun (_, lower) => !lower)
  walkGoal extras
    (← fixpointStep "walk fixpoint" "walk" j sg.obs sg.g (← specAdmissible sg) goal).1

/-- The error for a fact passed in the form a reader checks: `h : L …` when `L.obs` exists. -/
def checkFact (t : Term) : TermElabM Unit := do
  let some ty ← observing? do inferType (← elabFact t) | return
  let some L ← forallTelescope ty fun _ concl => return concl.getAppFn.constName? | return
  if (← getEnv).contains (L ++ `obs) then
    throwError "walk: the fact{indentD t}\nis stated as `{.ofConstName L}`; a walk takes facts \
      stated on an observation. Pass `{t}.obs`."

/-- Proves a statement about a generator by walking its syntax, leaving what only you can supply.

Restate the goal on its observation first (`rw [<Law>.iff_obs]`), then `walk [h₁.obs, …]`, passing
the callees' laws. What is left depends on the goal:

* `alwaysObs.spec (gen …) P` (soundness, cost): one goal per path, `P` of the value it built;
* `mayObs.spec (gen …) P` (completeness): one precondition, an `∃` per draw and an `∨` per choice,
  with the branches that cannot satisfy `P` pruned;
* `b ≤ O.spec (gen …) f` or `O.spec (gen …) f ≤ b` (mass, expectation): one inequality between `b`
  and the bound the walk computed;
* a relation registered by `@[walk_rel]` (`IsFaithful`'s fields): whatever relates the two sides.

A value drawn by `let x ← …` is `x✝` in what is left, with what is known of it as `h_x✝` (and its
cost as `n_x✝`); name them with `next x h_x =>`.

`walk fixpoint` first inducts over `gen`'s recursion, with `ih` for every recursive call. It proves
only what holds of a generator that never returns — soundness, cost, an upper bound on an
expectation, the relations — and refuses a lower bound. -/
syntax (name := walkTac) "walk" (&" fixpoint")? (walkFacts)? : tactic

elab_rules : tactic
  | `(tactic| walk $[fixpoint%$fix]? $[$fs]?) => withMainContext do
    let facts := walkFacts.terms fs
    -- this thread's entries only: other walks may be running
    let tid ← (IO.getTID : BaseIO UInt64)
    (← factConstsCache).modify fun m => m.filter fun k _ => k.1 != tid
    for t in facts do checkFact t
    let goal ← getMainGoal
    replaceMainGoal (← if fix.isSome then walkFixpoint facts goal else walkGoal facts goal)

end Basalt.Walk
