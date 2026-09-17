/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt.SPMF.Walk.Attr
import Lean.Elab.Tactic.Basic
import Lean.Elab.SyntheticMVars
import Lean.Meta.Eqns
import Lean.Meta.Transform
import Lean.Meta.Tactic.Replace
import Lean.Meta.Tactic.Assumption

/-!
# The Generator Walker

Proves a judgment about a generator by structural recursion on its syntax: a `@[gen_rule]` per
combinator, facts at the leaves. What no rule or fact covers is handed back as a residual goal.
-/

open Lean Meta Elab Tactic

namespace Basalt.Walk

/-- `apply` that matches `e`'s conclusion against the goal without unfolding it. A judgment may be a
definition whose body is a `∀`, and `MVarId.apply` then tries the unfolded arities first. Returns
the unassigned explicit premises. -/
def applyExact (goal : MVarId) (e : Expr) : MetaM (List MVarId) := goal.withContext do
  goal.checkNotAssigned `applyExact
  let target ← goal.getType
  let (xs, bis, concl) ← forallMetaTelescope (← inferType e)
  unless ← isDefEq concl target do
    throwError "could not unify the conclusion of{indentExpr e}\n{indentExpr concl}\n\
      with the goal{indentExpr target}"
  for x in xs, bi in bis do
    if bi.isInstImplicit && !(← x.mvarId!.isAssigned) then
      x.mvarId!.assign (← synthInstance (← inferType x))
  goal.assign (mkAppN e xs)
  xs.toList.zip bis.toList |>.filterMapM fun (x, bi) => do
    if bi.isExplicit && !(← x.mvarId!.isAssigned) then return some x.mvarId! else return none

/-- A value of type `ty`: its constructor applied to fresh field metavariables when `ty` has exactly
one constructor and no indices, so that a projection out of it reduces; a bare metavariable
otherwise. -/
private partial def mkCtorMVar (ty : Expr) : MetaM Expr := do
  let ty ← whnfR ty
  let some (.inductInfo iv) := ty.getAppFn.constName?.bind (← getEnv).find? | mkFreshExprMVar ty
  let [ctor] := iv.ctors | mkFreshExprMVar ty
  if iv.numIndices != 0 || iv.isRec then return ← mkFreshExprMVar ty
  let ctor ← getConstInfoCtor ctor
  let mut e := mkAppN (mkConst ctor.name ty.getAppFn.constLevels!) (ty.getAppArgs.extract 0 ctor.numParams)
  for _ in [:ctor.numFields] do
    let .forallE _ d _ _ ← whnfR (← inferType e) | throwError "walk: ill-typed constructor"
    e := e.app (← mkCtorMVar d)
  return e

/-- `e` with every projection out of a constructor application reduced (`(a, b).1` to `a`), and
nothing else unfolded. -/
def reduceCtorProjs (e : Expr) : MetaM Expr := do
  Meta.transform (← Core.betaReduce (← instantiateMVars e)) (post := fun x => do
    let some f := x.getAppFn.constName? | return .continue
    let some info ← getProjectionFnInfo? f | return .continue
    unless x.getAppNumArgs > info.numParams do return .continue
    let r ← whnfR x
    return if r.isProj then .continue else .done r)

/-- `e` with its leading binders instantiated, by `mkCtorMVar` when `ctor`, and its type ascribed
with the resulting projections reduced. A family criterion hands over a recursive bound
`∀ j, c ≤ (g j).mass` over a tupled (or `Unit`) seed, and `apply` alone cannot match `g j.1 j.2`
against `g lo (x - 1)`, nor invent the `()`; left unreduced, `(?a, ?b).1 =?= p.1` is solved by
structure eta, which fixes `?b := p.2` and fails on the second argument. A callee's law with
arguments (`<gen>.terminates : ∀ m, …`) is instantiated the same way. A binder whose constructor has
a proof field, as a subtype does, is matched only through its value (`k.1`), which leaves the proof
field unassigned; `ctor := false` is the retry for it. -/
private def instBinders (ctor : Bool) (e : Expr) : MetaM Expr := do
  let mut e := e
  repeat
    let .forallE _ d _ _ ← instantiateMVars (← inferType e) | break
    e := e.app (← if ctor then mkCtorMVar d else mkFreshExprMVar d)
  mkExpectedTypeHint e (← reduceCtorProjs (← inferType e))

/-- Assign every unassigned `Prop`-typed metavariable of `e` from a hypothesis, as a premise the
fact's use does not determine (an `if`'s branch condition) must be. -/
private def assumeProps (e : Expr) : MetaM Unit := do
  for m in (← getMVars e) do
    unless ← m.isAssigned do
      if ← isProp (← m.getType) then m.assumption

/-- `b` applied to `e` as its first explicit argument, with fresh metavariables before it. -/
private def applyBridge (b : Name) (e : Expr) : MetaM Expr := do
  let mut f ← mkConstWithFreshMVarLevels b
  repeat
    let .forallE _ d _ bi ← instantiateMVars (← inferType f)
      | throwError "walk: bridge `{b}` takes no explicit argument"
    if bi.isExplicit then
      unless ← isDefEq d (← inferType e) do failure
      return f.app e
    f := f.app (← mkFreshExprMVar d)
  failure

/-- The head constant of the type of `b`'s first explicit argument. -/
private def bridgeArgHead (b : Name) : MetaM (Option Name) := do
  forallTelescope (← getConstInfo b).type fun xs _ => do
    for x in xs do
      if (← x.fvarId!.getBinderInfo).isExplicit then
        return (← whnfR (← inferType x)).getAppFn.constName?
    return none

/-- Close `goal`, a leaf of judgment `j`, with the fact `e` through one of `j`'s bridges, `e`'s
binders possibly instantiated by `instBinders` first. Returns the bridge's premises, not yet
walked; `none` if `e` does not apply. -/
private def tryFact (j : Judgment) (goal : MVarId) (e : Expr) : MetaM (Option (List MVarId)) := do
  for inst in [none, some true, some false] do
    let e ← match inst with
      | none => pure (some e)
      | some ctor => observing? (instBinders ctor e)
    let some e := e | continue
    let head := (← whnfR (← inferType e)).getAppFn.constName?
    -- A bridge stated for the fact's own head is tried before one that must unfold the fact, which
    -- can succeed too, by unification against the unfolded judgment, but with a mangled result.
    let goalHead := (← whnfR (← goal.getType)).getAppFn.constName?
    let exact ← j.bridges.filterM fun b => return head == (← b.elim (pure goalHead) bridgeArgHead)
    for bridge in exact ++ j.bridges.filter (!exact.contains ·) do
      let r ← observing? do
        let cand ← match bridge with
          | none => pure e
          | some b => applyBridge b e
        let gs ← applyExact goal cand
        if bridge.isNone && !gs.isEmpty then failure
        goal.withContext (assumeProps e)
        if (← instantiateMVars e).hasExprMVar then failure
        return gs
      if let some gs := r then return some gs
  return none

/-- `head`'s law for judgment `j`, under the `<head>.<lawSuffix>` naming convention. -/
def law? (j : Judgment) (g : Expr) : MetaM (Option Expr) := do
  let some head := g.getAppFn.constName? | return none
  unless (← getEnv).contains (head ++ j.lawSuffix) do return none
  return some (← mkConstWithFreshMVarLevels (head ++ j.lawSuffix))

/-! ## Naming what a rule introduces

A rule's premises bind the values and costs the generator draws, under the rule's own binder names;
the generator's names for them survive only as binder names of its lambdas, and are lost once the
premise's metavariables are instantiated. They are recovered before the premise is walked: a
drawn value takes the name of the continuation it is passed to (`hint`), or else that of the goal's
postcondition (`post`); a cost is `n_<value>` and a hypothesis about the value `h_<value>`. -/

/-- The names of the lambda arguments of `g`'s head that bind something other than `Unit`: a
continuation's `delta`, a `dite` branch's `h`. -/
private def lambdaHints (g : Expr) : Array Name :=
  g.getAppArgs.filterMap fun
    | .lam n d _ _ => if d.isConstOf ``Unit || d.isConstOf ``PUnit || d.isAppOf ``PUnit then none
        else some n.eraseMacroScopes
    | _ => none

/-- The first two binder names of the goal's postcondition: its first argument that is a lambda of
two binders. -/
private def postNames (ty : Expr) : Option (Name × Name) :=
  ty.getAppArgs.findSome? fun
    | .lam v _ (.lam n _ _ _) _ => some (v.eraseMacroScopes, n.eraseMacroScopes)
    | _ => none

private def prefixed (p : String) (v : Name) : Name := .mkSimple (p ++ v.toString)

/-- `t`, a rule premise, with its binders named as the section docstring says. -/
private def nameBinders (t : Expr) (hint : Option Name) (post : Option (Name × Name)) :
    MetaM Expr := do
  let value? := hint <|> post.map (·.1)
  let cost? := if hint.isSome then value?.map (prefixed "n_") else post.map (·.2)
  let rec go (t : Expr) (fvars : Array Expr) (v : Option Name) (k : Nat) (hintUsed : Bool) :
      MetaM Expr := do
    match t with
    | .forallE n d b bi =>
      let d := d.instantiateRev fvars
      let (n', v', k', used) ← do
        if ← isProp d then
          match v, hint, hintUsed with
          | some v, _, _ => pure (prefixed "h_" v, some v, k, hintUsed)
          | none, some h, false => pure (h, none, k, true)
          | _, _, _ => pure (if n.hasMacroScopes then `h else n, v, k, hintUsed)
        else if k == 0 then
          let v := value?.getD n
          pure (v, some v, 1, true)
        else if k == 1 then pure ((cost?.getD n), v, 2, hintUsed)
        else pure (n, v, k + 1, hintUsed)
      withLocalDecl n' bi d fun x => do
        mkForallFVars #[x] (← go b (fvars.push x) v' k' used)
    | _ =>
      let t := t.instantiateRev fvars
      unless fvars.isEmpty do return t
      -- A premise that binds nothing may still hand a postcondition on: name its binders.
      let (some v, some c) := (value?, cost?) | return t
      let args := t.getAppArgs
      let some i := args.findIdx? (· matches .lam _ _ (.lam ..) _) | return t
      let .lam _ d₁ (.lam _ d₂ b bi₂) bi₁ := args[i]! | return t
      return mkAppN t.getAppFn (args.set! i (.lam v d₁ (.lam c d₂ b bi₂) bi₁))
  go t #[] none 0 false

/-- Whether premise `t` binds a drawn value: a `∀` over data, or a postcondition to hand on. -/
private def bindsValue (t : Expr) : MetaM Bool := do
  match t with
  | .forallE _ d _ _ => return !(← isProp d)
  | _ => return (postNames t).isSome

/-- `premises` renamed by `nameBinders`. The hints go one per premise when there are as many, and
otherwise, in order, to the premises that bind a value, when there are as many of those. -/
private def namePremises (g? : Option Expr) (goalTy : Expr) (premises : List MVarId) :
    MetaM (List MVarId) := do
  let hints := (g?.map lambdaHints).getD #[]
  let post := postNames goalTy
  let types ← premises.mapM fun p => do instantiateMVars (← p.getType)
  let hints ← if hints.size == premises.length then pure (hints.toList.map some) else do
    let binds ← types.mapM bindsValue
    if (binds.filter id).length != hints.size then pure (types.map fun _ => none) else
      let (out, _) := binds.foldl (fun (out, rest) b =>
        if b then (out ++ [rest.head?], rest.drop 1) else (out ++ [none], rest))
        (([] : List (Option Name)), hints.toList)
      pure out
  (premises.zip (types.zip hints)).mapM fun (p, t, hint) => do
    p.replaceTargetDefEq (← nameBinders t hint post)

mutual

/-- Prove `goal` by walking the generator it is about, returning the residual goals: those no
judgment recognizes. `extras` are the facts the caller passed; they stay syntax because one may be
used at several sub-generators, and elaborating once would freeze its metavariables at the first. -/
partial def walk (extras : Array Term) (goal : MVarId) : TermElabM (List MVarId) :=
  goal.withContext do
  let ty ← whnfR (← instantiateMVars (← goal.getType))
  -- A rule's premise may be a `∀` (a bind's continuation, an `ite`'s branch condition).
  if let .forallE n _ _ _ := ty then
    let (_, goal) ← goal.intro ((← getLCtx).getUnusedName n.eraseMacroScopes)
    return ← walk extras goal
  for j in judgments do
    if let some (g, restate) ← j.subject? ty then
      return ← bound j extras goal restate g
  -- The branch premises of a list combinator, built one branch at a time: any `nil`/`cons`
  -- relation whose last argument is the combinator's branch list.
  if let some head := ty.getAppFn.constName? then
    if (← getEnv).contains (head ++ `cons) && (← getEnv).contains (head ++ `nil) then
      let ctor := if (← whnfR ty.appArg!).isAppOfArity ``List.nil 1 then `nil else `cons
      return ← walkAll extras
        (← applyExact goal (← mkConstWithFreshMVarLevels (head ++ ctor)))
  return [← goal.replaceTargetDefEq (← instantiateMVars (← goal.getType)).headBeta]

/-- `walk` each goal in turn. -/
partial def walkAll (extras : Array Term) (goals : List MVarId) : TermElabM (List MVarId) :=
  goals.flatMapM (walk extras)

/-- The case of `walk` for a goal of judgment `j` about `g`: a rule for `g`'s combinator, or `g` is
a leaf. -/
partial def bound (j : Judgment) (extras : Array Term) (goal : MVarId) (restate : Expr → Expr)
    (g : Expr) : TermElabM (List MVarId) := goal.withContext do
  -- The reductions cover a branch that is still a redex or a projection (`(fun () => …) ()`,
  -- `p.2 ()`); no combinator is reducible, so no reduction can turn one combinator into another.
  -- The goal is restated in the reduced form before the rule is applied: matching a rule against
  -- an unreduced branch closes a side condition like `xs ≠ []` by proof irrelevance rather than by
  -- unification, and the side condition then survives as a goal.
  let rules : TermElabM (Option (List MVarId)) := do
    for g' in [g, ← whnfCore g, ← whnfR g] do
      let some lems := g'.getAppFn.constName?.bind (rulesFor (← getEnv) j.key) | continue
      let goal ← if g' == g then pure goal else goal.change (restate g')
      -- A later rule is a fallback: it runs only when every earlier one failed, and the first
      -- rule's failure is the one reported.
      let saved ← saveState
      let mut firstErr : Option Exception := none
      for lem in lems do
        try
          let premises ← applyExact goal (← mkConstWithFreshMVarLevels lem)
          return some (← walkAll extras (← namePremises (some g') (← goal.getType) premises))
        catch ex =>
          firstErr := firstErr <|> some ex
          saved.restore
      if let some ex := firstErr then throw ex
    return none
  -- A leaf: a caller-supplied fact, a hypothesis (a recursive occurrence), or a proved law. The
  -- fact is committed to before its bridge's premises are walked, so that a failure inside them is
  -- reported where it happens.
  let leaf : TermElabM (Option (List MVarId)) := do
    for t in extras do
      let r ← observing? do
        let e ← Term.withoutErrToSorry do
          let e ← Term.elabTerm t none
          Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
          instantiateMVars e
        let some gs ← tryFact j goal e | failure
        namePremises none (← goal.getType) gs
      if let some gs := r then return some (← walkAll extras gs)
    -- A hypothesis is tried only if it mentions `g`'s head: unifying one about another generator
    -- unfolds both, and on a generator over a long literal list that exceeds the recursion depth.
    let mentionsHead : Expr → Bool := match (← whnfCore g).getAppFn with
      | .const n _ => fun e => (e.find? (·.isConstOf n)).isSome
      | .fvar x => (·.containsFVar x)
      | _ => fun _ => true
    for decl in ← getLCtx do
      unless decl.isImplementationDetail do
        unless ← isProp decl.type do continue
        unless mentionsHead (← instantiateMVars decl.type) do continue
        if let some gs ← tryFact j goal decl.toExpr then
          return some (← walkAll extras (← namePremises none (← goal.getType) gs))
    if let some law ← law? j g then
      if let some gs ← tryFact j goal law then
        return some (← walkAll extras (← namePremises none (← goal.getType) gs))
    return none
  for step in if j.leavesFirst then [leaf, rules] else [rules, leaf] do
    if let some gs ← step then return gs
  throwError j.noLeaf g

end

/-! ## Reading a recursive definition -/

/-- The explicit-or-not argument positions of `gen` that some recursive call in one of its equations
changes, or that an equation of a recursive `gen` matches on: those are the seed. -/
def seedPositions (gen : Name) : MetaM (Array Nat) := do
  let some eqns ← getEqnsFor? gen
    | throwError "walk: `{gen}` has no equation lemmas to unfold"
  let varying ← IO.mkRef (∅ : Std.HashSet Nat)
  let matched ← IO.mkRef (∅ : Std.HashSet Nat)
  let recursive ← IO.mkRef false
  for eqn in eqns do
    forallTelescope (← getConstInfo eqn).type fun _ body => do
      let some (_, lhs, rhs) := body.eq? | return
      let params := lhs.getAppArgs
      for h : k in [:params.size] do
        unless params[k].isFVar do matched.modify (·.insert k)
      forEachExpr rhs fun e => do
        if e.isAppOf gen && e.getAppNumArgs == params.size then
          recursive.set true
          for h : k in [:params.size] do
            if e.getArg! k != params[k] then varying.modify (·.insert k)
  -- A pattern-matched argument is a seed only when there is a recursion for it to vary in.
  let v ← if ← recursive.get then pure ((← varying.get).union (← matched.get)) else pure ∅
  return (Array.range (← getConstInfo gen).type.getForallArity).filter v.contains

/-- The user-facing name of `gen`'s `k`th binder. -/
def binderName (gen : Name) (k : Nat) : MetaM Name :=
  do forallTelescope (← getConstInfo gen).type fun xs _ => do
    let n ← xs[k]!.fvarId!.getUserName
    return n.eraseMacroScopes

end Basalt.Walk
