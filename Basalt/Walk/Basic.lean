/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Lean.Elab.SyntheticMVars
import Lean.Elab.Tactic.Basic
import Lean.Elab.Tactic.NormCast
import Lean.Meta.CtorRecognizer
import Lean.Meta.Match.MatcherApp.Basic
import Lean.Meta.RecExt
import Lean.Meta.Tactic.AC.Main
import Lean.Meta.Tactic.Assumption
import Lean.Meta.Tactic.NormCast
import Lean.Meta.Tactic.Replace
import Lean.Meta.Transform
import Batteries.Data.List.Basic
import Basalt.Walk.Attr
import Basalt.Walk.Names

/-!
# The Generator Walker

Proves a judgment about a generator by structural recursion on its syntax.
-/

open Lean Meta Elab Tactic

namespace Basalt.Walk

/-! ## Branch relations

The relations a rule collects a list combinator's branches with: `List.Forall₂` for an unweighted
list, `Mix.Weighted` (`Basalt/Obs/Ordered.lean`) for a weighted one. -/

attribute [gen_branches] List.Forall₂

/-- The proofs among the arguments of the applications in `e`, outside binders. -/
private partial def proofArgs (e : Expr) (acc : Array Expr := #[]) : MetaM (Array Expr) := do
  unless e.isApp do return acc
  let mut acc ← proofArgs e.getAppFn acc
  for a in e.getAppArgs do
    unless a.hasLooseBVars do
      if ← (try isProof a catch _ => pure false) then acc := acc.push a
      else acc ← proofArgs a acc
  return acc

/-- Assign each unassigned proof among `xs` from a proof of the same proposition occurring in `src`.
Unification equates two proofs by proof irrelevance without assigning a metavariable that stands for
one, so a side condition a statement takes implicitly (`h : lo ≤ hi`) would otherwise stay open,
silently. -/
def assignProofsFrom (xs : Array Expr) (src : Expr) : MetaM Unit := do
  let open_ ← xs.filterM fun x => do
    return !(← x.mvarId!.isAssigned) && (← isProp (← inferType x))
  if open_.isEmpty then return
  let cands ← proofArgs (← instantiateMVars src)
  for x in open_ do
    for c in cands do
      if ← isDefEq (← inferType x) (← inferType c) then
        x.mvarId!.assign c
        break

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
  assignProofsFrom ((xs.zip bis).filterMap fun (x, bi) => if bi.isExplicit then none else some x)
    target
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

/-- `e` with what is already determined computed: an `if` whose condition is closed and decides is
its branch (a continuation's bound instantiated at `true`), and a closed number read off a rational
is its value (`(1 / 2 : ℚ).den`, a literal coin's weight). Both are definitional. -/
def evalClosed (e : Expr) : MetaM Expr := do
  let closed (x : Expr) := !x.hasFVar && !x.hasMVar && !x.hasLooseBVars
  Meta.transform (← instantiateMVars e) (pre := fun x => do
    if x.isAppOfArity ``ite 5 && closed (x.getArg! 1) then
      let inst ← whnf (x.getArg! 2)
      if inst.isAppOf ``Decidable.isTrue then return .visit (x.getArg! 3)
      if inst.isAppOf ``Decidable.isFalse then return .visit (x.getArg! 4)
    if closed x && x.isApp && (x.find? fun e => e.isConstOf `Rat.num || e.isConstOf `Rat.den).isSome
    then
      -- `Rat`'s operations are irreducible, which the kernel's `rfl` does not see.
      let ty ← inferType x
      if ty.isConstOf ``Nat then
        if let some n := (← withTransparency .all (whnf x)).rawNatLit? then
          return .done (mkNatLit n)
      if ty.isConstOf ``Int then
        let v ← withTransparency .all (whnf x)
        if v.isAppOfArity ``Int.ofNat 1 then
          if let some n := (← withTransparency .all (whnf v.appArg!)).rawNatLit? then
            return .done (toExpr (Int.ofNat n))
    return .continue)

/-- What a walk leaves, tidied: projections out of constructors reduced, then `evalClosed`. -/
def tidyExpr (e : Expr) : MetaM Expr := do evalClosed (← reduceCtorProjs e)

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

/-! ## Postconditions up to a constant -/

/-- `e` with every application of a recursive function to a constructor unfolded
(`(node l x r).size` to `l.size + r.size + 1`), which is a definitional unfolding. -/
def unfoldCtorApps (e : Expr) : MetaM Expr := do
  Meta.transform (← instantiateMVars e) (post := fun x => do
    let .const c _ := x.getAppFn | return .continue
    unless ← isRecursiveDefinition c do return .continue
    let onCtor ← x.getAppArgs.anyM fun a => do isConstructorApp (← whnfR a)
    unless onCtor do return .continue
    let some x' ← unfoldDefinition? x | return .continue
    let x' ← whnfCore x'
    if x'.getAppFn.isConst && (← isMatcherApp x') then return .continue
    return .visit x')

/-- The summands of `e`. -/
private partial def summands (e : Expr) : Array Expr :=
  if e.isAppOfArity ``HAdd.hAdd 6 then summands e.appFn!.appArg! ++ summands e.appArg! else #[e]

/-- Solve a side goal of an affine bridge: `∀ a…, lhs = ?h a…`, by assigning `?h`, or
`∀ a…, lhs = ?k + t`, by finding `t` among the summands of `lhs` (casts pushed, constructors
unfolded) and assigning the rest to `?k`. -/
def solveAffine (goal : MVarId) : MetaM Unit := do
  let (_, goal) ← goal.intros
  goal.withContext do
  let some (_, lhs, rhs) := (← instantiateMVars (← goal.getType)).eq?
    | throwError "walk: expected an equation between postconditions"
  let lhs ← unfoldCtorApps (← reduceCtorProjs lhs)
  let mut thms ← NormCast.pushCastExt.getTheorems
  for n in [`add_zero, `zero_add, ``ite_self] do
    if (← getEnv).contains n then thms ← thms.addConst n
  let ctx ← Simp.mkContext (simpTheorems := #[thms]) (congrTheorems := ← getSimpCongrTheorems)
  let (r, _) ← simp lhs ctx
  -- `ite_self` matters here: a conditional on the drawn value with one bound in both branches.
  let affine := rhs.isAppOfArity ``HAdd.hAdd 6 && rhs.appFn!.appArg!.getAppFn.isMVar
  unless affine do
    unless ← isDefEq rhs r.expr do
      throwError "the postcondition{indentExpr r.expr}\nis not{indentExpr rhs}"
    goal.assign (← mkExpectedTypeHint (← r.getProof) (← goal.getType))
    return
  let k := rhs.appFn!.appArg!
  let t := rhs.appArg!
  let parts := summands r.expr
  let some i ← parts.findIdxM? (isDefEq · t)
    | throwError "the postcondition{indentExpr r.expr}\nis not the fact's{indentExpr t}\nplus a \
        constant"
  let rest := parts.eraseIdx! i
  let kVal ← if h : 0 < rest.size then
      rest[1:].foldlM (fun acc x => mkAppM ``HAdd.hAdd #[acc, x]) rest[0]
    else mkNumeral (← inferType t) 0
  unless ← isDefEq k kVal do
    throwError "the constant{indentExpr kVal}\ndepends on the value drawn"
  let ac ← mkFreshExprMVar (← mkEq r.expr (← mkAppM ``HAdd.hAdd #[kVal, t]))
  if rest.isEmpty then
    let some zeroAdd := (← getEnv).find? `zero_add | throwError "walk: `zero_add` is not in scope"
    let pf ← mkAppM zeroAdd.name #[t]
    ac.mvarId!.assign (← mkEqSymm pf)
  else
    AC.rewriteUnnormalizedRefl ac.mvarId!
  goal.assign (← mkExpectedTypeHint (← mkEqTrans (← r.getProof) ac) (← goal.getType))

/-- Solve `b = ↑?k`, for a bound `b` computed in a type that natural numbers embed in, by moving
its casts to the root. -/
def solveCast (goal : MVarId) : MetaM Unit := goal.withContext do
  let some (_, lhs, rhs) := (← instantiateMVars (← goal.getType)).eq?
    | throwError "walk: expected an equation"
  let lhs ← reduceCtorProjs (← unfoldCtorApps (← reduceCtorProjs lhs))
  let r ← Lean.Elab.Tactic.NormCast.derive lhs
  if r.expr.isAppOfArity ``Nat.cast 3 then
    unless ← isDefEq rhs r.expr do throwError "walk: could not read off the bound{indentExpr r.expr}"
    goal.assign (← mkExpectedTypeHint (← r.getProof) (← goal.getType))
    return
  -- A bound that is a numeral: `norm_cast` prefers it to the cast of one.
  let some n := r.expr.nat? | throwError "the bound{indentExpr r.expr}\nis not the cast of a \
    natural number"
  unless ← isDefEq rhs.appArg! (mkNatLit n) do throwError "walk: could not read off the bound {n}"
  let num ← mkFreshExprMVar (← mkEq r.expr (← instantiateMVars rhs))
  let mut thms : SimpTheorems := {}
  for c in [``eq_self, `Nat.cast_ofNat, `Nat.cast_one, `Nat.cast_zero] do
    if (← getEnv).contains c then thms ← thms.addConst c
  let ctx ← Simp.mkContext (simpTheorems := #[thms]) (congrTheorems := ← getSimpCongrTheorems)
  let (res, _) ← simpTarget num.mvarId! ctx
  if res.isSome then throwError "walk: could not prove that {n} is its own cast"
  goal.assign (← mkExpectedTypeHint (← mkEqTrans (← r.getProof) num) (← goal.getType))

/-- Close `goal`, a leaf of judgment `j`, with the fact `e` through one of `j`'s bridges or one of
the observation's `leaves`, `e`'s binders possibly instantiated by `instBinders` first. Returns the
bridge's premises, not yet walked; `none` if `e` does not apply. -/
private def tryFact (j : Judgment) (leaves : Leaves) (goal : MVarId) (e : Expr) :
    MetaM (Option (List MVarId)) := do
  for inst in [none, some true, some false] do
    let e ← match inst with
      | none => pure (some e)
      | some ctor => observing? (instBinders ctor e)
    let some e := e | continue
    let head := (← whnfR (← inferType e)).getAppFn.constName?
    -- A bridge stated for the fact's own head is tried before one that must unfold the fact, which
    -- can succeed too, by unification against the unfolded judgment, but with a mangled result.
    let goalHead := (← whnfR (← goal.getType)).getAppFn.constName?
    -- A bridge not in scope cannot apply: a stronger law is stated after the rules that use it.
    let env ← getEnv
    let bridges := j.bridges.filter fun b => b.all env.contains
    let exact ← bridges.filterM fun b => return head == (← b.elim (pure goalHead) bridgeArgHead)
    for bridge in exact ++ bridges.filter (!exact.contains ·) do
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
    for bridge in leaves.facts do
      let saved ← saveState
      let some sides ← observing? (do
        let cand ← applyBridge bridge e
        applyExact goal (← mkExpectedTypeHint cand
          (nameBound (← instantiateMVars (← inferType cand))
            (postNames (← instantiateMVars (← goal.getType)))))) | continue
      try
        sides.forM solveAffine
        goal.withContext (assumeProps e)
        if (← instantiateMVars e).hasExprMVar then failure
        return some []
      catch ex =>
        saved.restore
        if leaves.facts.back? == some bridge && inst == some false then throw ex
  return none

/-- `g`'s head's laws for judgment `j`, under the naming convention (`Judgment.lawSuffixes`). -/
def law? (j : Judgment) (g : Expr) : MetaM (Array Expr) := do
  let some head := g.getAppFn.constName? | return #[]
  let env ← getEnv
  (j.lawSuffixes.filterMap fun suffix =>
    if env.contains (head ++ suffix) then some (head ++ suffix) else none).mapM
    mkConstWithFreshMVarLevels

/-! ## Reading a recursive definition -/

/-- `gen.fixpoint_induct`, and the positions of `gen`'s arguments it abstracts: those some recursive
call changes, as `partial_fixpoint` decided. `none` when `gen` is not a `partial_fixpoint`. -/
def fixpointSeed? (gen : Name) : MetaM (Option (Name × Array Nat)) := do
  let ind := gen ++ `fixpoint_induct
  unless (← getEnv).contains ind do
    unless isReservedName (← getEnv) ind do return none
    executeReservedNameAction ind
  let (_, _, concl) ← forallMetaTelescope (← inferType (← mkConstWithFreshMVarLevels ind))
  let F := concl.appArg!
  return some (ind, ← forallTelescope (← whnf (← inferType F)) fun ys _ => do
    let body := (mkAppN F ys).headBeta
    ys.mapM fun y => do
      let some k := body.getAppArgs.findIdx? (· == y)
        | throwError "`{gen}`'s fixpoint abstracts something other than an argument"
      return k)

/-! ## Unfolding a definition -/

/-- `g` with its head unfolded one step, when the head is a non-recursive definition with no rule:
a derived combinator or a helper, which is walked through rather than taught to the walker. A
combinator with a rule (unless `combinators`), a recursive definition, a matcher, a projection, and
an instance are not unfolded. Returns the head's name with the body. -/
def unfold? (g : Expr) (combinators := false) : MetaM (Option (Name × Expr)) := do
  let .const c us := g.getAppFn | return none
  let env ← getEnv
  if (!combinators && isCombinator env c) || isMatcherCore env c || env.isProjectionFn c then
    return none
  if ← isInstance c then return none
  let some (.defnInfo info) := env.find? c | return none
  if ← isRecursiveDefinition c then return none
  if (← observing? (fixpointSeed? c)).join.isSome then return none
  let v ← instantiateValueLevelParams (.defnInfo info) us
  return some (c, (renameLambdas v).beta g.getAppArgs)

/-- Rewrite `e`, a specification applied to a postcondition, with the `@[spec_apply]` lemma for its
head, by unification rather than by `simp`: a side condition's proof may have the type the shape
asks for only up to unfolding (`xs ≠ []` for a defined `xs`), which `simp` does not see through. -/
private def applySpecLemma (e : Expr) : MetaM (Option (Expr × Expr)) := do
  let some head := e.appFn!.getAppFn.constName? | return none
  for origin in (← specApplyExt.getTheorems).lemmaNames do
    let .decl n .. := origin | continue
    let lem ← mkConstWithFreshMVarLevels n
    let (xs, _, ty) ← forallMetaTelescope (← inferType lem)
    let some (_, lhs, rhs) := ty.eq? | continue
    unless lhs.isApp && lhs.appFn!.getAppFn.isConstOf head do continue
    if ← isDefEq lhs e then
      assignProofsFrom xs e
      return some (← instantiateMVars rhs, ← instantiateMVars (mkAppN lem xs))
  return none

/-- Turn `goal`, about a combinator with the `@[gen_map]` lemma `mapLem`, into a goal about that
lemma's right-hand side applied to the postcondition, rewritten into the algebra's shapes. -/
def applyMap (adapter mapLem : Name) (goal : MVarId) : MetaM (List MVarId) := goal.withContext do
  let names := postNames (← instantiateMVars (← goal.getType))
  let ad ← mkConstWithFreshMVarLevels adapter
  let (xs, bis, concl) ← forallMetaTelescope (← inferType ad)
  unless ← isDefEq concl (← goal.getType) do
    throwError "walk: `{adapter}` does not conclude{indentExpr (← goal.getType)}"
  let #[hEq, hw] := (xs.zip bis).filterMap fun (x, bi) => if bi.isExplicit then some x else none
    | throwError "walk: `{adapter}` must take an equation and a goal"
  let lem ← mkConstWithFreshMVarLevels mapLem
  let (ys, ybis, eqn) ← forallMetaTelescope (← inferType lem)
  unless ← isDefEq eqn (← inferType hEq) do
    throwError "walk: `{mapLem}` does not apply to{indentExpr (← inferType hEq)}"
  for x in xs ++ ys, bi in bis ++ ybis do
    if bi.isInstImplicit && !(← x.mvarId!.isAssigned) then
      x.mvarId!.assign (← synthInstance (← inferType x))
  assignProofsFrom ys (← goal.getType)
  hEq.mvarId!.assign (mkAppN lem ys)
  goal.assign (mkAppN ad xs)
  let ty ← instantiateMVars (← hw.mvarId!.getType)
  -- With the shapes, what makes a postcondition visibly constant: a draw under which every path
  -- has one bound gets that bound.
  let mut thms ← specApplyExt.getTheorems
  for c in [``Nat.add_zero, ``ite_self, `mul_one, `one_mul, `one_pow] do
    if (← getEnv).contains c then thms ← thms.addConst c
  let ctx ← Simp.mkContext (simpTheorems := #[thms]) (congrTheorems := ← getSimpCongrTheorems)
  -- The side that is not the bound being computed.
  let side := if (ty.getArg! 2).getAppFn.isMVar then 3 else 2
  let some (shape, hShape) ← applySpecLemma (ty.getArg! side)
    | throwError "walk: no `@[spec_apply]` lemma for the right-hand side of `{mapLem}`:\
        {indentExpr (ty.getArg! side)}"
  let (r, _) ← simp shape ctx
  unless mixShapes.any r.expr.isAppOf do
    throwError "walk: the right-hand side of `{mapLem}` is no shape of choice:{indentExpr r.expr}"
  let restate (z : Expr) := mkAppN ty.getAppFn (ty.getAppArgs.set! side z)
  let motive ← withLocalDeclD `z (← inferType (ty.getArg! side)) fun z => do
    mkLambdaFVars #[z] (restate z)
  let hw' ← hw.mvarId!.replaceTargetEq (restate r.expr)
    (← mkCongrArg motive (← mkEqTrans hShape (← r.getProof)))
  -- The shape's rule names the bound it computes after the value this draw binds.
  if let some (v, _) := names then hw'.setTag (drawTag ++ v)
  let sides ← (ys.zip ybis).filterMapM fun (y, bi) => do
    if bi.isExplicit && !(← y.mvarId!.isAssigned) then return some y.mvarId! else return none
  return hw' :: sides.toList

/-- The first of `cands` that proves `goal`: each is applied, then what it left is finished, and
the state is restored after a failure. A later candidate is a fallback, tried only when every earlier
one failed. When all fail, the error reported is that of the first one that applied, which was
stated for this goal and failed further down, over that of one that never unified. `none` when there
is no candidate. -/
private def firstApplying (cands : Array α) (apply : α → TermElabM β)
    (finish : β → TermElabM γ) : TermElabM (Option γ) := do
  let saved ← saveState
  let mut firstErr : Option Exception := none
  let mut appliedErr : Option Exception := none
  for c in cands do
    let applied ← try Except.ok <$> apply c catch ex => pure (Except.error ex)
    match applied with
    | .error ex =>
      firstErr := firstErr <|> some ex
      saved.restore
    | .ok b =>
      try return some (← finish b)
      catch ex =>
        appliedErr := appliedErr <|> some ex
        saved.restore
  if let some ex := appliedErr <|> firstErr then throw ex
  return none

mutual

/-- Prove `goal` by walking the generator, returning the goals no judgment recognizes. `extras` are
the facts the caller passed, kept as syntax because one may be used at several sub-generators, and
elaborating once would freeze its metavariables at the first. -/
partial def walk (extras : Array Term) (goal : MVarId) : TermElabM (List MVarId) :=
  goal.withContext do
  let ty ← whnfR (← instantiateMVars (← goal.getType))
  -- A rule's premise may be a `∀` (a bind's continuation, an `ite`'s branch condition).
  if let .forallE n _ _ _ := ty then
    let (_, goal) ← goal.intro ((← getLCtx).getUnusedName n.eraseMacroScopes)
    return ← walk extras goal
  for j in judgments do
    if let some (g, restate) := j.subject? ty then
      return ← bound j (← j.leaves ty) extras goal restate g
  -- The branch premises of a list combinator, built one branch at a time.
  if let some head := ty.getAppFn.constName? then
    if isBranchList (← getEnv) head then
      let ctor := if (← whnfR ty.appArg!).isAppOfArity ``List.nil 1 then `nil else `cons
      return ← walkAll extras
        (← applyExact goal (← mkConstWithFreshMVarLevels (head ++ ctor)))
  -- A side equation of a bridge or a rule, solved for the metavariable on its right.
  if let some (_, _, rhs) := ty.eq? then
    if rhs.isAppOfArity ``Nat.cast 3 && rhs.appArg!.getAppFn.isMVar then
      solveCast goal
      return []
    if rhs.getAppFn.isMVar || (rhs.isAppOfArity ``HAdd.hAdd 6 && rhs.appFn!.appArg!.isMVar) then
      solveAffine goal
      return []
  -- A side condition with nothing free in it (a literal coin's weight is in range) is decided.
  if !ty.hasFVar && !ty.hasMVar then
    let decided ← observing? do
      let d ← mkDecide ty
      unless (← withTransparency .all (whnf d)).isConstOf ``true do failure
      mkDecideProof ty
    if let some pf := decided then
      goal.assign pf
      return []
  -- A bound that is an output, on something that is no generator: the thing itself.
  if ty.isAppOfArity ``LE.le 4 && (← getEnv).contains `le_refl then
    for (out, val) in [(ty.getArg! 3, ty.getArg! 2), (ty.getArg! 2, ty.getArg! 3)] do
      if out.getAppFn.isMVar && !val.getAppFn.isMVar then
        let val ← tidyExpr val
        if ← isDefEq out val then
          goal.assign (← mkAppOptM `le_refl #[ty.getArg! 0, none, val])
          return []
  return [← goal.replaceTargetDefEq (← instantiateMVars (← goal.getType)).headBeta]

/-- `walk` each goal in turn. -/
partial def walkAll (extras : Array Term) (goals : List MVarId) : TermElabM (List MVarId) :=
  goals.flatMapM (walk extras)

/-- The case of `walk` for a goal of judgment `j` about `g`: a rule for `g`'s combinator, or `g` is
a leaf, closed by a fact or by one of the observation's `leaves`. -/
partial def bound (j : Judgment) (leaves : Leaves) (extras : Array Term) (goal : MVarId)
    (restate : Expr → Expr) (g : Expr) : TermElabM (List MVarId) := goal.withContext do
  -- The reductions cover a branch that is still a redex or a projection (`(fun () => …) ()`,
  -- `p.2 ()`); no combinator is reducible, so no reduction can turn one combinator into another.
  -- The goal is restated in the reduced form before the rule is applied: matching a rule against
  -- an unreduced branch closes a side condition like `xs ≠ []` by proof irrelevance rather than by
  -- unification, and the side condition then survives as a goal.
  let forms := #[g, ← whnfCore g, ← whnfR g]
  -- Whether some rule's conclusion unified: one that did not was stated for another observation.
  let ruleApplied ← IO.mkRef false
  let finish (g' : Expr) (goal : MVarId) (premises : List MVarId) := do
    ruleApplied.set true
    walkAll extras (← namePremises (some g') (← goal.getType) premises)
  let applyRule (goal : MVarId) (lem : Name) : TermElabM (List MVarId) := do
    let rule ← mkConstWithFreshMVarLevels lem
    let tag ← goal.getTag
    let goalTy ← instantiateMVars (← goal.getType)
    let names := if drawTag.isPrefixOf tag then some (tag.replacePrefix drawTag .anonymous, none)
      else postNames goalTy
    applyExact goal (← mkExpectedTypeHint rule (nameBound (← inferType rule) names))
  let rules : TermElabM (Option (List MVarId)) := do
    for g' in forms do
      let some lems := (← j.ruleHead? g').bind (rulesFor (← getEnv) j.key) | continue
      let goal ← if g' == g then pure goal else goal.change (restate g')
      if let some gs ← firstApplying lems (applyRule goal) (finish g' goal) then return some gs
    unless j.adapters.isEmpty do
      for g' in forms do
        let some mapLem := g'.getAppFn.constName?.bind (mapFor (← getEnv)) | continue
        let goal ← if g' == g then pure goal else goal.change (restate g')
        if let some gs ← firstApplying j.adapters (applyMap · mapLem goal) (finish g' goal) then
          return some gs
    return none
  -- A leaf: a caller-supplied fact, a hypothesis (a recursive occurrence), or a proved law, about
  -- `g` or a reduction of it. The fact is committed to before its bridge's premises are walked, so
  -- that a failure inside them is reported where it happens.
  let leaf : TermElabM (Option (List MVarId)) := do
    for t in extras do
      let r ← observing? do
        let e ← Term.withoutErrToSorry do
          let e ← Term.elabTerm t none
          Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
          instantiateMVars e
        let some gs ← tryFact j leaves goal e | failure
        namePremises none (← goal.getType) gs
      if let some gs := r then return some (← walkAll extras gs)
    -- A hypothesis is tried only if it mentions `g`'s head: unifying one about another generator
    -- unfolds both, and on a generator over a long literal list that exceeds the recursion depth.
    let mentionsHead (e : Expr) : Bool := forms.any fun g => match g.getAppFn with
      | .const n _ => (e.find? (·.isConstOf n)).isSome
      | .fvar x => e.containsFVar x
      | _ => true
    for decl in ← getLCtx do
      unless decl.isImplementationDetail do
        unless ← isProp decl.type do continue
        unless mentionsHead (← instantiateMVars decl.type) do continue
        if let some gs ← tryFact j leaves goal decl.toExpr then
          return some (← walkAll extras (← namePremises none (← goal.getType) gs))
    for g in forms do
      for law in ← law? j g do
        if let some gs ← tryFact j leaves goal law then
          return some (← walkAll extras (← namePremises none (← goal.getType) gs))
    return none
  -- A combinator's rules that all fail leave the leaves to try, and their error is reported only if
  -- no leaf applies either.
  let saved ← saveState
  let mut ruleErr : Option Exception := none
  let reduce : TermElabM (Option (List MVarId)) := do
    let some lem := j.reduceTo | return none
    unless (← getEnv).contains lem do return none
    return some (← walkAll extras (← applyExact goal (← mkConstWithFreshMVarLevels lem)))
  for (isRules, step) in if j.leavesFirst then [(false, leaf), (true, reduce), (true, rules)]
      else [(true, reduce), (true, rules), (false, leaf)] do
    try
      if let some gs ← step then return gs
    catch ex =>
      unless isRules do throw ex
      ruleErr := some ex
      saved.restore
  -- A self leaf that stands in for a rule per combinator applies only where such a rule could be.
  let self ← do
    if !leaves.selfOnlyCombinators then pure leaves.self else
    let env ← getEnv
    pure <| if forms.any fun g => (g.getAppFn.constName?.map (isCombinator env ·)).getD false
      then leaves.self else #[]
  -- Where the generator may be left in the bound as itself, a combinator none of whose rules is
  -- about this observation is one more generator nothing is known about.
  if let some ex := ruleErr then
    if self.isEmpty || (← ruleApplied.get) then throw ex
  -- Unfolding comes last, so that a law or a caller's fact stays an abstraction boundary.
  for g' in forms do
    if let some (c, body) ← unfold? g' j.unfoldsCombinators then
      let goal ← goal.change (restate body)
      try return ← walk extras goal
      catch ex => throwError "{ex.toMessageData}\n(in the unfolding of `{c}`)"
  for g' in forms do
    if (← matchMatcherApp? g').isSome then
      throwError "the walk does not enter a `match`:{indentExpr g'}\nOne on the generator's \
        arguments is split before the walk; one on a drawn value, or inside a helper the walk \
        unfolds, is not supported."
  -- A bound on the generator by itself, the tightest first: a later one is a fallback, as a later
  -- rule is.
  let applySelf (lem : Name) : TermElabM (List MVarId) := do
    let lem ← mkConstWithFreshMVarLevels lem
    let names := postNames (← instantiateMVars (← goal.getType))
    applyExact goal (← mkExpectedTypeHint lem (nameBound (← inferType lem) names))
  if let some (some gs) ← observing? (firstApplying self applySelf fun premises => do
      walkAll extras (← namePremises (some g) (← goal.getType) premises)) then
    return gs
  throwError j.noLeaf g

end

end Basalt.Walk
