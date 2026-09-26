/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Lean.Meta.Match.MatcherApp.Transform
import Lean.Meta.Tactic.Assumption
import Lean.Elab.Tactic.Simproc
import Lean.Meta.Tactic.Simp.Main
import Basalt.Walk.Attr

/-!
# Entering a `match`

A `match` is walked by one lemma per matcher, `m.walk_congr`, which relates two applications of
the matcher alternative by alternative. On a bound, the bound is made the same `match` over a fresh
bound per alternative, as `spec_ite_le` makes it an `if`.
-/

open Lean Meta

namespace Basalt.Walk

/-- `e`, a `match` on arbitrary discriminants, rewritten to its `k`-th alternative by that
alternative's congruence equation, whose hypotheses are in the context: `rwMatcher`, except that a
pattern's field that is a proof is found by `assumption`. Unifying the discriminant with the pattern
equates such a field by proof irrelevance without assigning it, and `rwMatcher` gives up on
`⟨n, _, h⟩`. -/
private def rwAlt (k : Nat) (e : Expr) : MetaM Simp.Result := do
  let some m := e.getAppFn.constName? | throwError "walk: not a `match`{indentExpr e}"
  let eqns ← Match.genMatchCongrEqns m
  let thm := mkAppN (mkConst eqns[k]! e.getAppFn.constLevels!) e.getAppArgs
  let (hyps, _, eqType) ← forallMetaTelescope (← inferType thm)
  let eqn := eqns[k]!
  let some (_, lhs, _, rhs) := eqType.heq? | throwError "walk: `{.ofConstName eqn}` is no `HEq`"
  unless ← isDefEq e lhs do throwError "walk: `{.ofConstName eqn}` does not rewrite{indentExpr e}"
  -- The equations first, which assign the pattern's fields that are not proofs.
  for h in hyps do
    let t ← h.mvarId!.getType
    if t.isEq || t.isHEq || Simp.isEqnThmHypothesis t then h.mvarId!.assumption
  for h in hyps do
    unless ← h.mvarId!.isAssigned do h.mvarId!.assumption
  let proof ← mkEqOfHEq (← instantiateMVars (mkAppN thm hyps))
  return { expr := ← instantiateMVars rhs, proof? := proof }

/-- `m.walk_congr`, for the matcher `m` whose motive's universe is its `pos`-th: for
`R : α → β → Prop`, the matcher taken at `α` on the left and at `β` on the right,

`(hᵢ : ∀ fields overlaps (h : ds = pᵢ fields), R (altᵢ …) (cᵢ …)) → R (m ds alts) (m ds cs)`.

Each alternative is proved through the splitter, the two `match`es rewritten by the congruence
equation for it, which takes the discriminants as they are rather than abstracted: under
`match h :` an alternative's type mentions the discriminants. -/
private def mkCongrLemma (m : Name) (info : MatcherInfo) (pos : Nat) (name : Name) :
    MetaM Unit := do
  let cinfo ← getConstInfo m
  let lps := cinfo.levelParams
  let fresh (n : Name) := if lps.contains n then n.appendIndexAfter lps.length else n
  let uα := fresh `uα
  let uβ := fresh `uβ
  let levels (u : Name) := (lps.set pos u).map Level.param
  forallTelescope cinfo.type fun xs _ => do
  let params := xs[:info.numParams].toArray
  let ds := xs[info.numParams + 1:info.numParams + 1 + info.numDiscrs].toArray
  withLocalDecl `α .implicit (.sort (.param uα)) fun α => do
  withLocalDecl `β .implicit (.sort (.param uβ)) fun β => do
  withLocalDecl `R .implicit (← mkArrow α (← mkArrow β (mkSort 0))) fun R => do
  let head (u : Name) (T : Expr) : MetaM Expr := do
    return mkAppN (mkApp (mkAppN (mkConst m (levels u)) params) (← mkLambdaFVars ds T)) ds
  let hA ← head uα α
  let hB ← head uβ β
  let decls (base : Name) (tys : Array Expr) :=
    tys.mapIdx fun k t => (base.appendIndexAfter (k + 1), BinderInfo.implicit, fun _ => pure t)
  withLocalDecls (decls `alt (← inferArgumentTypesN info.numAlts hA)) fun alts => do
  withLocalDecls (decls `c (← inferArgumentTypesN info.numAlts hB)) fun cs => do
  let lhs := mkAppN hA alts
  let rhs := mkAppN hB cs
  let concl := mkApp2 R lhs rhs
  let lctx ← getLCtx
  let insts ← getLocalInstances
  let hyps ← IO.mkRef #[]
  -- `transform` instantiates each alternative, so it is given them eta-expanded.
  let etaAlts ← alts.mapIdxM fun k alt => do
    forallBoundedTelescope (← inferType alt) (some (info.altNumParams[k]!)) fun ys _ =>
      mkLambdaFVars ys (mkAppN alt ys)
  let ma : MatcherApp := { info with
    matcherName := m, matcherLevels := (levels uα).toArray, params,
    motive := ← mkLambdaFVars ds α, discrs := ds, alts := etaAlts, remaining := #[] }
  let ma' ← ma.transform (useSplitter := true) (addEqualities := true)
    (onMotive := fun _ _ => pure concl)
    (onAlt := fun k _ fvars _ => do
      let rA ← rwAlt k lhs
      let rB ← rwAlt k rhs
      let hTy ← mkForallFVars fvars.all (mkApp2 R rA.expr rB.expr)
      let h ← withLCtx lctx insts (mkFreshExprMVar hTy)
      hyps.modify (·.push h)
      let eq ← mkCongr (← mkCongrArg R (← rA.getProof)) (← rB.getProof)
      mkEqMPR eq (mkAppN h fvars.all))
  let hs ← hyps.get
  let hTys ← hs.mapIdxM fun k h => do
    return ((`h).appendIndexAfter (k + 1), ← instantiateMVars (← h.mvarId!.getType))
  withLocalDeclsDND hTys fun hfvs => do
  for h in hs, f in hfvs do h.mvarId!.assign f
  let vars := params ++ #[α, β, R] ++ ds ++ alts ++ cs ++ hfvs
  addDecl <| .thmDecl {
    name, levelParams := lps.eraseIdx pos ++ [uα, uβ]
    type := ← mkForallFVars vars concl
    value := ← mkLambdaFVars vars (← instantiateMVars ma'.toExpr) }

/-- The name of `m.walk_congr` (`mkCongrLemma`), generated on first use. `none` for a matcher that
eliminates only into `Prop`. -/
def congrLemma? (m : Name) : MetaM (Option Name) := do
  let some info ← getMatcherInfo? m | return none
  let some pos := info.uElimPos? | return none
  let name := m ++ `walk_congr
  realizeConst m name (mkCongrLemma m info pos name)
  return some name

/-- The type a `match` returns, when it does not depend on the discriminants. -/
private def constMotive? (ma : MatcherApp) : MetaM (Option Expr) :=
  lambdaBoundedTelescope ma.motive ma.discrs.size fun xs b => do
    return if xs.size == ma.discrs.size && !b.hasAnyFVar (xs.contains <| .fvar ·) then some b
      else none

/-- `ma`'s matcher taken at `β`, of its universe `u`, on `ma`'s discriminants: without its
alternatives. -/
private def matcherAt (ma : MatcherApp) (pos : Nat) (u : Level) (β : Expr) : MetaM Expr := do
  let motive ← lambdaTelescope ma.motive fun xs _ => mkLambdaFVars xs β
  let levels := ma.matcherLevels.set! pos u
  return mkAppN (mkApp (mkAppN (mkConst ma.matcherName levels.toList) ma.params) motive) ma.discrs

/-- `m.walk_congr` for `e`, a `match`, at `R`, relating it to `ma`'s matcher at `β` over the
alternatives `cs`: the lemma applied up to its hypotheses, and the level of `β`. -/
private def congrApp? (ma : MatcherApp) (R β : Expr) (uβ : Level) (cs : Array Expr) :
    MetaM (Option Expr) := do
  let some pos := ma.uElimPos? | return none
  let some α ← constMotive? ma | return none
  let some lem ← congrLemma? ma.matcherName | return none
  let levels := ma.matcherLevels.eraseIdx! pos |>.push ma.matcherLevels[pos]! |>.push uβ
  return mkAppN (mkConst lem levels.toList) (ma.params ++ #[α, β, R] ++ ma.discrs ++ ma.alts ++ cs)

/-- The goals `app`'s hypotheses leave, one per alternative, with `R` reduced away, and `app`
applied to them. -/
private def congrGoals (app : Expr) (n : Nat) : MetaM (Expr × Array Expr) := do
  let mut t ← inferType app
  let mut hs := #[]
  for _ in [0:n] do
    let .forallE _ d b _ := t | throwError "walk: a `match` congruence with too few hypotheses"
    let h ← mkFreshExprSyntheticOpaqueMVar (← Core.betaReduce d)
    hs := hs.push h
    t := b.instantiate1 h
  return (mkAppN app hs, hs)

/-- Prove `goal`, the statement `restate g` of judgment `j` about `g`, a `match`, by
`m.walk_congr`, one goal per alternative. On a bound, the bound is made the same `match`, at the
bound's type, of a fresh bound per alternative over its fields. On a relation, the counterpart must
be the same matcher on the same discriminants. `none` when the `match` is not one of these. -/
def matchCongr? (j : Judgment) (goal : MVarId) (restate : Expr → Expr) (g : Expr) :
    MetaM (Option (List MVarId)) := goal.withContext do
  let some ma ← matchMatcherApp? g | return none
  let some pos := ma.uElimPos? | return none
  unless ma.remaining.isEmpty do return none
  let ty ← instantiateMVars (restate g)
  let some i := (match j with
      | .spec upper => some (if upper then 3 else 2)
      | .rel _ => some (ty.getAppNumArgs - 1)
      | .mix _ => none) | return none
  let other ← instantiateMVars (ty.getArg! i)
  let some (β, uβ, cs) ← (match j with
    | .rel _ => do
      let some mb ← matchMatcherApp? other | return none
      unless mb.matcherName == ma.matcherName && mb.remaining.isEmpty do return none
      let (xs, ys) := (ma.params ++ ma.discrs, mb.params ++ mb.discrs)
      unless xs.size == ys.size do return none
      unless ← (xs.zip ys).allM fun (a, b) => isDefEq a b do return none
      let some β ← constMotive? mb | return none
      return some (β, mb.matcherLevels[pos]!, mb.alts)
    | _ => do
      unless other.getAppFn.isMVar do return none
      let β ← inferType other
      let uβ ← getLevel β
      let aux ← matcherAt ma pos uβ β
      -- A bound's alternative is a pattern in its fields, so that the walk can assign it; one
      -- thunked by `Unit`, or taking a discriminant's equation, ignores that argument.
      let cs ← (← inferArgumentTypesN ma.alts.size aux).mapIdxM fun k t =>
        forallBoundedTelescope t (some ma.altInfos[k]!.numFields) fun ys t => do
          let c ← mkFreshExprMVar (some β)
          forallTelescope t fun zs _ => mkLambdaFVars (ys ++ zs) c
      unless ← isDefEq other (mkAppN aux cs) do return none
      return some (β, uβ, cs) : MetaM _) | return none
  let R ← withLocalDeclD `a (← inferType g) fun a => withLocalDeclD `b β fun b => do
    let t := restate a
    mkLambdaFVars #[a, b] (mkAppN t.getAppFn (t.getAppArgs.set! i b))
  let some app ← congrApp? ma R β uβ cs | return none
  let (pf, hs) ← congrGoals app ma.alts.size
  unless ← isDefEq (← inferType pf) (← instantiateMVars ty) do
    throwError "walk: `{.ofConstName ma.matcherName}.walk_congr` does not conclude{indentExpr ty}"
  goal.assign pf
  return some (hs.map (·.mvarId!)).toList

/-- `e = b`, when `e` is a `match` whose alternatives are all the one value `b`, as `ite_self` says
of an `if`: `m.walk_congr` at `R := fun x _ => x = b`. -/
def collapseMatch? (e : Expr) : MetaM (Option Simp.Result) := do
  let some ma ← matchMatcherApp? e | return none
  unless ma.remaining.isEmpty do return none
  let bodies := (ma.alts.zip ma.altNumParams).map fun (alt, k) => Id.run do
    let mut b := alt
    for _ in [0:k] do
      let .lam _ _ b' _ := b | return none
      b := b'
    return if b.hasLooseBVars then none else some b
  let some b := bodies[0]?.join | return none
  unless bodies.all (· == some b) do return none
  let some pos := ma.uElimPos? | return none
  let some α ← constMotive? ma | return none
  let R ← withLocalDeclD `x α fun x => withLocalDeclD `y α fun y => do
    mkLambdaFVars #[x, y] (← mkEq x b)
  let some app ← congrApp? ma R α ma.matcherLevels[pos]! ma.alts | return none
  let (_, hs) ← congrGoals app ma.alts.size
  for h in hs do
    h.mvarId!.assign (← forallTelescope (← h.mvarId!.getType) fun xs _ => do
      mkLambdaFVars xs (← mkEqRefl b))
  let pf ← instantiateMVars (mkAppN app hs)
  return some { expr := b, proof? := some (← mkExpectedTypeHint pf (← mkEq e b)) }

/-- A `match` whose alternatives are all one value is that value (`collapseMatch?`). -/
simproc_decl matchConst (_) := fun e => do
  let some r ← collapseMatch? e | return .continue
  return .visit r

/-- `e` with every `match` whose alternatives are all one value replaced by that value. -/
def collapseMatches (e : Expr) : MetaM Simp.Result := do
  let ctx ← Simp.mkContext (config := { Simp.neutralConfig with dsimp := false })
  (·.1) <$> Simp.main e ctx (methods := { post })
where
  post (e : Expr) : SimpM Simp.Step := do
    let some r ← collapseMatch? e | return .continue
    return .visit r

end Basalt.Walk
