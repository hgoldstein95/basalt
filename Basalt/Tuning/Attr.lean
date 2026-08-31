/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/

import Lean
import Basalt.Combinators
import Basalt.Tuning

/-!
# The `@[tunable]` attribute

`@[tunable]` makes a generator's `frequency` weights runtime-addressable. If the user tags a
generator definition:

```lean
@[tunable]
def genBST [Gen G] (lo hi : Int) : G (Tree Int) := do
  if h : lo > hi then return leaf
  else frequency [
    (1, fun _ => pure leaf),
    (5, fun _ => do … genBST … genBST …)
  ] (by simp)
partial_fixpoint
```

the attribute emits:

- `genBST.tuned (θ : Tuning) …` — the same generator reading its weights from `θ` (`Tuning.weight`);
- `genBST.defaults : Tuning` — the inline literal weights;
- `genBST.sites : Array Site` — the site metadata (offsets, arities, holes);
- `theorem genBST.tuned_defaults : genBST.tuned genBST.defaults … = genBST …` — proved by `Eq.refl`,
  checked by the kernel, so adopting tuning changes no existing proof.

## Conventions

- **Weights must be positive `Nat` literals.**  A literal `0` is rejected: a zero weight removes its
  branch from the generator's support, breaking `IsSoundAndComplete` (see `Basalt.Tuning`).  A zero
  entry in a *runtime* `θ` cannot do the same damage — `Tuning.weight` clamps to `1`.
- **Site names** are `<defName>.site<i>`, numbered outside-in in traversal order.
- **Depth**: if a `Nat` binder named `depth` is in scope at a site, that site reads its weights at
  that depth; otherwise at depth `0`.  Use `@[tunable (depth := lvl)]` when the binder is named
  something else — a name given explicitly must be found, and a site that cannot see it is an error.
  Because the search is over the local context at the site, it finds the binder wherever the
  recursion form happens to put it — including inside a `partial_fixpoint` functional, where it is
  not one of the declaration's own lambda binders at all.
- **`partial_fixpoint` bodies**: the attribute rebuilds `Lean.Order.fix`'s monotonicity proof for
  the tuned body, so a combinator used there still needs its `@[partial_fixpoint_monotone]` lemma.
-/

open Lean Meta Elab

namespace Basalt.Tuning

/-! ## Attribute syntax -/

/-- `@[tunable]`, optionally `@[tunable (depth := lvl)]` — see the module docstring. -/
syntax (name := tunableAttr) "tunable" (" (" &"depth" " := " ident ")")? : attr

/-! ## The rewrite -/

/-- What the traversal collects. -/
structure TuneState where
  /-- Next free index into `Tuning.schedules`. -/
  nextOffset : Nat := 0
  /-- The inline literal weights, flattened across sites — this becomes `<def>.defaults`. -/
  defaults : Array (Nat × Nat) := #[]
  /-- One entry per `frequency` site, in outside-in order. -/
  sites : Array Site := #[]
  deriving Inhabited

/-- `StateRefT` (not `StateT`): `Lean.Meta.transform` needs `MonadControlT MetaM`. -/
abbrev TuneM := StateRefT TuneState MetaM

/-- Everything the traversal needs to know that does not change as it descends. -/
structure TuneCtx where
  /-- The declaration being tuned; its auxiliaries are inlined and its sites are named after it. -/
  declName : Name
  /-- The fresh `θ : Tuning` local, free in the rewritten body. -/
  θ : Expr
  /-- The binder name to read the recursion depth from, and whether the user named it explicitly
  (in which case failing to find it is an error). -/
  depthName : Name
  depthExplicit : Bool
  /-- The declaration's own lambda binders — never recursive occurrences. -/
  outer : Array FVarId

/-- The elements of a `List` literal, if `e` is one. -/
private partial def listLitElems? (e : Expr) : Option (List Expr) :=
  if e.isAppOfArity ``List.nil 1 then some []
  else if e.isAppOfArity ``List.cons 3 then
    let args := e.getAppArgs
    (listLitElems? args[2]!).map (args[1]! :: ·)
  else none

/-- The depth expression for a site: the innermost `Nat` local named `ctx.depthName`, or `0`. -/
private def siteDepth (ctx : TuneCtx) : MetaM Expr := do
  let d? ← (← getLCtx).findDeclRevM? fun decl => do
    if decl.isImplementationDetail || decl.userName != ctx.depthName then return none
    return if decl.type.isConstOf ``Nat then some decl.toExpr else none
  match d? with
  | some d => return d
  | none =>
    if ctx.depthExplicit then
      throwError "tunable: `{ctx.declName}` has no `Nat` binder named `{ctx.depthName}` in scope \
        at one of its `frequency` sites — `(depth := {ctx.depthName})` names the binder whose value \
        each site reads its weight schedules at"
    return mkNatLit 0

/-- Is `fv` a recursive occurrence?  The recursion combinators bind exactly two shapes: a function
landing in the generator's own monad (`Lean.Order.fix`'s functional argument, `WellFounded.fix`'s
`ih`), or a structural-recursion `T.below` bundle whose projections are the recursive results.  The
declaration's own binders are excluded, so a generator that *takes* a generator is not miscounted. -/
private def isRecOccurrence (ctx : TuneCtx) (monad : Expr) (fv : FVarId) : MetaM Bool := do
  if ctx.outer.contains fv then return false
  forallTelescopeReducing (← fv.getType) fun _ res => do
    if res.getAppFn == monad then return true
    if let .str _ "below" := res.getAppFn.constName?.getD .anonymous then return true
    return false

/-- Occurrences of `targets` in `e`, counted with multiplicity. -/
private partial def countOccs (targets : Array FVarId) : Expr → Nat
  | .fvar fv => if targets.contains fv then 1 else 0
  | .app f a => countOccs targets f + countOccs targets a
  | .lam _ t b _ | .forallE _ t b _ => countOccs targets t + countOccs targets b
  | .letE _ t v b _ => countOccs targets t + countOccs targets v + countOccs targets b
  | .mdata _ b | .proj _ _ b => countOccs targets b
  | _ => 0

/-- The number of recursive calls in one `frequency` branch. -/
private def branchHoles (ctx : TuneCtx) (monad : Expr) (branch : Expr) : MetaM Nat := do
  let fvs := (Lean.collectFVars {} branch).fvarIds
  let recs ← fvs.filterM (isRecOccurrence ctx monad ·)
  return countOccs recs branch

/-- Inline an auxiliary definition of `ctx.declName` — the `foo._f` that structural recursion hands
to `brecOn`, or well-founded recursion's `foo._unary`.  Matchers are deliberately left alone: they
are the constants the untuned body scrutinises through, and reusing them verbatim is what makes
`tuned_defaults` hold by `rfl`. -/
private def inlineAux? (declName : Name) (e : Expr) : MetaM (Option Expr) := do
  let .const n _ := e.getAppFn | return none
  unless declName.isPrefixOf n && n != declName do return none
  if ← isMatcher n then return none
  let some ci := (← getEnv).find? n | return none
  let some val := ci.value? | return none
  if ← isProp ci.type then return none
  -- a self-referential auxiliary would loop; leave it (and fail later, legibly, if it has a site)
  if (val.find? (·.isConstOf n)).isSome then return none
  unfoldDefinition? e

mutual

/-- Rewrite every `frequency` under `e`.  `pre` handles the three things that are not leaf rewrites:
inlining this declaration's auxiliaries, `Lean.Order.fix` (whose monotonicity proof must be rebuilt),
and the `frequency` sites themselves. -/
private partial def tune (ctx : TuneCtx) (e : Expr) : TuneM Expr :=
  Meta.transform e (pre := fun e => do
    if let some e' ← inlineAux? ctx.declName e then
      return .visit e'
    if e.getAppFn.isConstOf ``Lean.Order.fix && e.getAppNumArgs ≥ 4 then
      return .done (← tuneFix ctx e)
    if e.getAppFn.isConstOf ``frequency && e.getAppNumArgs ≥ 5 then
      return .done (← tuneFrequency ctx e)
    return .continue)

/-- `Lean.Order.fix f hmono`: tune `f`, then re-prove `monotone f'` with the same procedure
`partial_fixpoint` uses.  `θ` is bound outside the fix, so `f'` has exactly `f`'s type and the
recursive occurrences inside it need no rewriting. -/
private partial def tuneFix (ctx : TuneCtx) (e : Expr) : TuneM Expr := do
  let args := e.getAppArgs
  let f := args[2]!
  let f' ← tune ctx f
  if f' == f then
    -- no site inside; leave the fix (and its monotonicity proof) untouched
    return mkAppN e.getAppFn (← args.mapIdxM fun i a => if i < 4 then pure a else tune ctx a)
  let monoTy ← inferType args[3]!
  let monoTy' := monoTy.replace fun x => if x == f then some f' else none
  let hmono ← mkFreshExprMVar monoTy'
  try
    Monotonicity.solveMono (goal := hmono.mvarId!)
  catch ex =>
    throwError "tunable: could not re-prove monotonicity of `{ctx.declName}`'s tuned body.\n\
      A `frequency` whose weights read a `Tuning` needs the same `@[partial_fixpoint_monotone]` \
      lemmas the untuned body used.\n{ex.toMessageData}"
  let args ← args.mapIdxM fun i a => if i < 4 then pure a else tune ctx a
  return mkAppN e.getAppFn ((args.set! 2 f').set! 3 (← instantiateMVars hmono))

/-- One `frequency` site: literal weights become `Tuning.weight θ (offset + j) d` reads, and the
positivity side condition is replaced by one that holds for every `θ`.  The site is recorded
*before* its branches are traversed, so offsets — and hence site names — run outside-in. -/
private partial def tuneFrequency (ctx : TuneCtx) (e : Expr) : TuneM Expr := do
  let args := e.getAppArgs
  let monad := args[0]!
  let α := args[1]!
  let inst := args[2]!
  let gs := args[3]!
  let some elems := listLitElems? gs
    | throwError "tunable: `{ctx.declName}` has a `frequency` whose branch list is not a literal \
        list of `(weight, generator)` pairs — the weights have to be visible to be collected"
  if elems.isEmpty then
    throwError "tunable: `{ctx.declName}` has a `frequency` with no branches"
  let d ← siteDepth ctx
  let offset := (← get).nextOffset
  let mut weights : Array Expr := #[]
  let mut gens : Array Expr := #[]
  let mut defaults : Array (Nat × Nat) := #[]
  let mut holes : Array Nat := #[]
  for (elem, j) in elems.zipIdx do
    let eargs := elem.getAppArgs
    unless elem.getAppFn.isConstOf ``Prod.mk && eargs.size == 4 do
      throwError "tunable: `{ctx.declName}` has a `frequency` branch that is not a literal \
        `(weight, generator)` pair:{indentExpr elem}"
    let some w := eargs[2]!.nat?
      | throwError "tunable: weights must be `Nat` literals — they become the entries of \
          `{ctx.declName}.defaults`; got:{indentExpr eargs[2]!}"
    if w == 0 then
      throwError "tunable: a literal weight of 0 is rejected: a zero weight removes its branch \
        from the generator's support (see `SPMF.support_frequency`), breaking support-completeness \
        (`IsSoundAndComplete`). To prune a branch, remove it from the source instead."
    defaults := defaults.push (w, 0)
    holes := holes.push (← branchHoles ctx monad eargs[3]!)
    weights := weights.push (← mkAppM ``Tuning.weight #[ctx.θ, mkNatLit (offset + j), d])
    gens := gens.push eargs[3]!
  let siteName := ctx.declName ++ Name.mkSimple s!"site{(← get).sites.size}"
  modify fun st => { st with
    nextOffset := offset + elems.length
    defaults := st.defaults ++ defaults
    sites := st.sites.push ⟨siteName, offset, elems.length, holes⟩ }
  let tunedGens ← gens.mapM (tune ctx)
  let genTy ← mkArrow (mkConst ``Unit) (mkApp monad α)
  let prodTy ← mkAppM ``Prod #[mkConst ``Nat, genTy]
  let pairs ← (weights.zip tunedGens).toList.mapM fun (w, g) => mkAppM ``Prod.mk #[w, g]
  let gs' ← mkListLit prodTy pairs
  let tl ← mkListLit prodTy pairs.tail
  let h' ← mkAppOptM ``Tuning.sum_map_fst_pos
    #[genTy, ctx.θ, mkNatLit offset, d, tunedGens[0]!, tl]
  let rest ← (args.extract 5 args.size).mapM (tune ctx)
  return mkAppN e.getAppFn (#[monad, α, inst, gs', h'] ++ rest)

end

/-! ## Emitting the declarations -/

/-- `⟨#[(a₀, b₀), …]⟩ : Tuning` as a closed term. -/
private def mkTuningLit (entries : Array (Nat × Nat)) : MetaM Expr := do
  let natTy := mkConst ``Nat
  let pairTy := mkAppN (mkConst ``Prod [0, 0]) #[natTy, natTy]
  let elems := entries.toList.map fun (a, b) =>
    mkAppN (mkConst ``Prod.mk [0, 0]) #[natTy, natTy, mkNatLit a, mkNatLit b]
  return mkApp (mkConst ``Tuning.mk) (← mkAppM ``List.toArray #[← mkListLit pairTy elems])

/-- `#[⟨name, offset, arity, holes⟩, …] : Array Site` as a closed term. -/
private def mkSitesLit (sites : Array Site) : MetaM Expr := do
  let elems := sites.toList.map fun s =>
    mkAppN (mkConst ``Site.mk) #[toExpr s.name, toExpr s.offset, toExpr s.arity, toExpr s.holes]
  mkAppM ``List.toArray #[← mkListLit (mkConst ``Site) elems]

/-- Tune one declaration's body: introduce `θ` after the first `k` binders of `type`, rewrite the
`frequency` sites under it, and re-abstract.  Taking the binders from the *type* rather than the
value's own lambdas eta-expands as needed, so `k` means the same thing for a `partial_fixpoint`
definition (whose arguments live inside the fix) as for a structural one (whose arguments do not). -/
private def tuneBody (declName : Name) (depthName? : Option Name) (type value : Expr) (k : Nat) :
    MetaM (Expr × TuneState) :=
  StateRefT'.run (s := ({} : TuneState)) <|
    forallBoundedTelescope type k fun xs _ =>
      withLocalDeclD `θ (mkConst ``Tuning) fun θ => do
        let ctx : TuneCtx :=
          { declName, θ
            depthName := depthName?.getD `depth
            depthExplicit := depthName?.isSome
            outer := xs.map (·.fvarId!) }
        mkLambdaFVars (xs.push θ) (← tune ctx (value.beta xs))

/-- Executable code for a recursive definition comes from its `_unsafe_rec` companion, looked up by
name, so the tuned generator needs its own.  Recursion there is a self-reference to a constant rather
than a bound variable, and it is rewritten to pass `θ` along. -/
private def tuneUnsafeRec (declName tunedName : Name) (depthName? : Option Name) (k : Nat)
    (safe : TuneState) : MetaM Bool := do
  let unsafeName := Compiler.mkUnsafeRecName declName
  let some uci := (← getEnv).find? unsafeName | return false
  let some uvalue := uci.value? | return false
  let tunedUnsafeName := Compiler.mkUnsafeRecName tunedName
  let lvlArgs := uci.levelParams.map mkLevelParam
  let (val, st) ← tuneBody declName depthName? uci.type uvalue k
  -- The two bodies are traversed independently, so the schedule indices they read have to be
  -- checked to agree: same site boundaries, same weights, in the same order.  `Site.holes` is
  -- excluded because it legitimately differs — recursion here is a constant self-reference rather
  -- than a bound variable — and only the safe pass's holes are ever emitted.
  let layout (s : TuneState) := (s.defaults, s.sites.map fun site => (site.offset, site.arity))
  unless layout st == layout safe do
    throwError "tunable: `{declName}` and `{unsafeName}` disagree about the layout of their \
      `frequency` sites, so the tuned generator would not run the distribution it denotes"
  let val ← lambdaBoundedTelescope val (k + 1) fun ys body => do
    -- `ys = x₀ … x_{k-1} θ`; a self-reference becomes the same call with `θ` spliced in
    let self ← mkLambdaFVars (ys.extract 0 k) (mkAppN (mkConst tunedUnsafeName lvlArgs) ys)
    let body := body.replace fun e => if e.isConstOf unsafeName then some self else none
    -- `self` is a `k`-ary closure, so the substitution leaves beta-redexes behind
    mkLambdaFVars ys (← Meta.transform body (post := fun e => return .done e.headBeta))
  -- a `mutualDefnDecl` block, even a singleton one, is what lets the value name itself
  addAndCompile <| .mutualDefnDecl
    [{ name := tunedUnsafeName, levelParams := uci.levelParams, type := ← inferType val
       value := val, hints := .opaque, all := [tunedUnsafeName]
       safety := match uci with | .defnInfo di => di.safety | _ => .unsafe }]
  return true

/-- The whole emission: `<def>.tuned`, `.defaults`, `.sites`, `.tuned_defaults`. -/
def tuneDecl (declName : Name) (depthName? : Option Name) : MetaM Unit := do
  let some ci := (← getEnv).find? declName
    | throwError "tunable: unknown declaration `{declName}`"
  let some value := ci.value?
    | throwError "tunable: `{declName}` has no value to tune"
  unless ci matches .defnInfo _ do
    throwError "tunable: `{declName}` is not a `def`"
  -- The attribute runs in a fresh `MetaM`; a surviving metavariable would only surface much later,
  -- as an `unknown universe metavariable` reported against the definition. Reject it here.
  if value.hasExprMVar || value.hasLevelMVar || ci.type.hasExprMVar || ci.type.hasLevelMVar then
    throwError "tunable: `{declName}` still contains metavariables — give the definition an \
      explicit type (and explicit universe parameters, if it has any)"
  -- `θ` goes just before the first explicit binder, so `foo.tuned θ x y` reads like `foo x y`
  let θIdx ← forallTelescope ci.type fun xs _ =>
    return (← xs.findIdxM? fun x => return (← x.fvarId!.getBinderInfo).isExplicit).getD xs.size
  let (val, st) ← tuneBody declName depthName? ci.type value θIdx
  if st.sites.isEmpty then
    throwError "tunable: no `frequency` site in `{declName}` — nothing to tune"
  let lvls := ci.levelParams
  let lvlArgs := lvls.map mkLevelParam
  let tunedName := declName ++ `tuned
  let defaultsName := declName ++ `defaults
  let sitesName := declName ++ `sites
  -- The tuned declaration has to exist before its `_unsafe_rec` companion can name it. Where there
  -- is such a companion it *is* the executable code — the compiler resolves `foo` through
  -- `foo._unsafe_rec` — so only a generator without one is compiled directly.
  let tunedDecl : Declaration := .defnDecl
    { name := tunedName, levelParams := lvls, type := ← inferType val, value := val
      hints := .regular (getMaxHeight (← getEnv) val + 1), safety := .safe }
  addDecl tunedDecl
  unless ← tuneUnsafeRec declName tunedName depthName? θIdx st do
    compileDecl tunedDecl
  addAndCompile <| .defnDecl
    { name := defaultsName, levelParams := [], type := mkConst ``Tuning
      value := ← mkTuningLit st.defaults, hints := .abbrev, safety := .safe }
  addAndCompile <| .defnDecl
    { name := sitesName, levelParams := []
      type := mkApp (mkConst ``Array [.zero]) (mkConst ``Site)
      value := ← mkSitesLit st.sites, hints := .abbrev, safety := .safe }
  -- `tuned_defaults` is `Eq.refl` typed at `tuned defaults args = orig args`: the two bodies differ
  -- only where a literal weight became `Tuning.weight defaults i d`, which reduces back to it.
  -- `addDecl` hands this straight to the kernel, which has no smart unfolding to get in the way.
  let (thmType, thmVal) ← forallTelescope ci.type fun targs _ => do
    let lhs := mkAppN (mkConst tunedName lvlArgs)
      (targs[:θIdx] ++ #[mkConst defaultsName] ++ targs[θIdx:])
    let rhs := mkAppN (mkConst declName lvlArgs) targs
    return (← mkForallFVars targs (← mkEq lhs rhs), ← mkLambdaFVars targs (← mkEqRefl rhs))
  addDecl <| .thmDecl
    { name := declName ++ `tuned_defaults, levelParams := lvls, type := thmType, value := thmVal }
  -- keep `.tuned` as unfoldable as the original, so `simp`/`rw` behave the same on both
  if (← getReducibilityStatus declName) matches .irreducible then
    setIrreducibleAttribute tunedName

initialize registerBuiltinAttribute {
  name := `tunableAttr
  descr := "emit `θ`-threaded weights for this generator's `frequency` sites"
  applicationTime := .afterCompilation
  add := fun declName stx kind => do
    unless kind == .global do
      throwError "tunable: must be a global attribute"
    let depthName? ← match stx with
      | `(attr| tunable) => pure none
      | `(attr| tunable (depth := $i:ident)) => pure (some i.getId)
      | _ => throwError "tunable: expected `@[tunable]` or `@[tunable (depth := binderName)]`"
    MetaM.run' (tuneDecl declName depthName?)
}

end Basalt.Tuning
