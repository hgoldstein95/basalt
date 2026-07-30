/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/

import Lean
import Basalt.Tuning

/-!
# The `tunable def` macro

`tunable def` makes a generator's `frequency` weights runtime-addressable.  Prefix an ordinary
generator definition:

```lean
tunable def genBST [Gen G] (lo hi : Nat) : G (Tree Nat) := do
  if h : lo > hi then return leaf
  else frequency [
    (1, fun _ => pure leaf),
    (5, fun _ => do … genBST … genBST …)
  ] (by simp)
partial_fixpoint
```

and, alongside `genBST` itself (elaborated exactly as written), the macro emits:

- `genBST.Weights` — a record with one `Nat × Nat` field per `frequency` branch, named after the
  constructor that branch produces (`leaf`, `node`, …) and defaulting to the source weight. This is
  what lets a caller write `genBST.tuned { node := (2, 0) }` — weights *by constructor name* — rather
  than a positional `Tuning`. A `Tuning` still coerces in (`Coe Tuning genBST.Weights`), so a
  weighting held as a flat `Tuning` keeps working;
- `genBST.tuned (θ : genBST.Weights) …` — the same generator reading its weights from `θ`
  (via `θ.toTuning` and `Tuning.weight`), with recursive calls threading `θ`;
- `genBST.defaults : genBST.Weights` — the record `{}` (every field at its source weight);
- `genBST.sites : Array Site` — the site metadata (offsets, arities, holes);
- `theorem genBST.tuned_defaults : genBST.tuned genBST.defaults … = genBST …` — definitional (`rfl`
  after unsealing `partial_fixpoint`'s `@[irreducible]`), so adopting tuning changes no existing
  proof.

## Field naming

Fields are named after the constructor each branch produces, inferred syntactically from the branch
body (`branchResultName?`): `fun _ => pure leaf` ↦ `leaf`, `… return node l x r` ↦ `node`. A branch
whose result constructor cannot be read off (it ends in a `match`, say) gets a positional field name
`field<i>`; a constructor that names two branches is disambiguated with a numeric suffix (`leaf_1`).

## Conventions

- **Weights must be positive `Nat` literals.** A literal `0` is rejected: a zero weight removes its
  branch from the generator's support, breaking `IsSoundAndComplete` (see `Basalt.Tuning`).
- **Site names** default to `<defName>.site<i>` in traversal order; override per site with
  `frequency (site := `myName) […]`. The named argument is a `tunable def` annotation, stripped before
  elaboration.
- **Depth**: if the definition has an explicit binder literally named `depth`, each site reads its
  weights at that depth; otherwise at depth `0`.  Depth-indexed schedules only mean something under a
  recursion that threads a depth, and the macro does not invent one.
- **Recursive calls** are detected syntactically, by name-suffix match against the definition's
  name. Write recursive calls the way the definition is named.

## Limitations

We can currently only support recursion vi `partial_fixpoint`. Both structural and well-founded
recursion elaborate to forms that introduce unique matches; this means that the tuned and untuned
versions cannot be reflexively equal.

NOTE: I suspect that a change to the match compiler could fix this. It's worth exploring later.
-/

open Lean Elab Command

namespace Basalt.Tuning.Macro

/-- Everything the macro learns about one `frequency` site. -/
structure SiteInfo where
  name : Name
  offset : Nat
  arity : Nat
  holes : Array Nat
  defaults : Array (Nat × Nat)
  /-- The constructor each branch is inferred to produce (see `branchResultName?`), for naming the
  fields of the generator's weights record. `none` when no constructor could be read off the branch;
  a positional field name is used in that case. -/
  fields : Array (Option Name)

/-- State threaded through the body traversal. -/
structure TraversalState where
  sites : Array SiteInfo := #[]
  /-- Next free index into `Tuning.schedules`. -/
  nextOffset : Nat := 0
  /-- Positional counter for default site names. -/
  nextSiteIdx : Nat := 0

/-- Does identifier `n` refer to the definition being processed? Syntactic: the user may write
`genBST` or `Tree.genBST` for a definition named `Tree.genBST`, so match on name suffixes in either
direction. -/
def matchesRec (declName n : Name) : Bool :=
  -- `Name.anonymous.isSuffixOf` is `true` for everything, and anonymous idents
  -- occur throughout parsed syntax (`hygieneInfo` nodes) — never match them
  !n.isAnonymous &&
    (n == declName || n.isSuffixOf declName || declName.isSuffixOf n)

/-- Count syntactic occurrences of the definition's name in `stx` — the number of recursive calls
(`Site.holes`). Runs before `partial_fixpoint`, so the recursive occurrences are still present. -/
partial def countRecCalls (declName : Name) (stx : Syntax) : Nat :=
  match stx with
  | .ident _ _ n _ => if matchesRec declName n then 1 else 0
  | .node _ _ args => args.foldl (init := 0) fun acc a => acc + countRecCalls declName a
  | _ => 0

/-- Is `n` a monadic wrapper whose argument, not itself, carries the result value? A branch body
`fun _ => pure leaf` or `… return (node l x r)` produces a `leaf`/`node`, not a `pure`/`return`. -/
def isResultWrapper (n : Name) : Bool :=
  let l := n.eraseMacroScopes.componentsRev.head?.getD n
  l == `pure || l == `return

/-- Infer the constructor a `frequency` branch produces, by walking to the branch's result
expression and reading its head identifier. Used to name the fields of the generated weights record
after the datatype's constructors, so a user can write `{ leaf := …, node := … }`. Returns the last
name component (`BST.Tree.node ↦ `node`); `none` if no head identifier can be read (e.g. the branch
ends in a `match` or a bare variable), in which case the field falls back to a positional name.

Syntactic and best-effort: it descends `fun`/`do`/`return`/`pure`/parens to the tail expression. -/
partial def branchResultName? (stx : Syntax) : Option Name :=
  let last (n : Name) : Name := n.eraseMacroScopes.componentsRev.head?.getD n
  let rec go (s : Syntax) : Option Name :=
    match s with
    | .ident _ _ n _ => if n.isAnonymous then none else some (last n)
    | .node _ kind args =>
      let descLast (a : Array Syntax) : Option Name := a.back?.bind go
      if kind == ``Lean.Parser.Term.fun then (args[1]?).bind go
      else if kind == ``Lean.Parser.Term.basicFun then descLast args
      else if kind == ``Lean.Parser.Term.paren then (args[1]?).bind go
      else if kind == ``Lean.Parser.Term.do then (args[1]?).bind go
      else if kind == ``Lean.Parser.Term.doSeqIndent
           || kind == ``Lean.Parser.Term.doSeqBracketed then (args[0]?).bind fun s => descLast s.getArgs
      else if kind == ``Lean.Parser.Term.doSeqItem then (args[0]?).bind go
      else if kind == ``Lean.Parser.Term.doReturn then (args[1]?).bind go
      else if kind == ``Lean.Parser.Term.doExpr then (args[0]?).bind go
      else if kind == ``Lean.Parser.Term.dotIdent then (args[1]?).bind go
      else if kind == ``Lean.Parser.Term.app then
        match args[0]? with
        | some head =>
          let headName := head.getId
          -- `pure x` / `return x`: the result is `x`, one level in
          if !headName.isAnonymous && isResultWrapper headName then
            ((args[1]?).map Syntax.getArgs).bind fun a => (a[0]?).bind go
          else go head
        | none => none
      else if kind == nullKind then descLast args
      else none
    | _ => none
  go stx

/-- Rewrite recursive calls: `genBST args…` becomes `genBST.tuned θ args ...`. -/
partial def rewriteRecCalls (declName : Name) (tunedId : Ident) (θ : Ident)
    (bareRepl : Syntax) (stx : Syntax) : Syntax :=
  match stx with
  | .ident _ _ n _ => if matchesRec declName n then bareRepl else stx
  | .node info kind args =>
    if kind == ``Lean.Parser.Term.app && matchesRec declName stx[0].getId then
      let restArgs := (args.getD 1 mkNullNode).getArgs.map
        (rewriteRecCalls declName tunedId θ bareRepl)
      .node info kind #[tunedId.raw, mkNullNode (#[θ.raw] ++ restArgs)]
    else
      .node info kind (args.map (rewriteRecCalls declName tunedId θ bareRepl))
  | _ => stx

/-- Extract the site-name override from a `(site := `name)` named argument. -/
def siteNameOfNamedArg (arg : Syntax) : Option Name :=
  if arg.isOfKind ``Lean.Parser.Term.namedArgument then
    if arg[1].getId == `site then
      -- value is arg[3]; accept a quoted name literal `foo.bar
      arg[3][0].isNameLit?.map fun s => s
    else none
  else none

/-- Is this syntax a `(site := …)` named argument? -/
def isSiteNamedArg (arg : Syntax) : Bool :=
  arg.isOfKind ``Lean.Parser.Term.namedArgument && arg[1].getId == `site

/-- Strip `(site := …)` annotations from every `frequency` application. -/
partial def stripSiteArgs (stx : Syntax) : Syntax :=
  match stx with
  | .node info kind args =>
    let args := args.map stripSiteArgs
    if kind == ``Lean.Parser.Term.app && stx[0].getId == `frequency then
      .node info kind (args.map fun a =>
        if a.getKind == nullKind then
          .node a.getHeadInfo nullKind (a.getArgs.filter (!isSiteNamedArg ·))
        else a)
    else
      .node info kind args
  | _ => stx

/-- The core traversal: find each `frequency` application, record a `SiteInfo`, replace its literal
weights with `Tuning.weight $θ i $d` reads, and replace (or install) its positivity proof with one
that holds for every `θ`. -/
partial def rewriteFrequencies (declName : Name) (θ : Term) (dTerm : Term)
    (stx : Syntax) : StateT TraversalState TermElabM Syntax := do
  match stx with
  | .node info kind args =>
    if kind == ``Lean.Parser.Term.app && stx[0].getId == `frequency then
      rewriteFrequencyApp info stx
    else do
      let args ← args.mapM (rewriteFrequencies declName θ dTerm)
      return .node info kind args
  | _ => return stx
where
  rewriteFrequencyApp (info : SourceInfo) (app : Syntax) : StateT TraversalState TermElabM Syntax := do
    let argsNode := app[1]
    unless argsNode.getKind == nullKind do
      throwErrorAt app "tunable def: unexpected shape of `frequency` application"
    let rawArgs := argsNode.getArgs
    for a in rawArgs do
      if isSiteNamedArg a && (siteNameOfNamedArg a).isNone then
        throwErrorAt a "tunable def: `site :=` expects a name literal, e.g. `(site := `myGen.myChoice)`"
    let siteOverride? := rawArgs.findSome? siteNameOfNamedArg
    let posArgs := rawArgs.filter (!isSiteNamedArg ·)
    let some listLit := posArgs.find? (·.isOfKind ``«term[_]»)
      | throwErrorAt app "tunable def: expected a literal list of (weight, generator) branches"
    let extraArgs := posArgs.filter (!·.isOfKind ``«term[_]»)
    -- at most one positional argument besides the list: the positivity proof
    unless extraArgs.size ≤ 1 do
      throwErrorAt app "tunable def: unexpected extra arguments to `frequency`"
    let st ← get
    let offset := st.nextOffset
    let siteIdx := st.nextSiteIdx
    let siteName := siteOverride?.getD (declName ++ Name.mkSimple s!"site{siteIdx}")
    let elems := listLit[1].getArgs
    let mut defaults : Array (Nat × Nat) := #[]
    let mut holes : Array Nat := #[]
    let mut fields : Array (Option Name) := #[]
    let mut newElems : Array Syntax := #[]
    for elem in elems do
      if elem.getKind == nullKind || elem.isOfKind `null then
        newElems := newElems.push elem
        continue
      if !elem.isOfKind ``Lean.Parser.Term.tuple then
        -- separator atoms (commas) pass through
        if elem.isAtom then
          newElems := newElems.push elem
          continue
        throwErrorAt elem "tunable def: each branch must be a literal `(weight, generator)` pair"
      let inner := elem[1]
      let weightStx := inner[0]
      let some w := weightStx.isNatLit?
        | throwErrorAt weightStx "tunable def: weights must be `Nat` literals — they become the entries of `{declName}.defaults`"
      if w == 0 then
        throwErrorAt weightStx "tunable def: a literal weight of 0 is rejected: a zero weight removes its branch from the generator's support (see `SPMF.support_frequency`), breaking support-completeness (`IsSoundAndComplete`). To prune a branch, remove it from the source instead."
      let branchGen := inner[2]
      let j := defaults.size
      defaults := defaults.push (w, 0)
      holes := holes.push (countRecCalls declName branchGen)
      fields := fields.push (branchResultName? branchGen)
      let idx : Nat := offset + j
      let weightTerm ← `(Tuning.weight $θ $(quote idx) $dTerm)
      let elem := elem.setArg 1 (inner.setArg 0 weightTerm.raw)
      newElems := newElems.push elem
    -- record this site before recursing into branches, so offsets read outside-in
    set { st with
      sites := st.sites.push ⟨siteName, offset, defaults.size, holes, defaults, fields⟩
      nextOffset := offset + defaults.size
      nextSiteIdx := siteIdx + 1 }
    let mut recElems : Array Syntax := #[]
    for elem in newElems do
      if elem.isOfKind ``Lean.Parser.Term.tuple then
        let inner := elem[1]
        let branchGen ← rewriteFrequencies declName θ dTerm inner[2]
        recElems := recElems.push (elem.setArg 1 (inner.setArg 2 branchGen))
      else
        recElems := recElems.push elem
    let newListLit := listLit.setArg 1 (.node (listLit[1].getHeadInfo) nullKind recElems)
    -- the positivity proof must hold for every θ; cite `Tuning.weight_pos` for
    -- the site's first branch (one positive summand suffices)
    let proofTerm ← `((by
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      have := Tuning.weight_pos $θ $(quote offset) $dTerm
      omega))
    return .node info ``Lean.Parser.Term.app
      #[app[0], .node (argsNode.getHeadInfo) nullKind #[newListLit, proofTerm.raw]]

/-- Collect the identifiers of the explicit binders (to apply both sides of `tuned_defaults` to),
and whether one of them is named `depth`. -/
def explicitBinderIds (binders : Array Syntax) : Array Ident := Id.run do
  let mut ids : Array Ident := #[]
  for b in binders do
    if b.isOfKind ``Lean.Parser.Term.explicitBinder then
      for id in b[1].getArgs do
        if id.isIdent then
          ids := ids.push ⟨id⟩
  return ids

/-- `tunable def foo … := body partial_fixpoint` — see the module docstring. -/
syntax (name := tunableDef) (docComment)? "tunable " command : command

elab_rules : command
  | `($[$doc?:docComment]? tunable $cmd:command) => do
    let declStx := cmd.raw
    unless declStx.isOfKind ``Lean.Parser.Command.declaration do
      throwErrorAt declStx "tunable: expected a definition"
    let defn := declStx[1]
    unless defn.isOfKind ``Lean.Parser.Command.definition do
      throwErrorAt defn "tunable: only `def` is supported"
    let declId := defn[1]
    let declName := declId[0].getId
    let optDeclSig := defn[2]
    let declVal := defn[3]
    unless declVal.isOfKind ``Lean.Parser.Command.declValSimple do
      throwErrorAt declVal "tunable: only `def … := …` (simple definition value) is supported"
    let body := declVal[1]
    -- the declared return type — needed to pin `G` in `tuned_defaults`
    let typeSpec := optDeclSig[1]
    unless typeSpec.getNumArgs == 1 do
      throwErrorAt defn "tunable: the definition needs an explicit return type"
    let retType : Term := ⟨typeSpec[0][1]⟩
    -- binders: bracketed only, so they can be spliced into the theorem
    let binders := optDeclSig[0].getArgs
    for b in binders do
      if b.isIdent then
        throwErrorAt b "tunable: binders must be bracketed, e.g. `(x : T)`"
    let explicitIds := explicitBinderIds binders
    let hasDepth := explicitIds.any (·.getId == `depth)
    let isPartialFixpoint := Option.isSome <|
      declVal[2].find? (·.isOfKind ``Lean.Parser.Termination.partialFixpoint)
    if countRecCalls declName body > 0 && !isPartialFixpoint then
      throwErrorAt defn "tunable: a recursive generator must use `partial_fixpoint` — with structural or well-founded recursion, `{declName}.tuned {declName}.defaults` would not be definitionally equal to `{declName}`, so `{declName}.tuned_defaults` cannot be proved by `rfl`"
    -- 1. the original definition, exactly as written (minus site annotations);
    --    a doc comment written before `tunable` attaches to it
    let originalDefn := defn.setArg 3 (declVal.setArg 1 (stripSiteArgs body))
    let originalDecl := declStx.setArg 1 originalDefn
    let originalDecl :=
      if let some doc := doc? then
        originalDecl.setArg 0 (declStx[0].setArg 0 (mkNullNode #[doc]))
      else originalDecl
    elabCommand originalDecl
    -- 2. traverse the body: collect the sites and produce the tuned body, which reads its weights
    --    from `θ.toTuning` (`θ` is the weights record emitted in step 3, threaded through recursion)
    let θ : Ident := mkIdent (Name.mkSimple "θ")
    let dTerm : Term ← if hasDepth then `($(mkIdent `depth)) else `(0)
    let tunedName := declName ++ `tuned
    let tunedId := mkIdent tunedName
    let weightsName := declName ++ `Weights
    let weightsId := mkIdent weightsName
    let toTuningName := weightsName ++ `toTuning
    -- weight reads and positivity proofs see the flat `Tuning`, via `θ.toTuning`
    let θT : Term ← `($(mkIdent toTuningName) $θ)
    let recRepl ← `(($tunedId $θ))
    let (tunedBody, st) ← liftTermElabM <|
      (rewriteFrequencies declName θT dTerm body).run {}
    if st.sites.isEmpty then
      throwErrorAt declStx "tunable: no `frequency` site found in the body — nothing to tune"
    let tunedBody := rewriteRecCalls declName tunedId θ recRepl.raw tunedBody
    -- 3. the weights record: one field per branch (in the flat schedule order), named after the
    --    constructor the branch produces (inferred by `branchResultName?`), defaulting to the
    --    source weight. This is what lets a user write `genFoo.tuned { leaf := …, node := … }`
    --    instead of a positional `Tuning`. Ambiguous or unreadable branches fall back to a
    --    positional field name (`field<i>`); a repeated constructor name is suffixed (`leaf_1`).
    let flatFields := st.sites.flatMap (·.fields)
    let flatDefaults := st.sites.flatMap (·.defaults)
    let mut usedNames : Array String := #[]
    let mut fieldIds : Array Ident := #[]
    for i in [0:flatFields.size] do
      let base : String := match flatFields[i]! with
        | some n => n.toString
        | none => s!"field{i}"
      let mut nm := base
      let mut k := 1
      while usedNames.contains nm do
        nm := s!"{base}_{k}"; k := k + 1
      usedNames := usedNames.push nm
      fieldIds := fieldIds.push (mkIdent (Name.mkSimple nm))
    let fieldDefaults : Array Term ← flatDefaults.mapM fun (a, b) => `(($(quote a), $(quote b)))
    elabCommand (← `(/-- Per-constructor weights for `$(mkIdent declName)`, one field per
      `frequency` branch named after the constructor it produces. Each field defaults to the
      source weight, so `{}` reproduces `$(mkIdent declName)`. Passed to `$tunedId`. -/
      structure $weightsId where
        $[$fieldIds:ident : Nat × Nat := $fieldDefaults]*
        deriving Repr, DecidableEq, Inhabited))
    let wId := mkIdent (Name.mkSimple "w")
    let accesses : Array Term ← fieldIds.mapM fun f => `($wId.$f:ident)
    elabCommand (← `(/-- The flat `Tuning` this weights record denotes: its fields in branch order. -/
      def $(mkIdent toTuningName) ($wId : $weightsId) : Tuning := ⟨#[$accesses,*]⟩))
    -- a `Tuning` still coerces in, so weightings held as `Tuning` values keep working with `.tuned`;
    -- fields past the array's end fall back to the source default (never the `getD` fallback)
    let tId := mkIdent (Name.mkSimple "t")
    let coeArgs : Array Term ← (flatDefaults.zipIdx).mapM fun ((a, b), i) =>
      `(($tId).schedules.getD $(quote i) ($(quote a), $(quote b)))
    elabCommand (← `(instance : Coe Tuning $weightsId := ⟨fun $tId => ⟨$coeArgs,*⟩⟩))
    -- 4. the tuned definition, taking the weights record
    let θBinder ← `(Lean.Parser.Term.bracketedBinderF| ($θ:ident : $weightsId))
    let tunedSig := optDeclSig.setArg 0
      (.node (optDeclSig[0].getHeadInfo) nullKind (#[θBinder.raw] ++ binders))
    let tunedDeclId := declId.setArg 0 (mkIdent tunedName)
    let tunedDefn := ((defn.setArg 1 tunedDeclId).setArg 2 tunedSig).setArg 3
      (declVal.setArg 1 tunedBody)
    elabCommand (declStx.setArg 1 tunedDefn)
    -- 5. defaults (the record with every field at its source weight) and site table
    let defaultsName := declName ++ `defaults
    let sitesName := declName ++ `sites
    let siteTerms : Array Term ← st.sites.mapM fun s => do
      let holeLits : Array Term := s.holes.map fun h => quote h
      `((⟨$(quote s.name), $(quote s.offset), $(quote s.arity), #[$holeLits,*]⟩ : Site))
    elabCommand (← `(def $(mkIdent defaultsName):ident : $weightsId := {}))
    elabCommand (← `(def $(mkIdent sitesName):ident : Array Site := #[$siteTerms,*]))
    -- 6. tuned_defaults: definitional, but `partial_fixpoint` marks both
    --    definitions `@[irreducible]`, so `rfl` needs full transparency
    let thmName := declName ++ `tuned_defaults
    let bs : TSyntaxArray ``Lean.Parser.Term.bracketedBinder := binders.map (⟨·⟩)
    let lhsApp := Syntax.mkApp (← `($tunedId $(mkIdent defaultsName)))
      (explicitIds.map (⟨·.raw⟩))
    let lhs ← `(($lhsApp : $retType))
    let rhs := Syntax.mkApp (← `($(mkIdent declName))) (explicitIds.map (⟨·.raw⟩))
    elabCommand (← `(theorem $(mkIdent thmName):ident $bs:bracketedBinder* : $lhs = $rhs := by
      with_unfolding_all rfl))

end Basalt.Tuning.Macro
