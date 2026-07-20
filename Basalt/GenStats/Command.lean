/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Lean
import Basalt.GenStats
import Basalt.Laws

/-!
# The `#genstats` Command

`#genstats g` draws from the generator `g` many times and prints a summary of the results.

```
#genstats Tree.genBST 0 10
#genstats (draws := 2000) (seed := 7) Tree.genBST 0 10
#genstats (size := fun t => t.size) Tree.genBST 0 10
```

Options (all optional, in any order, before the generator term):
- `(draws := n)` — number of draws (default 1000)
- `(fuel := n)` — max `choose` calls per draw (default 10000); draws that exceed it are reported
  as `fuel-exhausted`, which is what keeps a divergent generator from hanging the elaborator
- `(seed := n)` — RNG seed (default 0, so output is deterministic and `#guard_msgs`-testable)
- `(size := f)` — size function `α → Nat` used for the size distribution

When no `size` is given and the output type is a plain (non-indexed) inductive, a structural size
is derived automatically: the number of constructors of the *same* type in the value, so payloads
do not distort it (`sizeOf (n : Nat)` is `n`-ish, which would make a BST's "size" track its node
*values*; the structural count does not). Fields of other types — including nested occurrences
like `List (Tree α)` — count 0. If the type is not a plain inductive, `SizeOf` is used when
available; otherwise the size section is omitted. The head-constructor histogram and the
`Repr`-based sections degrade gracefully in the same way.
-/

open Lean Elab Command Meta

namespace GenStats.Command

/-- One `(key := value)` option. The `atomic` lets a parenthesized generator term
    (e.g. `#genstats (g : StatGen Nat)`) fail this parser cleanly and parse as the term. -/
syntax genStatsArg := atomic("(" ident " := ") term ")"

/-- Draw from a generator and print distribution statistics. See the module docstring of
    `Basalt.GenStats.Command` for the options. -/
syntax (name := genStatsCmd) "#genstats " genStatsArg* term : command

private structure Opts where
  draws : Nat := 1000
  fuel : Nat := 10000
  seed : Nat := 0
  size? : Option Term := none

private def asNatLit (v : Term) : CommandElabM Nat := do
  match v.raw.isNatLit? with
  | some n => pure n
  | none => throwErrorAt v "expected a numeric literal"

private def parseOpts (args : Array (TSyntax ``genStatsArg)) : CommandElabM Opts := do
  let mut opts : Opts := {}
  for arg in args do
    match arg with
    | `(genStatsArg| ($k:ident := $v:term)) =>
      match k.getId with
      | `draws => opts := { opts with draws := (← asNatLit v) }
      | `fuel => opts := { opts with fuel := (← asNatLit v) }
      | `seed => opts := { opts with seed := (← asNatLit v) }
      | `size => opts := { opts with size? := some v }
      | k => throwErrorAt arg "unknown #genstats option '{k}' (expected draws, fuel, seed, or size)"
    | _ => throwUnsupportedSyntax
  return opts

/-- The shape of one constructor of the output type: its name, the inductive's parameter count,
    and, for each field, whether it is a recursive occurrence (its type is the output type). -/
private structure CtorShape where
  ctor : Name
  numParams : Nat
  recFields : Array Bool

/-- If `α` is an application of a plain (non-indexed) inductive to its parameters, return its
    constructor shapes; otherwise `none`. -/
private def getCtorShapes? (α : Expr) : MetaM (Option (Array CtorShape)) := do
  let αW ← whnfD α
  let fn := αW.getAppFn
  let .const indName lvls := fn | return none
  let some (.inductInfo iv) := (← getEnv).find? indName | return none
  if iv.numIndices != 0 then return none
  let params := αW.getAppArgs
  if params.size != iv.numParams then return none
  let mut shapes := #[]
  for c in iv.ctors do
    let some (.ctorInfo ci) := (← getEnv).find? c | return none
    -- Instantiate the constructor's type at the inductive's parameters, leaving the fields.
    let mut ty := ci.type.instantiateLevelParams ci.levelParams lvls
    for p in params do
      let .forallE _ _ body _ := ty | return none
      ty := body.instantiate1 p
    let recFields ← forallTelescope ty fun fields _ =>
      fields.mapM fun f => do isDefEq (← inferType f) αW
    shapes := shapes.push { ctor := c, numParams := iv.numParams, recFields }
  return some shapes

/-- A fresh, deterministic top-level name for a generated helper, unique per source position. -/
private def mkHelperIdent (base : String) : CommandElabM Ident := do
  let pos := ((← getRef).getPos?).getD 0
  pure (mkIdent (Name.mkSimple s!"_{base}_{pos.byteIdx}"))

/-- An identifier that always resolves to the global `n`. -/
private def rootIdent (n : Name) : Ident := mkIdent (`_root_ ++ n)

/-- Build the pattern `@C _ … _ f₁ … fₙ` for a constructor, with `_` for the inductive's
    parameters and the given field patterns. -/
private def mkCtorPattern (shape : CtorShape) (fields : Array Term) : CommandElabM Term := do
  let head ← `(@$(rootIdent shape.ctor):ident)
  let mut args : Array Term := #[]
  for _ in [0:shape.numParams] do
    args := args.push (← `(_))
  return ⟨Syntax.mkApp head (args ++ fields)⟩

/-- Emit `private partial def <fnId> : <α> → Nat` counting the constructors of type `α` in a
    value (recursive fields recurse, everything else counts 0). -/
private def emitSizeDef (fnId : Ident) (αStx : Term) (shapes : Array CtorShape) :
    CommandElabM Unit := do
  let mut alts : Array (TSyntax ``Lean.Parser.Term.matchAlt) := #[]
  for shape in shapes do
    let mut fields : Array Term := #[]
    let mut body : Term ← `((1 : Nat))
    for i in [0:shape.recFields.size] do
      if shape.recFields[i]! then
        let f := mkIdent (Name.mkSimple s!"a{i}")
        fields := fields.push f
        body ← `($body + $fnId $f)
      else
        fields := fields.push (← `(_))
    let pat ← mkCtorPattern shape fields
    alts := alts.push (← `(Lean.Parser.Term.matchAltExpr| | $pat => $body))
  elabCommand (← `(private partial def $fnId : $αStx → Nat :=
    fun x => match x with $alts:matchAlt*))

/-- Emit `private def <fnId> : <α> → String` returning the head constructor's short name. -/
private def emitCtorDef (fnId : Ident) (αStx : Term) (shapes : Array CtorShape) :
    CommandElabM Unit := do
  let mut alts : Array (TSyntax ``Lean.Parser.Term.matchAlt) := #[]
  for shape in shapes do
    let pat ← mkCtorPattern shape (← shape.recFields.mapM fun _ => `(_))
    let name := Syntax.mkStrLit (shape.ctor.componentsRev.headD shape.ctor).toString
    alts := alts.push (← `(Lean.Parser.Term.matchAltExpr| | $pat => $name))
  elabCommand (← `(private def $fnId : $αStx → String :=
    fun x => match x with $alts:matchAlt*))

private def mkOptArg : Option Term → CommandElabM Term
  | some f => `(some ($f))
  | none => `(none)

/-- The laws `#genstats` reports on, in report order: the conventional suffix and the constant its
statement must be headed by. Laws are found by **naming convention** — `genFoo.sound_complete` — and
there is no registry to fall out of sync with.

Only Basalt's own laws appear here. A downstream library that emits laws Basalt has no definition
for (Palamedes' `total`, which is `Type`-valued, or its `IsSomeSoundAndComplete` for a filtering
generator) is invisible to this report; that is the cost of not having a registry, and it is
preferred to a registry that can silently disagree with what was actually proved. -/
private def lawSlots : Array (Name × Name) := #[
  (`sound_complete, ``IsSoundAndComplete),
  (`terminates,     ``IsAlmostSurelyTerminating),
  (`cost_bounded,   ``IsCostBounded),
  (`filter_free,    ``IsFilterFree),
  (`productive,     ``IsProductive)]

/-- Does `declName.suffix` exist *and* actually state the law?

**The statement is checked, not just the name.** A `theorem genFoo.sound_complete` that happens to
say something else — or says it about a different generator — must not be reported as a proof, so
the conclusion has to be headed by the law's constant and to mention `declName`. Without this the
report would launder any conventionally-named theorem into a ✓. -/
private def lawProved (env : Environment) (declName : Name) (suffix lawC : Name) : MetaM Bool := do
  let some ci := env.find? (declName ++ suffix) | return false
  forallTelescope ci.type fun _ body => do
    unless body.isAppOf lawC do return false
    return body.getAppArgs.any fun a => (a.find? (fun x => x.isConstOf declName)).isSome

/-- Testable entry point for the shape check, since a report that silently drops a law looks exactly
like a generator that has none. See `BasaltTest/LawLine.lean`. -/
def lawProvedFor (env : Environment) (declName suffix : Name) : MetaM Bool := do
  match lawSlots.find? (·.1 == suffix) with
  | none => return false
  | some (s, lawC) => lawProved env declName s lawC

/-- The generator's own constant, if the term has one to speak of.

Tries the head first, then the head of each argument: `#genstats genFoo` has `genFoo` at the head,
while an adapted `#genstats (toStatGen genFoo)` has the adapter there and the generator one level
in. A candidate only counts if it carries at least one law, so an adapter that happens to have a
`.sound_complete` of its own cannot shadow the generator's. -/
private def genConstant? (e : Expr) : MetaM (Option Name) := do
  let env ← getEnv
  let hasLaw (n : Name) : MetaM Bool :=
    lawSlots.anyM fun (suffix, lawC) => lawProved env n suffix lawC
  let candidates := #[e.getAppFn] ++ e.getAppArgs.map (·.getAppFn)
  for c in candidates do
    if let some n := c.constName? then
      if ← hasLaw n then return some n
  return none

elab_rules : command
  | `(#genstats $args:genStatsArg* $g:term) => do
    let opts ← parseOpts args
    -- Phase 1: elaborate the generator speculatively to learn its output type and what the type
    -- supports. The result expression is discarded; the generated `#eval` re-elaborates `g`.
    let (αStx, hasRepr, hasSizeOf, shapes?, laws) ← liftTermElabM do
      let α ← mkFreshExprMVar (some (mkSort levelOne))
      let gE ← Term.elabTermEnsuringType g (mkApp (mkConst ``GenStats.StatGen) α)
      Term.synthesizeSyntheticMVarsNoPostponing
      let α ← instantiateMVars α
      if α.hasExprMVar then
        throwErrorAt g "#genstats: could not infer the generator's output type"
      let αStx ← PrettyPrinter.delab α
      let hasRepr := (← synthInstance? (← mkAppM ``Repr #[α])).isSome
      let hasSizeOf := (← synthInstance? (← mkAppM ``SizeOf #[α])).isSome
      let shapes? ← getCtorShapes? α
      -- Laws, by naming convention off the generator's own constant. A term with no constant, or
      -- one carrying no laws, yields `#[]` and the report omits the block entirely.
      let laws ← do
        match ← genConstant? (← instantiateMVars gE) with
        | none => pure #[]
        | some n =>
          lawSlots.mapM fun (suffix, lawC) =>
            return (suffix.toString, ← lawProved (← getEnv) n suffix lawC)
      pure (αStx, hasRepr, hasSizeOf, shapes?, laws)
    -- Phase 2: generate the helper functions the output type supports.
    let mut sizeArg? : Option Term := opts.size?
    let mut ctorArg? : Option Term := none
    if let some shapes := shapes? then
      if !shapes.isEmpty then
        if sizeArg?.isNone then
          let fnId ← mkHelperIdent "genStatsSize"
          emitSizeDef fnId αStx shapes
          sizeArg? := some fnId
        let fnId ← mkHelperIdent "genStatsCtor"
        emitCtorDef fnId αStx shapes
        ctorArg? := some fnId
    if sizeArg?.isNone && hasSizeOf then
      sizeArg? := some (← `(fun a => sizeOf a))
    let reprArg? : Option Term ← if hasRepr then pure (some (← `(GenStats.reprLine))) else pure none
    -- Phase 3: delegate the actual running and printing to `#eval`.
    let label :=
      let raw := match g.raw.getSubstring? (withLeading := false) (withTrailing := false) with
        | some ss => ss.toString
        | none => toString g.raw
      -- Collapse all whitespace runs to single spaces so multi-line terms label cleanly.
      let words := Id.run do
        let mut ws : Array String := #[]
        let mut cur := ""
        for c in raw.toList do
          if c.isWhitespace then
            if cur ≠ "" then
              ws := ws.push cur
              cur := ""
          else
            cur := cur.push c
        if cur ≠ "" then
          ws := ws.push cur
        return ws
      " ".intercalate words.toList
    let cfg ← `({ draws := $(quote opts.draws), fuel := $(quote opts.fuel),
                  seed := $(quote opts.seed) : GenStats.Config })
    let lawsArg ← do
      let entries ← laws.mapM fun (n, ok) => do
        let b ← if ok then `(true) else `(false)
        `(($(Syntax.mkStrLit n), $b))
      `(#[$entries,*])
    elabCommand (← `(#eval GenStats.report (($g) : GenStats.StatGen _) $(Syntax.mkStrLit label)
      $cfg (size? := $(← mkOptArg sizeArg?)) (repr? := $(← mkOptArg reprArg?))
      (ctor? := $(← mkOptArg ctorArg?)) (laws := $lawsArg)))

end GenStats.Command
