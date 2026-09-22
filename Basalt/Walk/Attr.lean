/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Lean.Meta.Basic
import Lean.Meta.Tactic.Simp.Attr

/-!
# The Walker's Judgments and Registries

The judgments the generator walker (`Basalt/Walk/Basic.lean`) proves, and its registries: the
`@[gen_rule]` rules, keyed by judgment and by the head constant of what the rule is about; the
`@[gen_map]` lemmas, keyed by combinator; the `@[obs_leaf]` lemmas, keyed by observation; the
`@[spec_apply]` simp set; and the `@[gen_branches]` relations. Each attribute reads its key off the
statement it tags, and fails on one it cannot.
-/
open Lean Meta

namespace Basalt.Walk

/-- The naming convention for a generator's laws: `<gen>.<suffix>` states `<law> (gen …) …`, in the
order a leaf tries them. `#genstats` reports on the laws under it, and the walker closes a leaf with
a callee's law under it. The laws are named by quoted name, so that this module imports none of
them; `BasaltTest/LawLine.lean` checks that each resolves. -/
def lawConventions : Array (Name × Name) := #[
  (`sound_complete, `IsSoundAndComplete), (`sound, `IsSound), (`complete, `IsCompleteFor),
  (`terminates, `IsAlmostSurelyTerminating), (`cost_bounded, `IsCostBounded),
  (`filter_free, `IsFilterFree), (`productive, `IsProductive)]

/-- A statement about one generator that the walker proves by structural recursion on it.

The table names its constants by quoted name rather than by resolved name so that this module
imports nothing a judgment is defined in; `BasaltTest/Obs.lean` checks that each resolves. -/
structure Judgment where
  /-- The registry key, conventionally the constant the judgment is stated with. -/
  key : Name
  /-- On a statement already in `whnfR`: the generator it is about, and how to restate it about a
  generator that is definitionally equal. -/
  subject? : Expr → MetaM (Option (Expr × (Expr → Expr)))
  /-- How a fact closes a leaf: `none` uses the fact itself, which must then close the goal; `some b`
  passes it as the first explicit argument of `b`, whose remaining premises are walked. -/
  bridges : Array (Option Name)
  /-- For a judgment stated on an observation, which side of the `≤` the observation is on (the
  argument index); its leaves are then the observation's `@[obs_leaf]` lemmas (`Judgment.leaves`). -/
  specSide : Option Nat := none
  /-- The error for a leaf nothing closes. -/
  noLeaf : Expr → MessageData
  /-- Whether a fact about a generator is tried before its combinator's rules. -/
  leavesFirst : Bool := false
  /-- For a judgment stated on an observation: the lemmas, one per family of specification monad,
  that turn a goal about a combinator into one about the right-hand side of the combinator's
  `@[gen_map]` lemma. The explicit premises of each are that equation, then the new goal. -/
  adapters : Array Name := #[]
  /-- A lemma that restates a goal of this judgment, about any generator, as goals of other
  judgments; tried before the rules when it is in scope. -/
  reduceTo : Option Name := none
  /-- The registry key of the rules about the subject `g`. Tagging a rule and looking one up both
  go through this. -/
  ruleHead? : Expr → MetaM (Option Name) := fun g => pure g.getAppFn.constName?

/-- `IsBounded g c` with `c` to be found: a combinator's generator argument, whose cost bound the
combinator's rule is stated in terms of. A fact supplies it; failing one, a combinator term's rules
compute its worst case, a `c` that ignores the value. -/
def isBoundedJudgment : Judgment where
  key := `IsBounded
  subject? ty := do
    unless ty.isAppOfArity `IsBounded 3 do return none
    return some (ty.getArg! 1, fun g => mkApp3 ty.getAppFn (ty.getArg! 0) g (ty.getArg! 2))
  bridges := #[none, some `IsCostBounded.isBounded]
  noLeaf g := m!"cost_bound: no hypothesis or `.cost_bounded` law bounds the cost of the \
    combinator argument{indentExpr g}\nPass a cost bound for it to `cost_bound [_]`."
  leavesFirst := true
  reduceTo := some `SPMF.Cost.isBounded_of_worst

/-- `law g R` with `R` to be found, for `law` one half of the support law: a list combinator's
generator argument, whose support the list's postcondition does not mention. Only a leaf closes
it. -/
private def supportJudgment (law : Name) (bridge tactic : Name) : Judgment where
  key := law
  subject? ty := do
    unless ty.isAppOfArity law 3 do return none
    return some (ty.getArg! 1, fun g => mkApp3 ty.getAppFn (ty.getArg! 0) g (ty.getArg! 2))
  bridges := #[none, some bridge]
  noLeaf g := m!"{tactic}: no hypothesis or law gives `{law} _ _` of the combinator argument\
    {indentExpr g}\nProve one and pass it to `{tactic} [_]`."
  leavesFirst := true

@[inherit_doc supportJudgment]
def isSoundJudgment : Judgment :=
  supportJudgment `IsSound `IsSoundAndComplete.sound `sound_bound

@[inherit_doc supportJudgment]
def isCompleteForJudgment : Judgment :=
  supportJudgment `IsCompleteFor `IsSoundAndComplete.complete `complete_bound

/-- The generator of `O.spec g post`, and how to restate it about another. -/
private def specSubject? (e : Expr) : Option (Expr × (Expr → Expr)) :=
  let e := e.headBeta
  if e.isAppOfArity `Obs.spec 10 then
    some (e.getArg! 8, fun g => mkAppN e.getAppFn (e.getAppArgs.set! 8 g))
  else none

/-- The observation a bound `O.spec g post ≤ b` (`upper`) or `b ≤ O.spec g post` is about. -/
private def specObs? (ty : Expr) : Option (Name × Bool) := do
  guard (ty.isAppOfArity ``LE.le 4)
  let (spec, upper) ← if (specSubject? (ty.getArg! 2)).isSome then some (ty.getArg! 2, true)
    else if (specSubject? (ty.getArg! 3)).isSome then some (ty.getArg! 3, false) else none
  let obs ← (spec.headBeta.getArg! 6).getAppFn.constName?
  return (obs, upper)

/-- `O.spec g post ≤ b` (`side := 2`) or `b ≤ O.spec g post` (`side := 3`): a bound on an
observation into an ordered algebra, computed by the rules from the postcondition. The rules are
stated once for every monotone observation. -/
private def specJudgment (side : Nat) (key : Name) (adapters : Array Name) : Judgment where
  key := key
  subject? ty := do
    unless ty.isAppOfArity ``LE.le 4 do return none
    let some (g, restate) := specSubject? (ty.getArg! side) | return none
    return some (g, fun g => mkAppN ty.getAppFn (ty.getAppArgs.set! side (restate g)))
  bridges := #[none]
  noLeaf g := m!"no rule, `@[gen_map]` lemma, hypothesis, or law bounds{indentExpr g}\n\
    Pass a fact about it to the tactic."
  adapters := adapters
  specSide := some side

@[inherit_doc specJudgment]
def specLEJudgment : Judgment :=
  specJudgment 2 `Obs.spec #[`Obs.spec_le_of_map, `Obs.specC_le_of_map]

@[inherit_doc specJudgment]
def specGEJudgment : Judgment :=
  specJudgment 3 (`Obs.spec ++ `ge) #[`Obs.le_spec_of_map, `Obs.le_specC_of_map]

/-- The shapes of choice an algebra has rules for. -/
def mixShapes : Array Name :=
  #[`Mix.range, `Mix.threshold, `Mix.index, `Mix.element, `Mix.select, `Mix.rangeInt]

private def firstExplicit : Expr → Nat → Option Nat
  | .forallE _ _ b bi, i => if bi.isExplicit then some i else firstExplicit b (i + 1)
  | _, _ => none

/-- The key of a shape's rules: the shape, then its algebra, which is its first explicit argument.
Keyed by shape alone, a goal in one algebra tries another's rules first, and when every rule fails
the error is a unification failure against a lemma about the wrong carrier. -/
def shapeRuleHead? (shape : Expr) : MetaM (Option Name) := do
  let some head := shape.getAppFn.constName? | return none
  let some i := firstExplicit (← getConstInfo head).type 0 | return none
  let some algebra := (shape.getAppArgs[i]?).bind (·.getAppFn.constName?) | return none
  return some (head ++ algebra)

/-- `‹shape› ≤ b` (`side := 2`) or `b ≤ ‹shape›` (`side := 3`): a bound on a choice in an ordered
algebra, from bounds on what its outcomes mean. The "generator" is the shape, so a rule is keyed by
it. -/
private def mixJudgment (side : Nat) (key : Name) : Judgment where
  key := key
  subject? ty := do
    unless ty.isAppOfArity ``LE.le 4 do return none
    let shape := ty.getArg! side
    unless mixShapes.any shape.isAppOf do return none
    return some (shape, fun g => mkAppN ty.getAppFn (ty.getAppArgs.set! side g))
  bridges := #[]
  noLeaf g := m!"no rule bounds the choice{indentExpr g}"
  ruleHead? := shapeRuleHead?

@[inherit_doc mixJudgment]
def mixLEJudgment : Judgment := mixJudgment 2 `Mix.mix

@[inherit_doc mixJudgment]
def mixGEJudgment : Judgment := mixJudgment 3 (`Mix.mix ++ `ge)

/-- Every judgment the walker knows, tried in order. -/
def judgments : Array Judgment :=
  #[isBoundedJudgment, isSoundJudgment, isCompleteForJudgment, specLEJudgment, mixLEJudgment,
    specGEJudgment, mixGEJudgment]

/-! ## Leaves of a bound on an observation -/

/-- Observation ↦ its `@[obs_leaf]` lemmas, in declaration order: whether each bounds it from above,
whether it is a bound by itself (`self`), and its name. -/
initialize obsLeafExt :
    SimplePersistentEnvExtension (Name × Bool × Bool × Name) (NameMap (Array (Bool × Bool × Name))) ←
  let add (m : NameMap (Array (Bool × Bool × Name))) : Name × Bool × Bool × Name → _
    | (o, e) => m.insert o (((m.find? o).getD #[]).push e)
  registerSimplePersistentEnvExtension {
    addEntryFn := add
    addImportedFn := fun ess => ess.foldl (fun m es => es.foldl add m) {}
  }

/-- What closes a leaf of a bound on one observation, besides a fact that is the bound itself. -/
structure Leaves where
  /-- Bridges from a fact whose postcondition differs from the goal's by a constant: each takes the
  fact, then equations `∀ a, p a = k + h a` that the walker solves for `k`. -/
  facts : Array Name := #[]
  /-- Bounds on the subject by itself, tried in order for a leaf nothing else closes, in place of
  the judgment's `noLeaf`. -/
  self : Array Name := #[]
  /-- Whether `self` stands in for a rule per combinator — an upper bound's does, since a list
  combinator has no shape of choice for the walk to enter — and so applies only to a generator the
  walker knows as one. A generator nothing is known about is then still an error. A lower bound's
  keeps a recursive occurrence or an unknown callee in the bound as itself. -/
  selfOnlyCombinators : Bool := false

/-- The leaves of the goal `ty`, a statement of judgment `j`: its observation's, if it has one. -/
def Judgment.leaves (j : Judgment) (ty : Expr) : CoreM Leaves := do
  if j.specSide.isNone then return {}
  let some (obs, upper) := specObs? ty | return {}
  let all := ((obsLeafExt.getState (← getEnv)).find? obs).getD #[]
  let of (self : Bool) := all.filterMap fun (u, s, n) => if u == upper && s == self then n else none
  return { facts := of false, self := of true, selfOnlyCombinators := upper }

/-- `@[obs_leaf]` — a bridge from a fact about a generator to a bound on an observation of it, which
the walker tries at a leaf of that bound: its first explicit argument is the fact, and the rest are
equations `∀ a, p a = k + h a` for the walker to solve. `@[obs_leaf self]` — a bound on an
observation of any generator by itself, the walker's last resort. The observation and the direction
are read off the conclusion; lemmas for one pair are tried in declaration order. -/
syntax (name := obsLeafAttr) "obs_leaf" (&" self")? : attr

initialize registerBuiltinAttribute {
  name := `obsLeafAttr
  descr := "a leaf of the generator walker's bound on an observation"
  add := fun declName stx kind => do
    unless kind == .global do throwError "obs_leaf: must be a global attribute"
    let some (obs, upper) ← MetaM.run' <| forallTelescope (← getConstInfo declName).type
        fun _ concl => return specObs? (← whnfR concl)
      | throwError "obs_leaf: `{declName}` must conclude `O.spec g p ≤ b` or `b ≤ O.spec g p` for \
          an observation `O` that is a constant"
    modifyEnv (obsLeafExt.addEntry · (obs, upper, !stx[1].isNone, declName))
}

/-- `@[spec_apply]` — how a specification built from a shape of choice applies to a postcondition.
The walker rewrites with these after a `@[gen_map]` lemma, to reach the algebra's own shapes. -/
initialize specApplyExt : SimpExtension ←
  registerSimpAttr `spec_apply "a specification applied to a postcondition"

/-- Judgment key ↦ combinator head constant ↦ the `@[gen_rule]` rules for it, in declaration
order. -/
initialize genRuleExt :
    SimplePersistentEnvExtension (Name × Name × Name) (NameMap (NameMap (Array Name))) ←
  let add (m : NameMap (NameMap (Array Name))) : Name × Name × Name → NameMap (NameMap (Array Name))
    | (j, k, v) =>
      let byHead := (m.find? j).getD {}
      m.insert j (byHead.insert k (((byHead.find? k).getD #[]).push v))
  registerSimplePersistentEnvExtension {
    addEntryFn := add
    addImportedFn := fun ess => ess.foldl (fun m es => es.foldl add m) {}
  }

/-- The rules for judgment `j` about generators headed by `head`. -/
def rulesFor (env : Environment) (j head : Name) : Option (Array Name) :=
  ((genRuleExt.getState env).find? j).bind (·.find? head)

/-- Combinator head constant ↦ its `@[gen_map]` lemma. -/
initialize genMapExt : SimplePersistentEnvExtension (Name × Name) (NameMap Name) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun m (k, v) => m.insert k v
    addImportedFn := fun ess => ess.foldl (fun m es => es.foldl (fun m (k, v) => m.insert k v) m) {}
  }

/-- The `@[gen_map]` lemma for generators headed by `head`. -/
def mapFor (env : Environment) (head : Name) : Option Name :=
  (genMapExt.getState env).find? head

/-- Whether `head` is a combinator: some judgment has a rule for it, or it has a `@[gen_map]`
lemma. -/
def isCombinator (env : Environment) (head : Name) : Bool :=
  ((genRuleExt.getState env).any fun _ byHead => byHead.contains head)
    || (genMapExt.getState env).contains head

/-- The judgment a rule concludes and the combinator it is about. -/
def ruleKey (declName : Name) (type : Expr) : MetaM (Name × Name) :=
  forallTelescope type fun _ concl => do
    let concl ← whnfR concl
    for j in judgments do
      if let some (g, _) ← j.subject? concl then
        if let some head ← j.ruleHead? g then
          return (j.key, head)
    throwError "gen_rule: `{declName}` must conclude a judgment about a combinator application \
      (one of {judgments.map (·.key)}), not{indentExpr concl}"

/-- The relations a rule premise may use to collect a list combinator's branches. -/
initialize genBranchesExt : SimplePersistentEnvExtension Name NameSet ←
  registerSimplePersistentEnvExtension {
    addEntryFn := NameSet.insert
    addImportedFn := fun ess => ess.foldl (fun s es => es.foldl NameSet.insert s) {}
  }

/-- Whether `head` is a relation tagged `@[gen_branches]`. -/
def isBranchList (env : Environment) (head : Name) : Bool :=
  (genBranchesExt.getState env).contains head

/-- `@[gen_branches]` — let the generator walker build a proof of this relation one branch at a
time, with its `nil` and `cons` constructors, choosing between them by whether the relation's last
argument is `[]`. -/
syntax (name := genBranchesAttr) "gen_branches" : attr

initialize registerBuiltinAttribute {
  name := `genBranchesAttr
  descr := "a relation over a list combinator's branches, built by the generator walker"
  add := fun declName _ kind => do
    unless kind == .global do throwError "gen_branches: must be a global attribute"
    unless (← getEnv).contains (declName ++ `nil) && (← getEnv).contains (declName ++ `cons) do
      throwError "gen_branches: `{declName}` must have constructors `nil` and `cons`"
    modifyEnv (genBranchesExt.addEntry · declName)
}

/-- `@[gen_rule]` — teach the generator walker one combinator's rule for one judgment. Later rules
for the same pair are fallbacks. -/
syntax (name := genRuleAttr) "gen_rule" : attr

initialize registerBuiltinAttribute {
  name := `genRuleAttr
  descr := "a rule for one generator combinator, used by the generator walker"
  add := fun declName _ kind => do
    unless kind == .global do throwError "gen_rule: must be a global attribute"
    let (j, head) ← MetaM.run' (ruleKey declName (← getConstInfo declName).type)
    modifyEnv (genRuleExt.addEntry · (j, head, declName))
}

/-- `@[gen_map]` — a combinator's one lemma, `O.spec (<combinator> …) = …` for every observation
`O`, from which the walker proves any judgment stated on an observation. -/
syntax (name := genMapAttr) "gen_map" : attr

initialize registerBuiltinAttribute {
  name := `genMapAttr
  descr := "the lemma saying that every observation commutes with a generator combinator"
  add := fun declName _ kind => do
    unless kind == .global do throwError "gen_map: must be a global attribute"
    let head ← MetaM.run' <| forallTelescope (← getConstInfo declName).type fun _ concl => do
      let some (_, lhs, _) := concl.eq? | throwError "gen_map: `{declName}` must conclude an equation"
      unless lhs.isAppOfArity `Obs.spec 9 do
        throwError "gen_map: the left-hand side of `{declName}` must be `O.spec (<combinator> …)`"
      let some head := lhs.appArg!.getAppFn.constName?
        | throwError "gen_map: `{declName}` must be about a combinator application"
      return head
    modifyEnv (genMapExt.addEntry · (head, declName))
}

end Basalt.Walk
