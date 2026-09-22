/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Lean.Meta.Basic
import Lean.Meta.Tactic.Simp.Attr

/-!
# The Walker's Judgments and Registries

The judgments the generator walker (`Basalt/Walk/Basic.lean`) proves and the leaves each observation
closes them with; the registry of `@[gen_rule]` rules, keyed by judgment and by the head constant of
what the rule is about; the registry of `@[gen_map]` lemmas, keyed by combinator; the `@[spec_apply]`
simp set; and the `@[gen_branches]` relations a rule collects a list combinator's branches with. A
rule must conclude a statement one of the `judgments` recognizes; that is what makes both keys
readable off it.
-/

open Lean Meta

namespace Basalt.Walk

/-- A statement about one generator that the walker proves by structural recursion on it.

The table names its constants by quoted name rather than by resolved name so that this module
imports nothing a judgment is defined in; a misspelled constant recognizes no rule, and tagging one
then fails. -/
structure Judgment where
  /-- The registry key, conventionally the constant the judgment is stated with. -/
  key : Name
  /-- On a statement already in `whnfR`: the generator it is about, and how to restate it about a
  generator that is definitionally equal. -/
  subject? : Expr → MetaM (Option (Expr × (Expr → Expr)))
  /-- How a fact closes a leaf: `none` uses the fact itself, which must then close the goal; `some b`
  passes it as the first explicit argument of `b`, whose remaining premises are walked. -/
  bridges : Array (Option Name)
  /-- A callee's law for this judgment is `<callee>.<suffix>`, for the first of these that exists
  and closes the leaf. -/
  laws : Array Name := #[]
  /-- For a judgment stated on an observation, which side of the `≤` the observation is on (the
  argument index); its leaves are then the observation's (`Judgment.at`). -/
  specSide : Option Nat := none
  /-- The error for a leaf nothing closes. -/
  noLeaf : Expr → MessageData
  /-- Whether a fact about a generator is tried before its combinator's rules. -/
  leavesFirst : Bool := false
  /-- For a judgment stated on an observation: the lemmas, one per family of specification monad,
  that turn a goal about a combinator into one about the right-hand side of the combinator's
  `@[gen_map]` lemma. The explicit premises of each are that equation, then the new goal. -/
  adapters : Array Name := #[]
  /-- Bridges for a fact whose postcondition differs from the goal's by a constant: each takes the
  fact, then equations `∀ a, p a = k + h a` that the walker solves for `k`. -/
  affine : Array Name := #[]
  /-- A lemma that restates a goal of this judgment, about any generator, as goals of other
  judgments; tried before the rules when it is in scope. -/
  reduceTo : Option Name := none
  /-- Bounds on the subject by itself, tried in order for a leaf nothing else closes, in place of
  `noLeaf`. -/
  selfLeaf : Array Name := #[]
  /-- Whether `selfLeaf` stands in for a rule per combinator, and so applies only to a generator
  the walker knows as one. A generator nothing is known about is then still `noLeaf`'s error. -/
  selfLeafIsRule : Bool := false
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
  laws := #[`cost_bounded]
  noLeaf g := m!"cost_bound: no hypothesis or `.cost_bounded` law bounds the cost of the \
    combinator argument{indentExpr g}\nPass a cost bound for it to `cost_bound [_]`."
  leavesFirst := true
  reduceTo := some `SPMF.Cost.isBounded_of_worst

/-- `law g R` with `R` to be found, for `law` one half of the support law: a list combinator's
generator argument, whose support the list's postcondition does not mention. Only a leaf closes
it. -/
private def supportJudgment (law : Name) (bridge tactic : Name) (laws : Array Name) : Judgment where
  key := law
  subject? ty := do
    unless ty.isAppOfArity law 3 do return none
    return some (ty.getArg! 1, fun g => mkApp3 ty.getAppFn (ty.getArg! 0) g (ty.getArg! 2))
  bridges := #[none, some bridge]
  laws := laws
  noLeaf g := m!"{tactic}: no hypothesis or law gives `{law} _ _` of the combinator argument\
    {indentExpr g}\nProve one and pass it to `{tactic} [_]`."
  leavesFirst := true

@[inherit_doc supportJudgment]
def isSoundJudgment : Judgment :=
  supportJudgment `IsSound `IsSoundAndComplete.sound `sound_bound #[`sound_complete, `sound]

@[inherit_doc supportJudgment]
def isCompleteForJudgment : Judgment :=
  supportJudgment `IsCompleteFor `IsSoundAndComplete.complete `complete_bound
    #[`sound_complete, `complete]

/-- What a leaf of a judgment about one observation is closed with. The rules are shared by every
observation of a direction; the laws and bridges are not. -/
structure Observation where
  /-- The `Obs` constant. -/
  obs : Name
  /-- The affine bridges for an upper bound, and the suffixes of a callee's laws for one. -/
  upper : Array Name := #[]
  upperLaw : Array Name := #[]
  /-- The same for a lower bound. -/
  lower : Array Name := #[]
  lowerLaw : Array Name := #[]
  /-- Lower bounds on the observation of any generator, tried in order: a recursive occurrence or
  an unknown callee then stays in the bound, as an exact one, where another observation fails. -/
  lowerSelf : Array Name := #[]
  /-- The same for an upper bound, where what a generator gives is what the missing mass allows.
  These stand in for a rule per combinator — a list combinator has no shape of choice for the walk
  to enter — so they apply only to a combinator, and a generator nothing is known about is still an
  error. -/
  upperSelf : Array Name := #[]

/-- The observations the walker has leaves for. -/
def observations : Array Observation := #[
  { obs := `SPMF.expectObs
    upper := #[`SPMF.spec_le_add_of_expect_le]
    upperSelf := #[`SPMF.spec_le_of_const, `SPMF.spec_le_iSup]
    lower := #[`SPMF.le_spec_one_of_le_mass, `SPMF.le_spec_of_le_mass, `SPMF.le_spec_of_isPMF, `SPMF.le_spec_iInf_of_le_mass,
      `SPMF.le_spec_iInf_of_isPMF]
    lowerLaw := #[`terminates] },
  { obs := `SPMF.Cost.expectObs
    upper := #[`SPMF.Cost.spec_le_add_of_expect_le]
    upperSelf := #[`SPMF.Cost.specC_le_of_const, `SPMF.Cost.specC_le_iSup] },
  { obs := `SPMF.Cost.alwaysObs
    lower := #[`SPMF.Cost.le_spec_of_always, `SPMF.Cost.le_spec_of_isBounded,
      `SPMF.Cost.le_spec_of_isCostBounded]
    lowerLaw := #[`cost_bounded] },
  { obs := `SPMF.Cost.worstObs
    upper := #[`SPMF.Cost.worst_le_add_of_le, `SPMF.Cost.worst_le_add_of_isBounded]
    upperLaw := #[`cost_bounded] },
  { obs := `SPMF.alwaysObs
    lower := #[`SPMF.le_always_of_isSound, `SPMF.le_always_of_isSoundAndComplete]
    lowerLaw := #[`sound_complete, `sound] },
  { obs := `SPMF.mayObs
    lower := #[`SPMF.le_may_of_isCompleteFor, `SPMF.le_may_of_isSoundAndComplete,
      `SPMF.le_may_of_measure]
    lowerLaw := #[`sound_complete, `complete]
    lowerSelf := #[`SPMF.le_may_self] },
  { obs := `SPMF.Cost.mayObs
    lowerSelf := #[`SPMF.Cost.le_may_self] }]

/-- `j` with the leaves of the observation that the goal `ty` is about. -/
def Judgment.at (j : Judgment) (ty : Expr) : Judgment := Id.run do
  let some side := j.specSide | return j
  let spec := (ty.getArg! side).headBeta
  let some o := observations.find? (spec.getArg! 6 |>.getAppFn.isConstOf ·.obs) | return j
  return if side == 2 then
      { j with laws := o.upperLaw, affine := o.upper, selfLeaf := o.upperSelf,
               selfLeafIsRule := true }
    else { j with laws := o.lowerLaw, affine := o.lower, selfLeaf := o.lowerSelf }

/-- The generator of `O.spec g post`, and how to restate it about another. -/
private def specSubject? (e : Expr) : Option (Expr × (Expr → Expr)) :=
  let e := e.headBeta
  if e.isAppOfArity `Obs.spec 10 then
    some (e.getArg! 8, fun g => mkAppN e.getAppFn (e.getAppArgs.set! 8 g))
  else none

/-- `O.spec g post ≤ b`: an upper bound on an observation into an ordered algebra, computed by the
rules from the postcondition. The rules are stated once for every monotone observation. -/
def specLEJudgment : Judgment where
  key := `Obs.spec
  subject? ty := do
    unless ty.isAppOfArity ``LE.le 4 do return none
    let some (g, restate) := specSubject? (ty.getArg! 2) | return none
    return some (g, fun g => mkApp2 ty.appFn!.appFn! (restate g) (ty.getArg! 3))
  bridges := #[none]
  noLeaf g := m!"no rule, `@[gen_map]` lemma, hypothesis, or law bounds{indentExpr g}\n\
    Pass a fact about it to the tactic."
  adapters := #[`Obs.spec_le_of_map, `Obs.specC_le_of_map]
  specSide := some 2

/-- `b ≤ O.spec g post`: the lower bound, as `specLEJudgment`. -/
def specGEJudgment : Judgment where
  key := `Obs.spec ++ `ge
  subject? ty := do
    unless ty.isAppOfArity ``LE.le 4 do return none
    let some (g, restate) := specSubject? (ty.getArg! 3) | return none
    return some (g, fun g => mkApp2 ty.appFn!.appFn! (ty.getArg! 2) (restate g))
  bridges := #[none]
  noLeaf g := m!"no rule, `@[gen_map]` lemma, hypothesis, or law bounds{indentExpr g}\n\
    Pass a fact about it to the tactic."
  adapters := #[`Obs.le_spec_of_map, `Obs.le_specC_of_map]
  specSide := some 3

/-- The shapes of choice an algebra has rules for. -/
def mixShapes : Array Name :=
  #[`Mix.range, `Mix.binary, `Mix.threshold, `Mix.index, `Mix.element, `Mix.select, `Mix.rangeInt]

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

/-- `‹shape› ≤ b`: an upper bound on a choice in an ordered algebra, from bounds on what its
outcomes mean. The "generator" is the shape, so a rule is keyed by it. -/
def mixLEJudgment : Judgment where
  key := `Mix.mix
  subject? ty := do
    unless ty.isAppOfArity ``LE.le 4 do return none
    let lhs := ty.getArg! 2
    unless mixShapes.any lhs.isAppOf do return none
    return some (lhs, fun g => mkApp2 ty.appFn!.appFn! g (ty.getArg! 3))
  bridges := #[]
  noLeaf g := m!"no rule bounds the choice{indentExpr g}"
  ruleHead? := shapeRuleHead?

/-- `b ≤ ‹shape›`: the lower bound, as `mixLEJudgment`. -/
def mixGEJudgment : Judgment where
  key := `Mix.mix ++ `ge
  subject? ty := do
    unless ty.isAppOfArity ``LE.le 4 do return none
    let rhs := ty.getArg! 3
    unless mixShapes.any rhs.isAppOf do return none
    return some (rhs, fun g => mkApp2 ty.appFn!.appFn! (ty.getArg! 2) g)
  bridges := #[]
  noLeaf g := m!"no rule bounds the choice{indentExpr g}"
  ruleHead? := shapeRuleHead?

/-- Every judgment the walker knows, tried in order. -/
def judgments : Array Judgment :=
  #[isBoundedJudgment, isSoundJudgment, isCompleteForJudgment, specLEJudgment, mixLEJudgment,
    specGEJudgment, mixGEJudgment]

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
