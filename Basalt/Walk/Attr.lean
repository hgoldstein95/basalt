/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Lean.Elab.InfoTree.Main
import Lean.Meta.Basic
import Lean.Meta.Tactic.Simp.Attr
import Basalt.Obs.Basic

/-!
# The Walker's Judgments and Registries

The judgments the generator walker (`Basalt/Walk/Basic.lean`) proves, and its registries: the
judgments a file registers (`@[walk_argument]`, `@[walk_rel]`), the shapes of choice
(`@[mix_shape]`), the `@[gen_rule]` rules, keyed by judgment and by the head constant of what the
rule is about; the `@[gen_map]` lemmas, keyed by combinator; the `@[obs_leaf]` lemmas, keyed by
observation; the `@[spec_apply]` simp set; and the `@[gen_branches]` relations. Each attribute
reads its key off the statement it tags, and fails on one it cannot.
-/
open Lean Meta

namespace Basalt.Walk

/-- The generator of `O.spec g post`, and how to restate it about another. -/
private def specSubject? (e : Expr) : Option (Expr × (Expr → Expr)) :=
  let e := e.headBeta
  if e.isAppOfArity ``Obs.spec 10 then
    some (e.getArg! 8, fun g => mkAppN e.getAppFn (e.getAppArgs.set! 8 g))
  else none

/-- The observation a bound `O.spec g post ≤ b` (`upper`) or `b ≤ O.spec g post` is about. -/
private def specObs? (ty : Expr) : Option (Name × Bool) := do
  guard (ty.isAppOfArity ``LE.le 4)
  let (spec, upper) ← if (specSubject? (ty.getArg! 2)).isSome then some (ty.getArg! 2, true)
    else if (specSubject? (ty.getArg! 3)).isSome then some (ty.getArg! 3, false) else none
  let obs ← (spec.headBeta.getArg! 6).getAppFn.constName?
  return (obs, upper)

/-! ## Shapes of choice -/

/-- The shapes of choice an algebra has rules for. -/
initialize mixShapeExt : SimplePersistentEnvExtension Name NameSet ←
  registerSimplePersistentEnvExtension {
    addEntryFn := NameSet.insert
    addImportedFn := fun ess => ess.foldl (fun s es => es.foldl NameSet.insert s) {}
  }

/-- Whether `e` is a shape of choice. -/
def isMixShape (env : Environment) (e : Expr) : Bool :=
  (e.getAppFn.constName?.map (mixShapeExt.getState env).contains).getD false

/-- `@[mix_shape]` — a shape a choice takes in an algebra, which the walker bounds by the shape's
`@[gen_rule]` rules for that algebra. -/
syntax (name := mixShapeAttr) "mix_shape" : attr

initialize registerBuiltinAttribute {
  name := `mixShapeAttr
  descr := "a shape of choice in an algebra, bounded by the generator walker"
  add := fun declName _ kind => do
    unless kind == .global do throwError "mix_shape: must be a global attribute"
    modifyEnv (mixShapeExt.addEntry · declName)
}

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

/-! ## Judgments -/

/-- A statement about a generator proved by induction. -/
inductive Judgment where
  /-- `law g R` with `R` to be found: a list combinator's generator argument, which the
  combinator's rule asks about. No rule concludes one: a fact closes it, and failing one `reduceTo`
  restates it. `tactic` is the entry tactic that takes the fact, for the error. -/
  | argument (law : Name) (reduceTo : Option Name) (tactic : String)
  /-- `O.spec g post ≤ b` (`upper`) or `b ≤ O.spec g post`: a bound on an observation into an
  ordered algebra, computed by the rules from the postcondition. The rules are stated once for
  every monotone observation; a combinator with none goes through its `@[gen_map]` lemma. -/
  | spec (upper : Bool)
  /-- `‹shape› ≤ b` (`upper`) or `b ≤ ‹shape›`: a bound on a choice in an ordered algebra, from
  bounds on what its outcomes mean. The "generator" is the shape, so a rule is keyed by it. -/
  | mix (upper : Bool)
  /-- `rel … y x`: one generator at two monads, related construct by construct, `y` the side the
  induction is on and the one a rule is keyed by. A combinator with no rule is unfolded on both
  sides, which stay in step because they are one term; a leaf is a hypothesis or a fact. -/
  | rel (rel : Name) (tactic : String)

namespace Judgment

/-- The argument of the `≤` the subject of a bound is. -/
private def side (upper : Bool) : Nat := if upper then 2 else 3

/-- The registry key, the constant the judgment is stated with. -/
def key : Judgment → Name
  | argument law .. => law
  | spec upper => if upper then ``Obs.spec else ``Obs.spec ++ `ge
  | mix upper => if upper then `mix else `mix ++ `ge
  | rel r .. => r

/-- On a statement already in `whnfR`: the subject it is about, and how to restate it about a
subject that is definitionally equal. -/
def subject? (env : Environment) (j : Judgment) (ty : Expr) : Option (Expr × (Expr → Expr)) :=
  match j with
  | argument law .. => do
    guard (ty.isAppOfArity law 3)
    return (ty.getArg! 1, fun g => mkApp3 ty.getAppFn (ty.getArg! 0) g (ty.getArg! 2))
  | spec upper => do
    guard (ty.isAppOfArity ``LE.le 4)
    let (g, restate) ← specSubject? (ty.getArg! (side upper))
    return (g, fun g => mkAppN ty.getAppFn (ty.getAppArgs.set! (side upper) (restate g)))
  | mix upper => do
    guard (ty.isAppOfArity ``LE.le 4)
    let shape := ty.getArg! (side upper)
    guard (isMixShape env shape)
    return (shape, fun g => mkAppN ty.getAppFn (ty.getAppArgs.set! (side upper) g))
  | rel r .. => do
    guard (ty.isAppOf r && 2 ≤ ty.getAppNumArgs)
    let i := ty.getAppNumArgs - 2
    return (ty.getArg! i, fun g => mkAppN ty.getAppFn (ty.getAppArgs.set! i g))

/-- The registry key of the rules about the subject `g`. Tagging a rule and looking one up both go
through this. -/
def ruleHead? : Judgment → Expr → MetaM (Option Name)
  | mix _, g => shapeRuleHead? g
  | _, g => pure g.getAppFn.constName?

/-- A lemma that restates a goal of this judgment, about any generator, as goals of other
judgments; tried after the facts. -/
def reduceTo : Judgment → Option Name
  | argument _ r _ => r
  | _ => none

/-- Whether a fact about a generator is tried before its combinator's rules: the caller of a rule
that asks about an argument usually has one. -/
def leavesFirst : Judgment → Bool
  | argument .. => true
  | _ => false

/-- The error for a leaf nothing closes. -/
def noLeaf (j : Judgment) (g : Expr) : MessageData :=
  match j with
  | argument law _ tactic => m!"{tactic}: no hypothesis or fact gives `{law} _ _` of the \
      combinator argument{indentExpr g}\nProve one and pass it to `{tactic} [_]`."
  | spec _ => m!"no rule, `@[gen_map]` lemma, hypothesis, or fact bounds{indentExpr g}\n\
      Pass a fact about it to the tactic."
  | mix _ => m!"no rule bounds the choice{indentExpr g}"
  | rel r tactic => m!"{tactic}: no rule, hypothesis, or fact relates{indentExpr g}\nto its \
      counterpart. Pass a fact about it to `{tactic} [_]`; a recursive combinator needs a `{r}` \
      rule of its own."

/-- Whether a combinator with no rule is unfolded rather than being an error. -/
def unfoldsCombinators : Judgment → Bool
  | rel .. => true
  | _ => false

end Judgment

/-- The judgments registered by `@[walk_argument]` and `@[walk_rel]`, in registration order. -/
initialize judgmentExt : SimplePersistentEnvExtension Judgment (Array Judgment) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun ess => ess.foldl (fun acc es => acc ++ es) #[]
  }

/-- Every judgment the walker knows, tried in order: the registered ones, then the bounds on an
observation and on a choice. -/
def judgments (env : Environment) : Array Judgment :=
  judgmentExt.getState env ++ #[.spec true, .mix true, .spec false, .mix false]

/-- `@[walk_argument "tac"]` on a law `law g R` — the walker's judgment for a list combinator's
generator argument, closed by a fact passed to the entry tactic `tac`. With a lemma,
`@[walk_argument "tac" lem]`, a goal no fact closes is restated by `lem`. -/
syntax (name := walkArgumentAttr) "walk_argument " str (ppSpace ident)? : attr

initialize registerBuiltinAttribute {
  name := `walkArgumentAttr
  descr := "a law the generator walker asks of a list combinator's generator argument"
  add := fun declName stx kind => do
    unless kind == .global do throwError "walk_argument: must be a global attribute"
    let tac := stx[1].isStrLit?.getD ""
    let reduceTo ← if stx[2].isNone then pure none
      else some <$> Elab.realizeGlobalConstNoOverloadWithInfo stx[2][0]
    modifyEnv (judgmentExt.addEntry · (.argument declName reduceTo tac))
}

/-- `@[walk_rel "tac"]` on a relation `rel … y x` between one generator at two monads — the
walker's judgment relating them construct by construct, proved by the entry tactic `tac`. -/
syntax (name := walkRelAttr) "walk_rel " str : attr

initialize registerBuiltinAttribute {
  name := `walkRelAttr
  descr := "a relation between one generator at two monads, proved by the generator walker"
  add := fun declName stx kind => do
    unless kind == .global do throwError "walk_rel: must be a global attribute"
    modifyEnv (judgmentExt.addEntry · (.rel declName (stx[1].isStrLit?.getD "")))
}

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
  let .spec upper := j | return {}
  let some (obs, _) := specObs? ty | return {}
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
    let js := judgments (← getEnv)
    for j in js do
      if let some (g, _) := j.subject? (← getEnv) concl then
        if let some head ← j.ruleHead? g then
          return (j.key, head)
    throwError "gen_rule: `{declName}` must conclude a judgment about a combinator application \
      (one of {js.map (·.key)}), not{indentExpr concl}"

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
      unless lhs.isAppOfArity ``Obs.spec 9 do
        throwError "gen_map: the left-hand side of `{declName}` must be `O.spec (<combinator> …)`"
      let some head := lhs.appArg!.getAppFn.constName?
        | throwError "gen_map: `{declName}` must be about a combinator application"
      return head
    modifyEnv (genMapExt.addEntry · (head, declName))
}

end Basalt.Walk
