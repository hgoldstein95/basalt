/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Lean.Meta.Basic

/-!
# The `@[gen_rule]` Attribute

The judgments the generator walker (`Basalt/SPMF/Walk.lean`) proves, and the registry of their
per-combinator rules, keyed by judgment and by the combinator's head constant. A rule must conclude
a statement one of the `judgments` recognizes; that is what makes both keys readable off it.
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
  /-- A callee's law for this judgment is `<callee>.<lawSuffix>`. -/
  lawSuffix : Name
  /-- The error for a leaf nothing closes. -/
  noLeaf : Expr → MessageData

/-- `c ≤ SPMF.mass g`: a lower bound on the mass, computed by the rules. -/
def massJudgment : Judgment where
  key := `SPMF.mass
  subject? ty := do
    unless ty.isAppOfArity ``LE.le 4 do return none
    let rhs ← whnfR (ty.getArg! 3)
    unless rhs.isAppOfArity `SPMF.mass 2 do return none
    return some (rhs.getArg! 1, fun g => ty.appFn!.app (rhs.appFn!.app g))
  bridges := #[none, some `SPMF.le_mass_of_isPMF]
  lawSuffix := `terminates
  noLeaf g := m!"mass_bound: no rule, hypothesis, or `.terminates` law bounds the mass \
    of{indentExpr g}\nTag a lower bound for it `@[gen_rule]`, or pass one to `mass_bound [_]`."

/-- `SPMF.Cost.Always g Q`: every value `g` produces satisfies `Q` together with its cost. The
postcondition is given, and the rules push it into the sub-generators. -/
def alwaysJudgment : Judgment where
  key := `SPMF.Cost.Always
  subject? ty := do
    unless ty.isAppOfArity `SPMF.Cost.Always 3 do return none
    return some (ty.getArg! 1, fun g => mkApp3 ty.getAppFn (ty.getArg! 0) g (ty.getArg! 2))
  bridges := #[none, some `SPMF.Cost.Always.of_isBounded, some `SPMF.Cost.Always.of_always]
  lawSuffix := `cost_bounded
  noLeaf g := m!"cost_bound: no rule, hypothesis, or `.cost_bounded` law bounds the cost \
    of{indentExpr g}\nTag a rule for it `@[gen_rule]`, or pass a cost bound to `cost_bound [_]`."

/-- `IsBounded g c` with `c` to be found: a combinator's generator argument, whose cost bound the
combinator's rule is stated in terms of. Only a fact can supply it. -/
def isBoundedJudgment : Judgment where
  key := `IsBounded
  subject? ty := do
    unless ty.isAppOfArity `IsBounded 3 do return none
    return some (ty.getArg! 1, fun g => mkApp3 ty.getAppFn (ty.getArg! 0) g (ty.getArg! 2))
  bridges := #[none]
  lawSuffix := `cost_bounded
  noLeaf g := m!"cost_bound: no hypothesis or `.cost_bounded` law bounds the cost of the \
    combinator argument{indentExpr g}\nPass a cost bound for it to `cost_bound [_]`."

/-- Every judgment the walker knows, tried in order. -/
def judgments : Array Judgment := #[massJudgment, alwaysJudgment, isBoundedJudgment]

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

/-- Whether `head` is a combinator: some judgment has a rule for it. -/
def isCombinator (env : Environment) (head : Name) : Bool :=
  (genRuleExt.getState env).any fun _ byHead => byHead.contains head

/-- The judgment a rule concludes and the combinator it is about. -/
def ruleKey (declName : Name) (type : Expr) : MetaM (Name × Name) :=
  forallTelescope type fun _ concl => do
    let concl ← whnfR concl
    for j in judgments do
      if let some (g, _) ← j.subject? concl then
        if let some head := g.getAppFn.constName? then
          return (j.key, head)
    throwError "gen_rule: `{declName}` must conclude a judgment about a combinator application \
      (one of {judgments.map (·.key)}), not{indentExpr concl}"

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

end Basalt.Walk
