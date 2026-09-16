/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt.SPMF.Mass

/-!
# The `@[mass_bound]` Attribute

The registry the `mass_bound` tactic walks: the rules for each generator combinator, keyed by the
combinator's head constant and tried in the order they were declared. A rule must conclude
`<bound> ≤ SPMF.mass (<combinator> …)`; that is what makes the key readable off its statement, and
what makes the walk syntax-directed.
-/

open Lean Meta

namespace Basalt.MassBound

/-- Combinator head constant ↦ the `@[mass_bound]` rules that bound its mass below, in declaration
order. -/
initialize massBoundExt : SimplePersistentEnvExtension (Name × Name) (NameMap (Array Name)) ←
  let add (m : NameMap (Array Name)) : Name × Name → NameMap (Array Name)
    | (k, v) => m.insert k (((m.find? k).getD #[]).push v)
  registerSimplePersistentEnvExtension {
    addEntryFn := add
    addImportedFn := fun ess => ess.foldl (fun m es => es.foldl add m) {}
  }

/-- The combinator a rule is about: the head constant of `g` in a conclusion `_ ≤ SPMF.mass g`. -/
def ruleKey (declName : Name) (type : Expr) : MetaM Name :=
  forallTelescopeReducing type fun _ concl => do
    let concl ← whnfR concl
    let fail {α : Type} : MetaM α := throwError
      "mass_bound: `{declName}` must conclude `_ ≤ SPMF.mass _`, not{indentExpr concl}"
    unless concl.isAppOfArity ``LE.le 4 do fail
    let rhs ← whnfR (concl.getArg! 3)
    unless rhs.isAppOfArity ``SPMF.mass 2 do fail
    let some key := (rhs.getArg! 1).getAppFn.constName? | fail
    return key

/-- `@[mass_bound]` — teach the `mass_bound` tactic how to bound one combinator's mass below. -/
syntax (name := massBoundAttr) "mass_bound" : attr

initialize registerBuiltinAttribute {
  name := `massBoundAttr
  descr := "a mass lower bound for one generator combinator, used by the `mass_bound` tactic"
  add := fun declName _ kind => do
    unless kind == .global do throwError "mass_bound: must be a global attribute"
    let key ← MetaM.run' (ruleKey declName (← getConstInfo declName).type)
    modifyEnv (massBoundExt.addEntry · (key, declName))
}

end Basalt.MassBound
