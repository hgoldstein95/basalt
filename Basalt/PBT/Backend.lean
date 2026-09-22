/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Michael Hicks, Harrison Goldstein
-/
import Lean.Elab.ElabRules
import Lean.Meta.AppBuilder
import Basalt.PBT.Campaign

/-!
# Backends Registry

A `Backend` is a way of running a `Property`.  `@[basalt_backend]` adds one to a global registry, so
an interpretation defined downstream of the front end can still be reached from the command line.
-/

open Lean Meta Elab

namespace Basalt.PBT

/-- One way to run a property: an interpretation of `Gen`, and a campaign over it. Register with
`@[basalt_backend]` rather than naming it anywhere. -/
structure Backend where
  /-- The `--backend=` spelling. -/
  name : String
  /-- Start a campaign, given the property and the command-line arguments after the property name. -/
  campaign : Property → Array String → IO Unit
  /-- Reproduce one saved input, for a backend whose inputs are files (a fuzzer's artifacts). -/
  replay? : Option (Property → String → IO Unit) := none

/-- The registered backends, in declaration order, imports first. -/
initialize backendExt : SimplePersistentEnvExtension Name (Array Name) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := Array.flatten
  }

/-- `@[basalt_backend]` — make this `Backend` one of the ones `dispatch` offers. -/
syntax (name := backendAttr) "basalt_backend" : attr

initialize registerBuiltinAttribute {
  name := `backendAttr
  descr := "make this `Backend` one of the ones `dispatch` offers"
  applicationTime := .afterCompilation
  add := fun declName _ kind => do
    unless kind == .global do
      throwError "basalt_backend: must be a global attribute"
    let type := (← getConstInfo declName).type
    unless type.isConstOf ``Backend do
      throwError "basalt_backend: expected a definition of type `Backend`, got{indentExpr type}"
    modifyEnv (backendExt.addEntry · declName)
}

/-- Elaborates to the `List Backend` of everything tagged `@[basalt_backend]`. -/
elab "registered_backends%" : term => do
  mkListLit (mkConst ``Backend) ((backendExt.getState (← getEnv)).toList.map (mkConst ·))

end Basalt.PBT
