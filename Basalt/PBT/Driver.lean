/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Michael Hicks, Harrison Goldstein
-/
module

public import Basalt.PBT.Backend

/-!
# A Command-Line Front End

Infrastructure for running Basalt properties from the command line.
-/

public section

namespace Basalt.PBT

/-! Command-line flags. A flag with a value is named with its `=` (`"-runs="`); `isFlag` takes the
bare name (`"--truncate"`), for a flag that may be given with or without one. -/

/-- `a`'s value, if `a` is the flag `flag` given one: `flagArg? "-runs=" "-runs=5" = some "5"`. -/
def flagArg? (flag a : String) : Option String :=
  if a.startsWith flag then some (a.drop flag.length).toString else none

/-- The value of the first `flag` in `argv`, if any. -/
def flagValue? (argv : Array String) (flag : String) : Option String :=
  argv.findSome? (flagArg? flag)

/-- Whether `a` is the flag `name`, bare or with a value (`name=v`). -/
def isFlag (name a : String) : Bool :=
  a == name || (flagArg? (name ++ "=") a).isSome

/-- The value of an `-flag=N` argument, or `default`. -/
private def natFlag (argv : Array String) (flag : String) (default : Nat) : Nat :=
  ((flagValue? argv flag).bind String.toNat?).getD default

/-- The run budget, read from `-runs=N`: libFuzzer's own flag spelling, so one command line drives
every backend. -/
def runsOf (argv : Array String) (default : Nat := 100000) : Nat :=
  natFlag argv "-runs=" default

/-- How many inputs may be discarded per requested run before the campaign gives up, read from
`-discard_ratio=N`. QuickCheck's `maxDiscardRatio`, spelled as a flag. -/
def discardRatioOf (argv : Array String) (default : Nat := 10) : Nat :=
  natFlag argv "-discard_ratio=" default

/-- Report a usage error and exit with code `2`. A campaign reports its verdict only through its exit
status, so a usage error must read as neither a pass (`0`) nor a counterexample (`failureExitCode`,
which is also libFuzzer's own). -/
def usageError (msg : String) : IO α := do
  IO.eprintln msg
  IO.Process.exit 2

/-- The requested backend, or the first one as the default. -/
def findBackend (backends : List Backend) : Option String → Option Backend
  | none => backends.head?
  | some n => backends.find? (·.name == n)

/-- A front end for an executable exposing several named properties:
`<exe> [--backend=…] <property> [args...]` starts a campaign, and `<exe> replay <property> <file>`
reproduces a saved input.

`backends` defaults to everything tagged `@[basalt_backend]` at the *call site*, so an executable
offers each backend whose module it imports, with no further ceremony; the first one registered, in
import order, is the default. -/
def dispatch (exe : String) (props : List (String × Property)) (args : List String)
    (backends : List Backend := by exact registered_backends%) : IO Unit := do
  let names := String.intercalate ", " (props.map (·.1))
  let usage :=
    s!"usage: {exe} [--backend={String.intercalate "|" (backends.map (·.name))}] <property> \
        [-runs=N] [-discard_ratio=N] [backend args...]\n"
      ++ s!"       {exe} replay <property> <file>\n"
      ++ s!"known properties: {names}"
  let (flags, rest) := args.partition (flagArg? "--backend=" · |>.isSome)
  let requested := flags.head?.bind (flagArg? "--backend=")
  if backends.isEmpty then
    usageError "no backend is registered: import a module that tags one `@[basalt_backend]`"
  match findBackend backends requested, rest with
  | none, _ => usageError s!"unknown backend '{requested.getD ""}'\n{usage}"
  | some backend, "replay" :: name :: path :: _ =>
    match backend.replay?, props.lookup name with
    | none, _ => usageError s!"backend '{backend.name}' has no saved inputs to replay"
    | _, none => usageError s!"unknown property '{name}'; known: {names}"
    | some replay, some T => replay T path
  | some backend, name :: rest =>
    match props.lookup name with
    | some T => backend.campaign T rest.toArray
    | none => usageError s!"unknown property '{name}'; known: {names}"
  | some _, [] => usageError usage

end Basalt.PBT
