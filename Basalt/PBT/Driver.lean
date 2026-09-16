/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Michael Hicks, Harrison Goldstein
-/
import Basalt.PBT.Backend

/-!
# A Command-Line Front End

Infrastructure for running Basalt properties from the command line.
-/

namespace Basalt.PBT

/-- The value of an `-flag=N` argument, or `default`. -/
private def natFlag (argv : Array String) (flag : String) (default : Nat) : Nat :=
  match argv.findSome? (fun a =>
      if a.startsWith flag then (a.drop flag.length).toNat? else none) with
  | some n => n
  | none => default

/-- The run budget, read from `-runs=N`: libFuzzer's own flag spelling, so one command line drives
every backend. -/
def runsOf (argv : Array String) (default : Nat := 100000) : Nat :=
  natFlag argv "-runs=" default

/-- How many inputs may be discarded per requested run before the campaign gives up, read from
`-discard_ratio=N`. QuickCheck's `maxDiscardRatio`, spelled as a flag. -/
def discardRatioOf (argv : Array String) (default : Nat := 10) : Nat :=
  natFlag argv "-discard_ratio=" default

/-- Uniform random testing at `IO`. -/
@[basalt_backend]
def ioBackend : Backend where
  name := "io"
  campaign T argv := ioCampaign T (runsOf argv) (discardRatioOf argv)

/-- Uniform random testing at `Plausible.Gen`. -/
@[basalt_backend]
def plausibleBackend : Backend where
  name := "plausible"
  campaign T argv := plausibleCampaign T (runsOf argv) (discardRatioOf argv)

/-- Report a usage error and exit nonzero.

The exit code is the point. A campaign reports its verdict *only* through the exit status, so while
these paths exited `0` a misspelled property name was indistinguishable from a property that passed:
the `.github/workflows/fuzz_build.yml` steps that assert "this property must fail" would have read
that `0` as the property having survived a campaign that never ran. `2` also distinguishes it from a
counterexample (`77` at `IO`/`Plausible`, libFuzzer's own code under the fuzzer). -/
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
that imports a fuzzer backend offers it with no further ceremony; the first one registered is the
default, which is `ioBackend` for anyone importing this module. -/
def dispatch (exe : String) (props : List (String × Property)) (args : List String)
    (backends : List Backend := by exact registered_backends%) : IO Unit := do
  let names := String.intercalate ", " (props.map (·.1))
  let usage :=
    s!"usage: {exe} [--backend={String.intercalate "|" (backends.map (·.name))}] <property> \
        [-runs=N] [-discard_ratio=N] [backend args...]\n"
      ++ s!"       {exe} replay <property> <file>\n"
      ++ s!"known properties: {names}"
  let (flags, rest) := args.partition (·.startsWith "--backend=")
  let requested := flags.head?.map (fun f => (f.drop "--backend=".length).toString)
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
