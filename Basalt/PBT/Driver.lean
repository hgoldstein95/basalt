/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Michael Hicks
-/
import Basalt.PBT.Campaign

/-!
# A command-line front end

`dispatch` turns a list of named properties into a `main`: it picks the property and the
interpretation to test it at. Backends are a list rather than an enumeration so that an
interpretation defined outside this module can register itself.
-/

namespace Basalt.PBT

/-- An interpretation a campaign can run at, named for the command line. -/
structure Backend where
  /-- The `--backend=` spelling. -/
  name : String
  /-- Start a campaign, given the property and the command-line arguments after the property name. -/
  campaign : Property → Array String → IO Unit
  /-- Reproduce one saved input, for a backend whose inputs are files (a fuzzer's artifacts). -/
  replay? : Option (Property → String → IO Unit) := none

/-- The run budget, read from `-runs=N`: libFuzzer's own flag spelling, so one command line drives
every backend. -/
def runsOf (argv : Array String) (default : Nat := 100000) : Nat :=
  match argv.findSome? (fun a => if a.startsWith "-runs=" then (a.drop 6).toNat? else none) with
  | some n => n
  | none => default

/-- Uniform random testing at `IO`. -/
def ioBackend : Backend where
  name := "io"
  campaign T argv := ioCampaign T (runsOf argv)

/-- Uniform random testing at `Plausible.Gen`. -/
def plausibleBackend : Backend where
  name := "plausible"
  campaign T argv := plausibleCampaign T (runsOf argv)

/-- The requested backend, or the first one as the default. -/
def findBackend (backends : List Backend) : Option String → Option Backend
  | none => backends.head?
  | some n => backends.find? (·.name == n)

/-- A front end for an executable exposing several named properties:
`<exe> [--backend=…] <property> [args...]` starts a campaign, and `<exe> replay <property> <file>`
reproduces a saved input. The first backend in `backends` is the default. -/
def dispatch (exe : String) (backends : List Backend) (props : List (String × Property))
    (args : List String) : IO Unit := do
  let names := String.intercalate ", " (props.map (·.1))
  let usage :=
    s!"usage: {exe} [--backend={String.intercalate "|" (backends.map (·.name))}] <property> \
        [-runs=N] [backend args...]\n"
      ++ s!"       {exe} replay <property> <file>\n"
      ++ s!"known properties: {names}"
  let (flags, rest) := args.partition (·.startsWith "--backend=")
  let requested := flags.head?.map (fun f => (f.drop "--backend=".length).toString)
  match findBackend backends requested, rest with
  | none, _ => IO.eprintln s!"unknown backend '{requested.getD ""}'\n{usage}"
  | some backend, "replay" :: name :: path :: _ =>
    match backend.replay?, props.lookup name with
    | none, _ => IO.eprintln s!"backend '{backend.name}' has no saved inputs to replay"
    | _, none => IO.eprintln s!"unknown property '{name}'; known: {names}"
    | some replay, some T => replay T path
  | some backend, name :: rest =>
    match props.lookup name with
    | some T => backend.campaign T rest.toArray
    | none => IO.eprintln s!"unknown property '{name}'; known: {names}"
  | some _, [] => IO.eprintln usage

end Basalt.PBT
