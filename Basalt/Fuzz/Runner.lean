/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Michael Hicks
-/
import Basalt.Fuzz.Core

/-!
# Driving `FuzzGen` from libFuzzer

The Lean half of the C bridge in `Basalt/Fuzz/native.c`. `go` hands a per-input closure and the
remaining CLI arguments to libFuzzer's driver (via the `basalt_fuzz_go` extern), and libFuzzer calls
back into `runOneIO` once per mutated input.

Failure handling follows **bolero** (`/home/mwhicks/src/bolero`, `lib/bolero-libfuzzer`), the proven
libFuzzer PBT integration: on a failing input the closure prints the counterexample (rendered from
the generated value via `Repr`) and returns `1`, and the C bridge `abort()`s so libFuzzer saves the
crashing input as an artifact. Reproduce it with `replay`. The campaign's result is therefore the
process exit code (nonzero ⇒ a counterexample was found and saved) plus the printed report — not a
value returned to the Lean caller; see `FUZZING-DESIGN.md` §9 for the subprocess model that would
return one.

This module imports only `Basalt.Fuzz.Core` (no Mathlib), so an executable built from it links a
small closure — see `FUZZING-DESIGN.md` §6. Everything here is opt-in and never part of the default
`lake build`.
-/

namespace Basalt.Fuzz

/-- The C bridge: store `run` as the per-input callback, then hand `argv` to libFuzzer's driver.
Blocks in the fuzzing loop; libFuzzer parses its own flags from `argv`. Returns only if the campaign
completes without a failure (a failure `abort()`s the process). -/
@[extern "basalt_fuzz_go"]
opaque goImpl (run : ByteArray → IO UInt8) (argv : Array String) : IO Unit

/-- Run the property on one input. On failure, print the counterexample and the raw bytes (flushing,
since the C side then `abort()`s), and return code `1`; libFuzzer records the crashing artifact.
`0` = pass, `2` = discard (not added to the corpus). -/
def runOneIO (T : FuzzGen TestOutcome) (bytes : ByteArray) : IO UInt8 := do
  match runOne T bytes with
  | .pass => pure 0
  | .discard => pure 2
  | .fail render =>
    IO.eprintln "\n*** BASALT PROPERTY FAILED ***"
    IO.eprintln s!"counterexample : {render ()}"
    IO.eprintln s!"input bytes    : {bytes.toList.map (fun b => b.toNat)}"
    (← IO.getStdout).flush
    (← IO.getStderr).flush
    pure 1

/-- Start a fuzzing campaign for property `T`. `argv` is forwarded to libFuzzer (corpus dirs,
`-runs`, `-max_len`, `-artifact_prefix`, …). Returns when the campaign completes with no failure; a
failure aborts the process (exit code set by libFuzzer, artifact saved). -/
def go (T : FuzzGen TestOutcome) (argv : Array String := #[]) : IO Unit := do
  IO.println s!"[basalt-fuzz] starting campaign ({argv.toList})"
  goImpl (fun bytes => runOneIO T bytes) argv

/-- Replay one saved input file against a property (no fuzzer): reproduces the outcome
deterministically and prints it. This is how a saved artifact (`crash-…`) is consumed. -/
def replay (T : FuzzGen TestOutcome) (path : String) : IO Unit := do
  let bytes ← IO.FS.readBinFile path
  IO.println s!"[basalt-fuzz] replaying {path} ({bytes.size} bytes)"
  match runOne T bytes with
  | .pass => IO.println "outcome: pass"
  | .discard => IO.println "outcome: discard"
  | .fail render =>
    IO.eprintln "*** BASALT PROPERTY FAILED ***"
    IO.eprintln s!"counterexample : {render ()}"

/-- A tiny front end for an executable exposing several named properties.
`fuzz <property> [libFuzzer args...]` starts a campaign; `fuzz replay <property> <file>` reproduces a
saved input. -/
def dispatch (props : List (String × FuzzGen TestOutcome)) (args : List String) : IO Unit := do
  let names := String.intercalate ", " (props.map (·.1))
  match args with
  | "replay" :: name :: path :: _ =>
    match props.lookup name with
    | some T => replay T path
    | none => IO.eprintln s!"unknown property '{name}'; known: {names}"
  | name :: rest =>
    match props.lookup name with
    | some T => go T rest.toArray
    | none => IO.eprintln s!"unknown property '{name}'; known: {names}"
  | [] =>
    IO.eprintln s!"usage: fuzz <property> [libFuzzer args...]\n       fuzz replay <property> <file>\nknown properties: {names}"

end Basalt.Fuzz
