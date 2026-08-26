/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Michael Hicks
-/
import Basalt.Fuzz.Core
import Basalt.IO
import Basalt.PlausibleGen

/-!
# Running a property: libFuzzer, or plain random testing

The Lean half of the C bridge in `Basalt/Fuzz/native.c`. `go` hands a per-input closure and the
remaining CLI arguments to libFuzzer's driver (via the `basalt_fuzz_go` extern), and libFuzzer calls
back into `runOneIO` once per mutated input.

Because a Basalt property is polymorphic in its monad, the *same* property term also runs under the
random interpretations (`IO`, `Plausible.Gen`) with no fuzzer involved — that is what `Property` and
`randomCampaign` below are for, and what `--backend=` selects. The three backends share the failure
contract (counterexample on stderr, exit 77), so a campaign under one is directly comparable to a
campaign under another.

Failure handling follows **bolero** (`/home/mwhicks/src/bolero`, `lib/bolero-libfuzzer`), the proven
libFuzzer PBT integration: on a failing input the closure prints the counterexample (rendered from
the generated value via `Repr`) and returns `1`, and the C bridge `abort()`s so libFuzzer saves the
crashing input as an artifact. Reproduce it with `replay`. The campaign's result is therefore the
process exit code (nonzero ⇒ a counterexample was found and saved) plus the printed report — not a
value returned to the Lean caller; see `BasaltFuzz/DESIGN.md` §9 for the subprocess model that would
return one.

This module imports only `Basalt.Fuzz.Core` (no Mathlib), so an executable built from it links a
small closure — see `BasaltFuzz/DESIGN.md` §6. The *executable* is opt-in (`fuzz-run/build.sh` owns
the C emission and the native link); this module is still elaborated by `lake build`, which is what
`BasaltTest/Fuzz.lean` uses to pin the byte → choice mapping.
-/

namespace Basalt.Fuzz

/-- The C bridge: store `run` as the per-input callback, then hand `argv` to libFuzzer's driver.
Blocks in the fuzzing loop; libFuzzer parses its own flags from `argv`. Returns only if the campaign
completes without a failure (a failure `abort()`s the process). -/
@[extern "basalt_fuzz_go"]
opaque goImpl (run : ByteArray → IO UInt8) (argv : Array String) : IO Unit

/-- Run the property on one input. On failure, print the counterexample and the raw bytes (flushing,
since the C side then `abort()`s), and return code `1`; libFuzzer records the crashing artifact.
`0` = pass, `2` = discard (not added to the corpus).

`counters` tallies executions and discards so a failing campaign can report the same
`runs : N (M discarded)` line the random backends do — libFuzzer's own `#N` markers count only
corpus-worthy inputs, which is not the number of tests run. -/
def runOneIO (counters : IO.Ref (Nat × Nat)) (T : FuzzGen TestOutcome) (bytes : ByteArray) :
    IO UInt8 := do
  counters.modify (fun (runs, discards) => (runs + 1, discards))
  match runOne T bytes with
  | .pass => pure 0
  | .discard => counters.modify (fun (r, d) => (r, d + 1)); pure 2
  | .fail render =>
    let (runs, discards) ← counters.get
    IO.eprintln "\n*** BASALT PROPERTY FAILED ***"
    IO.eprintln s!"counterexample : {render ()}"
    IO.eprintln s!"input bytes    : {bytes.toList.map (fun b => b.toNat)}"
    IO.eprintln s!"runs           : {runs} ({discards} discarded)"
    (← IO.getStdout).flush
    (← IO.getStderr).flush
    pure 1

/-- Start a fuzzing campaign for property `T`. `argv` is forwarded to libFuzzer (corpus dirs,
`-runs`, `-max_len`, `-artifact_prefix`, …). A failure aborts the process (exit code set by
libFuzzer, artifact saved).

Do not add a post-campaign summary here: libFuzzer's driver calls `exit()` when `-runs` is exhausted,
so nothing after `goImpl` runs, and a line placed there simply never appears (its own
`Done N runs …` is the passing-campaign report). This is why the run tally lives in `runOneIO`, which
prints it on the failing input itself. -/
def go (T : FuzzGen TestOutcome) (argv : Array String := #[]) : IO Unit := do
  IO.println s!"[basalt-fuzz] starting libFuzzer campaign ({argv.toList})"
  let counters ← IO.mkRef (0, 0)
  goImpl (fun bytes => runOneIO counters T bytes) argv

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

/-! ### The random backends

A property is a `[Gen G] → G TestOutcome`, so nothing about it is fuzzer-specific: instantiating `G`
at `IO` or `Plausible.Gen` gives ordinary uniform random testing of the *same* term. The loop below
is all the extra machinery that takes, and it reports through the same failure contract as `go`
(counterexample on stderr, exit 77) so campaigns are comparable across backends. -/

/-- A property held polymorphically, so one registry entry serves every backend. The explicit `G`
binder is what lets a caller pick the interpretation (`T FuzzGen`, `T IO`, `T Plausible.Gen`);
`List (String × FuzzGen TestOutcome)` could not. -/
def Property := (G : Type → Type) → [Gen G] → G TestOutcome

/-- The interpretation a campaign runs the property at: libFuzzer-driven, or one of the two random
`Gen` instances. -/
inductive Backend where
  /-- `FuzzGen`: choices come from libFuzzer's mutated byte buffer, guided by coverage. -/
  | fuzz
  /-- `IO`: choices come from `IO.rand`. -/
  | io
  /-- `Plausible.Gen`: choices come from Plausible's `StdGen`. -/
  | plausible

/-- Parse the `--backend=` value. -/
def Backend.ofString? : String → Option Backend
  | "fuzz" => some .fuzz
  | "io" => some .io
  | "plausible" => some .plausible
  | _ => none

/-- Run `step` up to `runs` times, stopping at the first counterexample. `exit 77` matches the code
libFuzzer uses for a crash, so a caller need not know which backend ran. -/
def randomCampaign (label : String) (step : IO TestOutcome) (runs : Nat) : IO Unit := do
  IO.println s!"[basalt-fuzz] starting {label} campaign (runs={runs})"
  let mut discards := 0
  for i in [0:runs] do
    match ← step with
    | .pass => pure ()
    | .discard => discards := discards + 1
    | .fail render =>
      IO.eprintln "\n*** BASALT PROPERTY FAILED ***"
      IO.eprintln s!"counterexample : {render ()}"
      IO.eprintln s!"runs           : {i + 1} ({discards} discarded)"
      (← IO.getStdout).flush
      (← IO.getStderr).flush
      IO.Process.exit 77
  IO.println s!"[basalt-fuzz] {label}: {runs} runs, no counterexample ({discards} discarded)"

/-- The `-runs=N` bound, read from the same flag spelling libFuzzer uses so one command line drives
every backend. Absent, a random campaign is finite anyway (libFuzzer's default is unbounded, but an
unbounded random loop on a property with no bug would simply hang). -/
def runsOf (argv : Array String) (default : Nat := 100000) : Nat :=
  match argv.findSome? (fun a => if a.startsWith "-runs=" then (a.drop 6).toNat? else none) with
  | some n => n
  | none => default

/-- Run one campaign of `T` under `backend`. `fuzz` forwards all of `argv` to libFuzzer; the random
backends read only `-runs=N` from it.

The `size` handed to `Plausible.Gen.run` is inert here: Basalt generators bound their own recursion
(via `pick`/`partial_fixpoint`) and no combinator reads Plausible's size parameter, so it cannot
affect the distribution. -/
def campaign (T : Property) (backend : Backend) (argv : Array String) : IO Unit :=
  match backend with
  | .fuzz => go (T FuzzGen) argv
  | .io => randomCampaign "IO" (T IO) (runsOf argv)
  | .plausible => randomCampaign "Plausible.Gen" (Plausible.Gen.run (T Plausible.Gen) 0) (runsOf argv)

/-- A tiny front end for an executable exposing several named properties.
`fuzz [--backend=…] <property> [args...]` starts a campaign; `fuzz replay <property> <file>`
reproduces a saved input (fuzz backend only — a saved artifact *is* a `FuzzGen` byte buffer). -/
def dispatch (props : List (String × Property)) (args : List String) : IO Unit := do
  let names := String.intercalate ", " (props.map (·.1))
  let usage :=
    "usage: basalt-fuzz [--backend=fuzz|io|plausible] <property> [-runs=N] [libFuzzer args...]\n"
      ++ "       basalt-fuzz replay <property> <file>\n"
      ++ s!"known properties: {names}"
  match args with
  | "replay" :: name :: path :: _ =>
    match props.lookup name with
    | some T => replay (T FuzzGen) path
    | none => IO.eprintln s!"unknown property '{name}'; known: {names}"
  | _ =>
    let (flags, rest) := args.partition (·.startsWith "--backend=")
    match flags.head?.map (fun f => Backend.ofString? (f.drop 10).toString), rest with
    | some none, _ => IO.eprintln s!"unknown backend in '{flags.head!}'\n{usage}"
    | _, [] => IO.eprintln usage
    | backend?, name :: rest =>
      match props.lookup name with
      | some T => campaign T (backend?.join.getD .fuzz) rest.toArray
      | none => IO.eprintln s!"unknown property '{name}'; known: {names}"

end Basalt.Fuzz
