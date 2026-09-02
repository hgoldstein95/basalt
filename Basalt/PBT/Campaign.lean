/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Michael Hicks
-/
import Basalt.PBT.Property
import Basalt.IO
import Basalt.PlausibleGen

/-!
# Running a campaign

A campaign runs a property until it fails or a run budget is exhausted. `runCampaign` neither prints
nor exits: the reporting policy is `CampaignReport`'s, so every interpretation — including one whose
inputs come from somewhere other than a PRNG — shares one failure contract (counterexample on stderr,
exit `failureExitCode`) and campaigns stay comparable across them.
-/

namespace Basalt.PBT

/-- What a campaign found: how many inputs ran, how many were discarded, and the counterexample if
one was found (in which case the campaign stopped there). -/
structure CampaignReport where
  runs : Nat
  discards : Nat
  counterexample? : Option String
  deriving Inhabited

/-- Run `step` up to `runs` times, stopping at the first counterexample. Pure bookkeeping: a caller
decides what to print and whether to exit. -/
def runCampaign (step : IO TestOutcome) (runs : Nat) : IO CampaignReport := do
  let mut report : CampaignReport := { runs := 0, discards := 0, counterexample? := none }
  for _ in [0:runs] do
    report := { report with runs := report.runs + 1 }
    match ← step with
    | .pass => pure ()
    | .discard => report := { report with discards := report.discards + 1 }
    | .fail render =>
      report := { report with counterexample? := some (render ()) }
      break
  return report

private def padTo (width : Nat) (s : String) : String :=
  s ++ "".pushn ' ' (width - s.length)

/-- The counterexample report every interpretation shares, on stderr: the rendered counterexample
followed by `details` lines (a run tally, and whatever else the interpretation can say about the
failing input).

Both streams are flushed, stdout *first*: stdout is block-buffered when redirected, so a report
written to the unbuffered stderr otherwise lands ahead of the announcement of the campaign that
produced it. The trailing flush is for callers that terminate the process immediately after. -/
def reportFailure (counterexample : String) (details : Array (String × String) := #[]) : IO Unit := do
  (← IO.getStdout).flush
  IO.eprintln "\n*** BASALT PROPERTY FAILED ***"
  for (label, value) in #[("counterexample", counterexample)] ++ details do
    IO.eprintln s!"{padTo 15 label}: {value}"
  (← IO.getStderr).flush

/-- Report the campaign: the shared failure report, or a one-line summary on stdout. -/
def CampaignReport.report (r : CampaignReport) (label : String) : IO Unit :=
  match r.counterexample? with
  | some c => reportFailure c #[("runs", s!"{r.runs} ({r.discards} discarded)")]
  | none => IO.println s!"[basalt] {label}: {r.runs} runs, no counterexample ({r.discards} discarded)"

/-- The exit code of a failed campaign. `77` is what libFuzzer uses for a crash, so a caller need not
know which interpretation ran. -/
def failureExitCode : UInt8 := 77

/-- Exit with `failureExitCode` if a counterexample was found. -/
def CampaignReport.exitOnFailure (r : CampaignReport) : IO Unit :=
  if r.counterexample?.isSome then IO.Process.exit failureExitCode else pure ()

/-- A whole campaign: announce it, run it, report it, and exit if it failed. -/
def campaign (label : String) (step : IO TestOutcome) (runs : Nat) : IO Unit := do
  IO.println s!"[basalt] starting {label} campaign (runs={runs})"
  let r ← runCampaign step runs
  r.report label
  r.exitOnFailure

/-- Test `T` at the default `IO` interpretation, where choices come from `IO.rand`. -/
def ioCampaign (T : Property) (runs : Nat) : IO Unit :=
  campaign "IO" (T IO) runs

/-- Test `T` at `Plausible.Gen`, where choices come from Plausible's `StdGen`.

The `size` handed to `Plausible.Gen.run` is inert: Basalt generators bound their own recursion (via
`pick`/`partial_fixpoint`) and no combinator reads Plausible's size parameter. -/
def plausibleCampaign (T : Property) (runs : Nat) : IO Unit :=
  campaign "Plausible.Gen" (Plausible.Gen.run (T Plausible.Gen) 0) runs

end Basalt.PBT
