/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
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

/-- What a campaign found: how many inputs were actually *tested*, how many were discarded, the
counterexample if one was found (in which case the campaign stopped there), and whether the campaign
gave up before testing as many inputs as it was asked to. -/
structure CampaignReport where
  runs : Nat
  discards : Nat
  counterexample? : Option String
  gaveUp : Bool := false
  deriving Inhabited

/-- Run `step` until `runs` inputs have been tested or a counterexample is found. Discarded inputs
have their own budget, `maxDiscardRatio * runs`, and do not consume a run: a property with a
selective precondition still gets the tests it asked for. Exhausting that budget sets `gaveUp`,
which is *not* a pass — a property whose precondition is unsatisfiable would otherwise report
success without ever having been tested. (This is QuickCheck's accounting, ratio and all.)

Pure bookkeeping: a caller decides what to print and whether to exit. The `for` bounds the loop by
the two budgets together, which is the whole point of having them — the campaign is total. -/
def runCampaign (step : IO TestOutcome) (runs : Nat) (maxDiscardRatio : Nat := 10) :
    IO CampaignReport := do
  let discardBudget := maxDiscardRatio * runs
  let mut report : CampaignReport := { runs := 0, discards := 0, counterexample? := none }
  for _ in [0:runs + discardBudget] do
    if report.runs ≥ runs || report.discards ≥ discardBudget
        || report.counterexample?.isSome then break
    match ← step with
    | Except.ok () => report := { report with runs := report.runs + 1 }
    | Except.error .discard => report := { report with discards := report.discards + 1 }
    | Except.error (.fail msg) =>
      report := { report with runs := report.runs + 1, counterexample? := some msg }
  if report.counterexample?.isNone && report.runs < runs then
    report := { report with gaveUp := true }
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

/-- Report the campaign: the shared failure report, the give-up report, or a one-line summary on
stdout. Giving up goes to `reportFailure` because it is one: nothing was falsified, but the property
was not tested either, and a campaign that says so quietly on stdout will be read as a pass. -/
def CampaignReport.report (r : CampaignReport) (label : String) : IO Unit :=
  match r.counterexample? with
  | some c => reportFailure c #[("runs", s!"{r.runs} ({r.discards} discarded)")]
  | none =>
    if r.gaveUp then
      reportFailure s!"none — gave up after {r.discards} discarded inputs"
        #[("runs", s!"{r.runs} ({r.discards} discarded)")]
    else
      IO.println s!"[basalt] {label}: {r.runs} runs, no counterexample ({r.discards} discarded)"

/-- The exit code of a failed campaign. `77` is what libFuzzer uses for a crash, so a caller need not
know which interpretation ran. -/
def failureExitCode : UInt8 := 77

/-- Exit with `failureExitCode` if the campaign failed — which includes giving up. -/
def CampaignReport.exitOnFailure (r : CampaignReport) : IO Unit :=
  if r.counterexample?.isSome || r.gaveUp then IO.Process.exit failureExitCode else pure ()

/-- A whole campaign: announce it, run it, report it, and exit if it failed. -/
def campaign (label : String) (step : IO TestOutcome) (runs : Nat)
    (maxDiscardRatio : Nat := 10) : IO Unit := do
  IO.println s!"[basalt] starting {label} campaign (runs={runs})"
  let r ← runCampaign step runs maxDiscardRatio
  r.report label
  r.exitOnFailure

/-- Test `T` at the default `IO` interpretation, where choices come from `IO.rand`. -/
def ioCampaign (T : Property) (runs : Nat) (maxDiscardRatio : Nat := 10) : IO Unit :=
  campaign "IO" (T IO) runs maxDiscardRatio

/-- Test `T` at `Plausible.Gen`, where choices come from Plausible's `StdGen`.

The `size` handed to `Plausible.Gen.run` is inert: Basalt generators bound their own recursion (via
`pick`/`partial_fixpoint`) and no combinator reads Plausible's size parameter. -/
def plausibleCampaign (T : Property) (runs : Nat) (maxDiscardRatio : Nat := 10) : IO Unit :=
  campaign "Plausible.Gen" (Plausible.Gen.run (T Plausible.Gen) 0) runs maxDiscardRatio

end Basalt.PBT
