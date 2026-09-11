/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Michael Hicks, Harrison Goldstein
-/

import Basalt.PBT.Property
import Basalt.IO
import Basalt.PlausibleGen

/-!
# Running a Campaign

A campaign runs a property until it fails or a run budget is exhausted.
-/

namespace Basalt.PBT

structure CampaignReport where
  /-- The total number of test inputs that passed the property's precondition and were tested
  against the SUT. -/
  runs : Nat
  /-- The total number of test inputs that failed the property's precondition or `assume`
  statements. -/
  discards : Nat
  /-- A string representation of the counterexample, if one is found. -/
  counterexample? : Option String
  /-- `True` if the test execution gave up due to excessive discards. -/
  gaveUp : Bool := false
  deriving Inhabited

/-- Run `step` until `runs` inputs have been tested or a counterexample is found. Discarded inputs
have their own budget, `maxDiscardRatio * runs`, and do not consume a run. Exhausting that budget
sets `gaveUp`. -/
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

def reportFailure (counterexample : String) (details : Array (String × String) := #[]) : IO Unit := do
  (← IO.getStdout).flush
  IO.eprintln "\n*** BASALT PROPERTY FAILED ***"
  for (label, value) in #[("counterexample", counterexample)] ++ details do
    IO.eprintln s!"{padTo 15 label}: {value}"
  (← IO.getStderr).flush

def CampaignReport.report (r : CampaignReport) (label : String) : IO Unit :=
  match r.counterexample? with
  | some c => reportFailure c #[("runs", s!"{r.runs} ({r.discards} discarded)")]
  | none =>
    if r.gaveUp then
      reportFailure s!"none — gave up after {r.discards} discarded inputs"
        #[("runs", s!"{r.runs} ({r.discards} discarded)")]
    else
      IO.println s!"[basalt] {label}: {r.runs} runs, no counterexample ({r.discards} discarded)"

/-- The exit code of a failed campaign. (`77` is what libFuzzer uses for a crash, so a caller need
not know which interpretation ran.) -/
def failureExitCode : UInt8 := 77

def CampaignReport.exitOnFailure (r : CampaignReport) : IO Unit :=
  if r.counterexample?.isSome || r.gaveUp then IO.Process.exit failureExitCode else pure ()

def campaign (label : String) (step : IO TestOutcome) (runs : Nat)
    (maxDiscardRatio : Nat := 10) : IO Unit := do
  IO.println s!"[basalt] starting {label} campaign (runs={runs})"
  let r ← runCampaign step runs maxDiscardRatio
  r.report label
  r.exitOnFailure

/-- Test `T` at the default `IO` interpretation, where choices come from `IO.rand`. -/
def ioCampaign (T : Property) (runs : Nat) (maxDiscardRatio : Nat := 10) : IO Unit :=
  campaign "IO" (runProp (T IO)) runs maxDiscardRatio

/-- Test `T` at `Plausible.Gen`, where choices come from Plausible's `StdGen`.

The `size` handed to `Plausible.Gen.run` is inert: Basalt generators bound their own recursion (via
`pick`/`partial_fixpoint`) and no combinator reads Plausible's size parameter. -/
def plausibleCampaign (T : Property) (runs : Nat) (maxDiscardRatio : Nat := 10) : IO Unit :=
  campaign "Plausible.Gen" (Plausible.Gen.run (runProp (T Plausible.Gen)) 0) runs maxDiscardRatio

end Basalt.PBT
