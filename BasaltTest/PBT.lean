/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Michael Hicks
-/
import Basalt.PBT
import Basalt.Combinators

/-!
# Property-testing regression tests

Campaigns whose outcome cannot depend on the random draw — the properties below either ignore their
input or draw from a singleton range — so the report is pinned at every backend.
-/

open Basalt.PBT RandomChoice

private def render : TestOutcome → String
  | .pass => "pass"
  | .fail r => s!"fail: {r ()}"
  | .discard => "discard"

private def summary (r : CampaignReport) : String :=
  s!"runs={r.runs} discards={r.discards} counterexample={reprStr r.counterexample?}"

/-! ## Stating a property -/

/-- info: pass -/
#guard_msgs in #eval do IO.println (render (← (check true : IO TestOutcome)))

/-- info: fail: (no counterexample detail) -/
#guard_msgs in #eval do IO.println (render (← (check false : IO TestOutcome)))

/-- info: fail: x=1 -/
#guard_msgs in #eval do IO.println (render (← (checkWith false (fun () => "x=1") : IO TestOutcome)))

/-- info: discard -/
#guard_msgs in #eval do IO.println (render (← (assume false : IO TestOutcome)))

/-! ## Running a campaign

`runCampaign` reports and does not exit, so a failing campaign is `#eval`-able. -/

/-- A property that fails on its first input, with a deterministic counterexample. -/
private def propFail [Gen G] : G TestOutcome :=
  forAll (chooseNat 0 0) (fun _ => false)

/-- A property no input can falsify. -/
private def propPass [Gen G] : G TestOutcome :=
  forAll (chooseNat 0 9) (fun n => n ≤ 9)

/-- A property whose precondition rejects every input. -/
private def propDiscard [Gen G] : G TestOutcome := do
  let n ← chooseNat 0 9
  assume (n > 9)

/- A counterexample stops the campaign on the input that found it. -/
/-- info: runs=1 discards=0 counterexample=some "0" -/
#guard_msgs in #eval do IO.println (summary (← runCampaign propFail 100))

/- A passing campaign runs its whole budget. -/
/-- info: runs=25 discards=0 counterexample=none -/
#guard_msgs in #eval do IO.println (summary (← runCampaign propPass 25))

/- Discards are counted, and never mistaken for passes or failures. -/
/-- info: runs=10 discards=10 counterexample=none -/
#guard_msgs in #eval do IO.println (summary (← runCampaign propDiscard 10))

/- The same property, tested at `Plausible.Gen` instead: nothing about it changes. -/
/-- info: runs=1 discards=0 counterexample=some "0" -/
#guard_msgs in #eval do IO.println (summary (← runCampaign (Plausible.Gen.run propFail 0) 100))

/- The failure report: the counterexample, then the run tally, aligned. -/
/--
info:
*** BASALT PROPERTY FAILED ***
counterexample : 0
runs           : 1 (0 discarded)
-/
#guard_msgs in #eval do (← runCampaign propFail 100).report "IO"

/-! ## The command line -/

#guard runsOf #["-runs=7"] == 7
#guard runsOf #["some-dir", "-max_len=64"] 5 == 5
#guard (findBackend [ioBackend, plausibleBackend] none).map (·.name) == some "io"
#guard (findBackend [ioBackend, plausibleBackend] (some "plausible")).map (·.name) == some "plausible"
#guard (findBackend [ioBackend, plausibleBackend] (some "fuzz")).isNone

private def demo : List (String × Property) :=
  [("pass", fun _ => propPass), ("fail", fun _ => propFail)]

/--
info: [basalt] starting IO campaign (runs=3)
[basalt] IO: 3 runs, no counterexample (0 discarded)
-/
#guard_msgs in
#eval dispatch "demo" [ioBackend, plausibleBackend] demo ["--backend=io", "pass", "-runs=3"]

/--
info: [basalt] starting Plausible.Gen campaign (runs=3)
[basalt] Plausible.Gen: 3 runs, no counterexample (0 discarded)
-/
#guard_msgs in
#eval dispatch "demo" [ioBackend, plausibleBackend] demo ["--backend=plausible", "pass", "-runs=3"]
