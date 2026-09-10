/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Michael Hicks
-/
import Basalt.PBT
import Basalt.Combinators
import BasaltExamples.BST.ByInsertion

/-!
# Property-testing regression tests

Campaigns whose outcome cannot depend on the random draw — the properties below either ignore their
input or draw from a singleton range — so the report is pinned at every backend.
-/

open Basalt.PBT RandomChoice

private def render : TestOutcome → String
  | Except.ok () => "pass"
  | Except.error (.fail r) => s!"fail: {r}"
  | Except.error .discard => "discard"

private def summary (r : CampaignReport) : String :=
  s!"runs={r.runs} discards={r.discards} counterexample={reprStr r.counterexample?} \
    gaveUp={r.gaveUp}"

/-! ## Stating a property -/

/-- info: pass -/
#guard_msgs in #eval do IO.println (render (← runProp (check true : PropM IO Unit)))

/-- info: fail:  -/
#guard_msgs in #eval do IO.println (render (← runProp (check false : PropM IO Unit)))

/-- info: fail: x=1 -/
#guard_msgs in #eval do IO.println (render (← runProp (check false s!"x=1" : PropM IO Unit)))

/-- info: discard -/
#guard_msgs in #eval do IO.println (render (← runProp (assume false : PropM IO Unit)))

/-! ### A rejection short-circuits

The property monad, not the `do` block, is what stops the rest of the property from running — so a
precondition holds through a *function call*, which a bare outcome value could not do. -/

private def calleeAssume [Gen G] (n : Nat) : PropM G Unit := do
  assume (n > 100)
  check false "the callee's precondition did not stop the caller"

private def propCallerDiscards [Gen G] : PropM G Unit := do
  let n ← generate (chooseNat 0 9)
  calleeAssume n
  check false "the caller ran past a rejected callee"

/-- info: discard -/
#guard_msgs in #eval do IO.println (render (← runProp (propCallerDiscards : PropM IO Unit)))

/- `assume` in statement position and `==>` around the rest agree. -/
/-- info: discard -/
#guard_msgs in #eval do
  IO.println (render (← runProp (implies false (check true) : PropM IO Unit)))

/-! ### `forAll` names the drawn value, and nests -/

/-- info: fail: 0 -/
#guard_msgs in #eval do
  IO.println (render (← runProp (forAll (chooseNat 0 0) (fun _ => false) : PropM IO Unit)))

/-- info: fail: 0, x=0 -/
#guard_msgs in #eval do
  IO.println (render (← runProp (forAll (chooseNat 0 0) (fun x => check false s!"x={x}") : PropM IO Unit)))

/- A nested `forAll` adds its own value, outermost first; the inner generator may depend on the
outer value. -/
/-- info: fail: 3, 4 -/
#guard_msgs in #eval do
  IO.println (render (← runProp (forAll (chooseNat 3 3) (fun x =>
    forAll (chooseNat (x + 1) (x + 1)) (fun y => x == y)) : PropM IO Unit)))

/- A discard from the inside is still a discard, not a counterexample. -/
/-- info: discard -/
#guard_msgs in #eval do
  IO.println (render (← runProp (forAll (chooseNat 0 0) (fun _ => assume false) : PropM IO Unit)))

/-! ## Running a campaign

`runCampaign` reports and does not exit, so a failing campaign is `#eval`-able. -/

/-- A property that fails on its first input, with a deterministic counterexample. -/
private def propFail [Gen G] : PropM G Unit :=
  forAll (chooseNat 0 0) (fun _ => false)

/-- A property no input can falsify. -/
private def propPass [Gen G] : PropM G Unit :=
  forAll (chooseNat 0 9) (fun n => n ≤ 9)

/-- A property whose precondition rejects every input. -/
private def propDiscard [Gen G] : PropM G Unit := do
  let n ← generate (chooseNat 0 9)
  assume (n > 9)

/- A counterexample stops the campaign on the input that found it.

The ascription is load-bearing: `runCampaign` wants an `IO TestOutcome`, and unifying that with
`PropM ?G Unit` unfolds `IO` past the monad `Gen IO` is registered for, so `?G` must be named. -/
/-- info: runs=1 discards=0 counterexample=some "0" gaveUp=false -/
#guard_msgs in #eval do IO.println (summary (← runCampaign (propFail : PropM IO Unit) 100))

/- A passing campaign runs its whole budget. -/
/-- info: runs=25 discards=0 counterexample=none gaveUp=false -/
#guard_msgs in #eval do IO.println (summary (← runCampaign (propPass : PropM IO Unit) 25))

/- Discards have their own budget (`maxDiscardRatio * runs`), so they never consume a run — and
exhausting it is a give-up, not a pass. -/
/-- info: runs=0 discards=30 counterexample=none gaveUp=true -/
#guard_msgs in #eval do IO.println (summary (← runCampaign (propDiscard : PropM IO Unit) 10 (maxDiscardRatio := 3)))

/- A property that rejects only *some* inputs still gets every run it asked for. -/
private def propHalfDiscard [Gen G] : PropM G Unit := do
  let n ← generate (chooseNat 0 9)
  assume (n < 5)

/-- info: runs=10 counterexample=none gaveUp=false -/
#guard_msgs in #eval do
  let r ← runCampaign (propHalfDiscard : PropM IO Unit) 10
  IO.println s!"runs={r.runs} counterexample={reprStr r.counterexample?} gaveUp={r.gaveUp}"

/- The same property, tested at `Plausible.Gen` instead: nothing about it changes. -/
/-- info: runs=1 discards=0 counterexample=some "0" gaveUp=false -/
#guard_msgs in #eval do
  IO.println (summary (← runCampaign
    (Plausible.Gen.run (propFail : PropM Plausible.Gen Unit) 0) 100))

/- The failure report: the counterexample, then the run tally, aligned. -/
/--
info:
*** BASALT PROPERTY FAILED ***
counterexample : 0
runs           : 1 (0 discarded)
-/
#guard_msgs in #eval do (← runCampaign (propFail : PropM IO Unit) 100).report "IO"

/- Giving up is reported the same way, so it cannot be read as a pass. -/
/--
info:
*** BASALT PROPERTY FAILED ***
counterexample : none — gave up after 30 discarded inputs
runs           : 0 (30 discarded)
-/
#guard_msgs in #eval do (← runCampaign (propDiscard : PropM IO Unit) 10 (maxDiscardRatio := 3)).report "IO"

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

/-! ## The design document's examples

[Basalt/PBT/README.md](../Basalt/PBT/README.md) claims these compile and pass; only the
counterexample is pinned, since the discard count depends on the draw. -/

private def prop_takeDrop [Gen G] : PropM G Unit := do
  let xs ← generate (listOf (chooseNat 0 99))
  let k ← generate (chooseNat 0 99)
  assume !xs.isEmpty
  check (xs.take k ++ xs.drop k == xs) s!"xs={xs}, k={k}"

/-- info: true -/
#guard_msgs in #eval do
  IO.println (← runCampaign (prop_takeDrop : PropM IO Unit) 50).counterexample?.isNone

open BST in
private def prop_insertMem [Gen G] : PropM G Unit :=
  forAll (Tree.genBST 0 99) fun t =>
    forAll (chooseInt 0 99 (by omega)) fun k =>
      k ∈ (t.insert k).preorder

/-- info: true -/
#guard_msgs in #eval do
  IO.println (← runCampaign (prop_insertMem : PropM IO Unit) 50).counterexample?.isNone
