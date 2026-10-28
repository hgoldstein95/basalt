/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Michael Hicks
-/
module

public import Basalt.Fuzz.Basic
public import Basalt.Fuzz.Cover
public import Basalt.Fuzz.Record
public import Basalt.IO
public import Basalt.PBT.Driver

/-!
# Running a property under libFuzzer

The Lean half of the C bridge in `Basalt/Fuzz/native.c`: `goFuzz` hands libFuzzer's driver a
per-input closure, and libFuzzer calls back into `runOneFuzz` once per mutated input. A failing
input is reported through `Basalt.PBT`'s shared failure contract and then crashes the process, which
is how libFuzzer saves the input as an artifact; `replay` consumes one. `goHybrid` runs a hybrid
campaign in the same loop, alternating fuzzing *rounds* with random ones, whose tests `runOneRandom`
draws at `RecordGen` and whose *finds* become libFuzzer's seeds (`Cover.lean`). The `io-cov` backend
(`ioCovCampaign`) is plain random testing, as the `io` backend does it, but run in this instrumented
executable and recording each test's coverage as a fuzzing campaign does (`BASALT_COV_OUT`), so that
random testing and fuzzing can be compared by the coverage they reach.
-/

public section

namespace Basalt.Fuzz

open Basalt.PBT

/-- The C bridge: store `run` as the per-input callback, then hand `argv` to libFuzzer's driver.
Blocks in the fuzzing loop; libFuzzer parses its own flags from `argv`, and `truncate` arms
`--truncate`. Returns only if the campaign completes without a failure (a failure aborts the
process). -/
@[extern "basalt_fuzz_go"]
opaque goImpl (run : ByteArray → IO UInt8) (argv : Array String) (truncate : Bool) : IO Unit

/-- Before a test of an `io-cov` campaign: clear the coverage counters, as libFuzzer clears them
before each of its runs, so that they count that test alone (`BASALT_COV_OUT`). -/
@[extern "basalt_cov_before_test"]
opaque covBeforeTestImpl : BaseIO Unit

/-- After a test of an `io-cov` campaign: record the edges it hit first (`BASALT_COV_OUT`). -/
@[extern "basalt_cov_after_test"]
opaque covAfterTestImpl : BaseIO Unit

/-- Called at the conclusion of a run to report to the C code how many bytes it read
(`FuzzResult.cursor`), which `--truncate` cuts the next mutation of its input to. -/
@[extern "basalt_fuzz_note_cursor"]
opaque noteCursorImpl (cursor : UInt64) : BaseIO Unit

/-- Count a run's outcome in `counters` and give the C bridge its code: `0` = pass, `1` = failed,
`2` = discard. A failure is reported by `onFail` with the tests run so far (`runs`, then discards)
before `1` is returned, since the bridge then aborts. The tally is kept here because libFuzzer's own
`#N` markers count only corpus-worthy inputs, which is not the number of tests run. -/
def tally (counters : IO.Ref (Nat × Nat)) (outcome : TestOutcome)
    (onFail : String → Nat → Nat → IO Unit) : IO UInt8 := do
  match outcome with
  | Except.ok () => counters.modify (fun (r, d) => (r + 1, d)); pure 0
  | Except.error .discard => counters.modify (fun (r, d) => (r, d + 1)); pure 2
  | Except.error (.fail msg) =>
    counters.modify (fun (r, d) => (r + 1, d))
    let (runs, discards) ← counters.get
    onFail msg runs discards
    pure 1

/-- Run the property on one input, for the C bridge (`tally`). -/
def runOneFuzz (counters : IO.Ref (Nat × Nat)) (T : PropM FuzzGen Unit)
    (bytes : ByteArray) : IO UInt8 := do
  let r := runOne T bytes -- run the property test
  noteCursorImpl r.cursor.toUInt64 -- the bytes it read, for `--truncate`
  tally counters r.outcome fun msg runs discards =>
    reportFailure msg
      #[("input bytes", s!"{bytes.toList.map (fun b => b.toNat)}"),
        ("runs", s!"{runs} ({discards} discarded)"),
        ("buffer", s!"{bytes.size} bytes, {r.deficit bytes.size} short")]

/-- Start a fuzzing campaign for property `T`. `argv` is forwarded to libFuzzer (corpus dirs,
`-runs`, `-max_len`, `-artifact_prefix`, …), and `truncate` arms `--truncate`. `counters?` is the
run and discard tally to count into: a hybrid campaign passes the one its random rounds also count
into, so that a failure reports the tests of both; otherwise it starts at zero. A failure aborts the
process, with the artifact saved and the exit code set by libFuzzer. -/
def goFuzz (T : PropM FuzzGen Unit) (argv : Array String := #[]) (truncate : Bool := false)
    (counters? : Option (IO.Ref (Nat × Nat)) := none) : IO Unit := do
  IO.println s!"[basalt] starting libFuzzer campaign ({argv.toList})"
  -- libFuzzer announces that the linked custom mutator disables `-len_control`; a ramp asked for
  -- explicitly wins over that, so say so.
  if let some lc := flagValue? argv "-len_control=" then
    if lc != "0" then
      IO.println s!"[basalt] -len_control={lc} is explicit and overrides libFuzzer's \
        \"Disabling -len_control by default\""
  let counters ← match counters? with | some c => pure c | none => IO.mkRef (0, 0)
  -- Report nothing after `goImpl`: libFuzzer `exit()`s when `-runs` is exhausted, so a line placed
  -- there silently never appears (the tally lives in `runOneFuzz`, the statistics in an `atexit`).
  goImpl (fun bytes => runOneFuzz counters T bytes) argv truncate

/-- Replay one saved input file against a property (no fuzzer): reproduces the outcome
deterministically and prints it. This is how a saved artifact (`crash-…`) is consumed.

The bytes alone are the whole reproduction: zero-extension is a property of `readByte`, not a
campaign setting, so an artifact means the same thing however it was produced. -/
def replay (T : PropM FuzzGen Unit) (path : String) : IO Unit := do
  let bytes ← IO.FS.readBinFile path
  IO.println s!"[basalt] replaying {path} ({bytes.size} bytes)"
  let r := runOne T bytes
  match r.outcome with
  | Except.ok () => IO.println s!"outcome: pass ({r.deficit bytes.size} bytes short)"
  | Except.error .discard => IO.println s!"outcome: discard ({r.deficit bytes.size} bytes short)"
  | Except.error (.fail msg) => reportFailure msg

/-! ## Hybrid campaigns -/

/-- When a hybrid campaign moves between its random and coverage-guided rounds (`fuzz-run/README.md`,
"Hybrid campaigns"). Every campaign starts random. -/
inductive SwitchRule where
  /-- In both directions, once a round has gone its stale effort without a find. -/
  | stale
  /-- Once, to fuzzing, after this many random tests. -/
  | fixed (tests : Nat)

/-- The bridge's encoding of a rule: the random round's length for `fixed`, `0` for `stale`. -/
def SwitchRule.encode : SwitchRule → UInt64
  | .stale => 0
  | .fixed tests => tests.toUInt64

/-- Check a passed random test for new coverage in the C bridge, given the length of its recorded
bytes: the features it reached that no earlier round did, or none if it reached nothing new. -/
@[extern "basalt_hybrid_judge"]
opaque hybridJudgeImpl (len : UInt64) : BaseIO (Array UInt32)

/-- Arm a hybrid campaign in the C bridge, with `runRandom` as the random rounds' callback, `cover`
as what a switch to fuzzing hands libFuzzer, and the rule as `SwitchRule.encode` gives it. -/
@[extern "basalt_hybrid_config"]
opaque hybridConfigImpl (runRandom : ByteArray → IO UInt8) (cover : IO (Array ByteArray))
    (fixed : UInt64) : IO Unit

/-- One random test, for a random round (`tally`): libFuzzer's buffer is ignored, the run is drawn at
`RecordGen` from `gen`, and a pass that reached new coverage is kept in `finds`. A failure is
reported and its bytes saved under `artifactPrefix` — a `FuzzGen` input, so `replay` reproduces it —
and the bridge exits on the `1` it returns, without letting libFuzzer save the buffer, which is not
this run's input. -/
def runOneRandom (counters : IO.Ref (Nat × Nat)) (T : PropM RecordGen Unit)
    (gen : IO.Ref SplitMix) (finds : IO.Ref (Array Find)) (artifactPrefix : String) (_ : ByteArray) :
    IO UInt8 := do
  let (outcome, bytes, g') := runRecord T (← gen.get)
  gen.set g'
  if outcome matches .ok _ then
    let feats ← hybridJudgeImpl bytes.size.toUInt64
    if !feats.isEmpty then finds.modify (·.push { bytes, feats })
  tally counters outcome fun msg runs discards => do
    let path := s!"{artifactPrefix}crash-random-{runs + discards}"
    let saved ← try IO.FS.writeBinFile path bytes; pure path
      catch e => pure s!"not saved ({e})"
    reportFailure msg
      #[("input bytes", s!"{bytes.toList.map (fun b => b.toNat)}"),
        ("runs", s!"{runs} ({discards} discarded), failing in a random round"),
        ("artifact", saved)]

/-- A hybrid campaign: random and coverage-guided rounds in one libFuzzer loop, switching by `rule`.
Every round's tests count against the one `-runs` budget. -/
def goHybrid (T : Property) (rule : SwitchRule) (argv : Array String) (truncate : Bool) :
    IO Unit := do
  IO.println s!"[basalt] hybrid campaign: random first, then {match rule with
    | .stale => "switching both ways by stale effort"
    | .fixed tests => s!"fuzzing after {tests} tests"}"
  let counters ← IO.mkRef (0, 0)
  let gen ← IO.mkRef (← SplitMix.newIO)
  let artifactPrefix := (flagValue? argv "-artifact_prefix=").getD ""
  let finds ← IO.mkRef #[]
  let seeds := do pure ((cover (← finds.modifyGet (·, #[])).toList).toArray.map (·.bytes))
  hybridConfigImpl (runOneRandom counters (T RecordGen) gen finds artifactPrefix) seeds rule.encode
  goFuzz (T FuzzGen) argv truncate counters

/-- Basalt's flags, parsed. -/
structure FuzzFlags where
  /-- `--truncate`. -/
  truncate : Bool := false
  hybrid : Option SwitchRule := none
  /-- What goes to libFuzzer. -/
  rest : Array String := #[]
  /-- The flags given malformed. -/
  bad : Array String := #[]

/-- Basalt's own fuzz flags, each `--name` or `--name=value`, consumed before libFuzzer sees `argv`,
which rejects a flag it does not recognize. -/
private def ours : List String := ["--truncate", "--hybrid"]

/-- Split Basalt's flags out of `argv`. -/
def splitFlags (argv : Array String) : FuzzFlags :=
  let rule : Except String (Option SwitchRule) :=
    if !argv.any (isFlag "--hybrid") then .ok none
    else match flagValue? argv "--hybrid=" with
    | none => .ok (some .stale)
    | some v => match v.toNat? with
      | some n => if n > 0 then .ok (some (.fixed n)) else .error "--hybrid"
      | none => .error "--hybrid"
  let isOurs (a : String) := ours.any (isFlag · a)
  let f : FuzzFlags := { truncate := argv.contains "--truncate", rest := argv.filter (!isOurs ·),
                         bad := argv.filter fun a => (flagArg? "--truncate=" a).isSome }
  match rule with
  | .ok r => { f with hybrid := r }
  | .error n => { f with bad := f.bad.push n }

/-- Basalt's length regime, each flag only if `argv` does not set it: no `-len_control` ramp (as
libFuzzer already has it once a custom mutator is linked) and a `-max_len` of 64 KB, so an input can
grow as long as its generator reads (`fuzz-run/README.md`, "Truncation"). -/
def withDefaults (argv : Array String) : Array String :=
  let set (flag value : String) (a : Array String) :=
    if (flagValue? a flag).isSome then a else a.push (flag ++ value)
  argv |> set "-len_control=" "0" |> set "-max_len=" "65536"

/-- The coverage-guided backend, for `Basalt.PBT.dispatch`. `--truncate` and `--hybrid` are Basalt's own
(`fuzz-run/README.md`); the rest of `argv` goes to libFuzzer, and a saved artifact — which *is* a
`FuzzGen` input buffer — can be replayed. -/
@[basalt_backend]
def fuzzBackend : Backend where
  name := "fuzz"
  flags := ours
  campaign T argv := do
    let f := splitFlags argv
    if !f.bad.isEmpty then
      usageError s!"malformed: {f.bad.toList}; --truncate takes no value, --hybrid nothing or a \
        positive number of tests"
    match f.hybrid with
    | some rule => goHybrid T rule (withDefaults f.rest) f.truncate
    | none => goFuzz (T FuzzGen) (withDefaults f.rest) f.truncate
  replay? := some (fun T path => replay (T FuzzGen) path)

/-- Random testing at `IO`, as the `io` backend does it, with each test's coverage counted the way
`fuzz` counts it (`BASALT_COV_OUT`): the baseline a fuzzing campaign's coverage is compared
against, in the same instrumented binary, with only the source of the choices changed. -/
def ioCovCampaign (T : Property) (argv : Array String) : IO Unit :=
  campaign "IO (coverage counted)"
    (do covBeforeTestImpl; let o ← runProp (T IO); covAfterTestImpl; pure o)
    (runsOf argv) (discardRatioOf argv)

@[basalt_backend]
def ioCovBackend : Backend where
  name := "io-cov"
  campaign T argv := ioCovCampaign T argv

end Basalt.Fuzz
