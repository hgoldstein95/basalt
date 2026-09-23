/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Michael Hicks
-/
import Basalt.Fuzz.Core
import Basalt.PBT.Driver

/-!
# Running a property under libFuzzer

The Lean half of the C bridge in `Basalt/Fuzz/native.c`: `go` hands libFuzzer's driver a per-input
closure, and libFuzzer calls back into `runOneIO` once per mutated input. A failing input is reported
through `Basalt.PBT`'s shared failure contract and then crashes the process, which is how libFuzzer
saves the input as an artifact; `replay` consumes one.
-/

namespace Basalt.Fuzz

open Basalt.PBT

/-- The C bridge: store `run` as the per-input callback, then hand `argv` to libFuzzer's driver.
Blocks in the fuzzing loop; libFuzzer parses its own flags from `argv`. `grow` arms the custom
mutator's buffer extension. Returns only if the campaign completes without a failure (a failure
aborts the process). -/
@[extern "basalt_fuzz_go"]
opaque goImpl (run : ByteArray → IO UInt8) (argv : Array String) (grow : Bool) : IO Unit

/-- Called at the conclusion of a run to report to the C code the deficit in the buffer,
i.e., the difference N - S between requested bytes N and available bytes S. -/
@[extern "basalt_fuzz_note_deficit"]
opaque noteDeficitImpl (deficit : UInt32) : BaseIO Unit

/-- Run the property on one input, reporting the byte codes the C bridge expects: `0` = pass,
`1` = failed (the bridge then aborts, so the report must already be flushed), `2` = discard.

`counters` tallies executions and discards so a failing campaign can report the same run line the
other backends do — libFuzzer's own `#N` markers count only corpus-worthy inputs, which is not the
number of tests run. -/
def runOneIO (counters : IO.Ref (Nat × Nat)) (T : PropM FuzzGen Unit)
    (bytes : ByteArray) : IO UInt8 := do
  let r := runOne T bytes -- run the property test
  noteDeficitImpl (UInt32.ofNatClamp r.deficit) -- note any bytes deficit
  match r.outcome with
  | Except.ok () => counters.modify (fun (runs, discards) => (runs + 1, discards)); pure 0
  | Except.error .discard => counters.modify (fun (r, d) => (r, d + 1)); pure 2
  | Except.error (.fail msg) =>
    counters.modify (fun (runs, discards) => (runs + 1, discards))
    let (runs, discards) ← counters.get
    reportFailure msg
      #[("input bytes", s!"{bytes.toList.map (fun b => b.toNat)}"),
        ("runs", s!"{runs} ({discards} discarded)"),
        ("buffer", s!"{bytes.size} bytes, {r.deficit} short")]
    pure 1

/-- Start a fuzzing campaign for property `T`. `argv` is forwarded to libFuzzer (corpus dirs,
`-runs`, `-max_len`, `-artifact_prefix`, …). A failure aborts the process, with the artifact saved and
the exit code set by libFuzzer.

Report nothing after `goImpl`: libFuzzer's driver `exit()`s when `-runs` is exhausted, so a line
placed there silently never appears — which is why `runOneIO` carries the run tally and the bridge
prints its buffer statistics from an `atexit` handler. -/
def go (T : PropM FuzzGen Unit) (argv : Array String := #[]) (grow : Bool := false) : IO Unit := do
  IO.println s!"[basalt] starting libFuzzer campaign (grow={grow}, {argv.toList})"
  let counters ← IO.mkRef (0, 0)
  goImpl (fun bytes => runOneIO counters T bytes) argv grow

/-- Replay one saved input file against a property (no fuzzer): reproduces the outcome
deterministically and prints it. This is how a saved artifact (`crash-…`) is consumed.

The bytes alone are the whole reproduction: zero-extension is a property of `readByte`, not a
campaign setting, so an artifact means the same thing however it was produced — including one grown
by `--grow`, which is already whatever length the failing run read. -/
def replay (T : PropM FuzzGen Unit) (path : String) : IO Unit := do
  let bytes ← IO.FS.readBinFile path
  IO.println s!"[basalt] replaying {path} ({bytes.size} bytes)"
  let r := runOne T bytes
  match r.outcome with
  | Except.ok () => IO.println s!"outcome: pass ({r.deficit} bytes short)"
  | Except.error .discard => IO.println s!"outcome: discard ({r.deficit} bytes short)"
  | Except.error (.fail msg) => reportFailure msg

/-- Basalt's own fuzz flag, split out of `argv`: libFuzzer rejects a flag it does not recognize, so
what we consume must not be forwarded. -/
def splitFlags (argv : Array String) : Bool × Array String :=
  let grow := argv.contains "--grow"
  let rest := argv.filter (· != "--grow")
  -- `-max_len` bounds the buffer and so bounds the structure growth can build; libFuzzer's own
  -- default derives it from the seed corpus, which is 4096 at a cold start. Left there it, and not
  -- the property, decides how far growth gets.
  let rest := if grow && !rest.any (·.startsWith "-max_len=") then rest.push "-max_len=65536"
              else rest
  -- Linking a custom mutator makes libFuzzer disable its `-len_control` length ramp, which is what
  -- growth wants: the mutator, not the ramp, decides how long an input needs to be. With `--grow`
  -- off there is no mutator decision to make, so restore libFuzzer's own default and leave the
  -- campaign as it was before growth existed. Only an *absent* flag is defaulted — passing
  -- `-len_control=N` explicitly (including `0`) wins, which is how the two modes are compared under
  -- one length regime.
  let rest := if !grow && !rest.any (·.startsWith "-len_control=") then rest.push "-len_control=100"
              else rest
  (grow, rest)

/-- The coverage-guided backend, for `Basalt.PBT.dispatch`. `--grow` is Basalt's own
(`fuzz-run/README.md`); the rest of `argv` goes to libFuzzer, and a saved artifact — which *is* a
`FuzzGen` input buffer — can be replayed. -/
@[basalt_backend]
def fuzzBackend : Backend where
  name := "fuzz"
  campaign T argv := let (grow, rest) := splitFlags argv; go (T FuzzGen) rest grow
  replay? := some (fun T path => replay (T FuzzGen) path)

end Basalt.Fuzz
