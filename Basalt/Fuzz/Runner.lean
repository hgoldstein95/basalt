/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All rights reserved.
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
Blocks in the fuzzing loop; libFuzzer parses its own flags from `argv`. Returns only if the campaign
completes without a failure (a failure aborts the process). -/
@[extern "basalt_fuzz_go"]
opaque goImpl (run : ByteArray → IO UInt8) (argv : Array String) : IO Unit

/-- Run the property on one input, reporting the byte codes the C bridge expects: `0` = pass,
`1` = failed (the bridge then aborts, so the report must already be flushed), `2` = discard.

`counters` tallies executions and discards so a failing campaign can report the same run line the
other backends do — libFuzzer's own `#N` markers count only corpus-worthy inputs, which is not the
number of tests run. -/
def runOneIO (counters : IO.Ref (Nat × Nat)) (T : FuzzGen TestOutcome) (bytes : ByteArray) :
    IO UInt8 := do
  counters.modify (fun (runs, discards) => (runs + 1, discards))
  match runOne T bytes with
  | .pass => pure 0
  | .discard => counters.modify (fun (r, d) => (r, d + 1)); pure 2
  | .fail render =>
    let (runs, discards) ← counters.get
    reportFailure (render ())
      #[("input bytes", s!"{bytes.toList.map (fun b => b.toNat)}"),
        ("runs", s!"{runs} ({discards} discarded)")]
    pure 1

/-- Start a fuzzing campaign for property `T`. `argv` is forwarded to libFuzzer (corpus dirs,
`-runs`, `-max_len`, `-artifact_prefix`, …). A failure aborts the process, with the artifact saved and
the exit code set by libFuzzer.

Nothing may be reported after `goImpl`: libFuzzer's driver calls `exit()` when `-runs` is exhausted,
so a line placed there never appears. That is why the run tally is reported by `runOneIO`. -/
def go (T : FuzzGen TestOutcome) (argv : Array String := #[]) : IO Unit := do
  IO.println s!"[basalt] starting libFuzzer campaign ({argv.toList})"
  let counters ← IO.mkRef (0, 0)
  goImpl (fun bytes => runOneIO counters T bytes) argv

/-- Replay one saved input file against a property (no fuzzer): reproduces the outcome
deterministically and prints it. This is how a saved artifact (`crash-…`) is consumed. -/
def replay (T : FuzzGen TestOutcome) (path : String) : IO Unit := do
  let bytes ← IO.FS.readBinFile path
  IO.println s!"[basalt] replaying {path} ({bytes.size} bytes)"
  match runOne T bytes with
  | .pass => IO.println "outcome: pass"
  | .discard => IO.println "outcome: discard"
  | .fail render => reportFailure (render ())

/-- The coverage-guided backend, for `Basalt.PBT.dispatch`. All of `argv` goes to libFuzzer, and a
saved artifact — which *is* a `FuzzGen` input buffer — can be replayed. -/
def fuzzBackend : Backend where
  name := "fuzz"
  campaign T argv := go (T FuzzGen) argv
  replay? := some (fun T path => replay (T FuzzGen) path)

end Basalt.Fuzz
