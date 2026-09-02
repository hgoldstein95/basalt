/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Michael Hicks
-/
import Basalt.Combinators
import Basalt.PBT.Property

/-!
# A microbenchmark that separates the backends

`BasaltTest/Fuzz/BuggyBST.lean`'s bugs are all *shallow* — one unlucky draw exposes them, so every
backend finds them in tens of runs and a comparison measures nothing. This module is the opposite
case and exists only to be measured: a bug behind a chain of guards, the shape a real bug takes
behind a parser, a magic value, or a sequence of state transitions, but synthetic so the depth is a
knob. `fuzz-run/compare-backends.sh` runs the comparison and `fuzz-run/README.md` records it.

Do not add an import that reaches Mathlib (the `Basalt` umbrella does): the `basalt-fuzz` executable
links this module, and the failure is a native link error from `fuzz-run/build.sh`, not from
`lake build`.
-/

namespace Staged

open Basalt.PBT RandomChoice

/-- The needle each stage must draw. Any fixed value in `[0, 255]` does; the point is that one draw
in 256 advances a stage. -/
abbrev needle : Nat := 7

/-- `n` guards in series: draw a byte, and stop early unless it is `needle`. Fails only when all `n`
draws hit, so a blind sampler needs them at once (`256⁻ⁿ`), while a coverage-guided one banks each
newly-reached guard as coverage and mutates onward from that input, paying roughly `n · 256`.

Do not drop the `break`: it is what nests the guards. Without it every input draws all `n` bytes and
reaches every stage, so no new coverage distinguishes a partial match and the benchmark quietly
degrades to blind search for every backend. -/
def propChain [Gen G] (n : Nat) : G TestOutcome := do
  let mut ok := 0
  for _ in [0:n] do
    if (← chooseNat 0 255) == needle then ok := ok + 1 else break
  checkWith (ok < n) (fun () => s!"stages={ok} of {n}")

end Staged
