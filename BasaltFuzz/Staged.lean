/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Michael Hicks
-/
import Basalt.Combinators
import Basalt.Fuzz.Core

/-!
# A microbenchmark that separates the backends

`BasaltFuzz/BuggyBST.lean`'s bugs are all *shallow*: one unlucky draw exposes them, so every backend finds
them in tens of runs and a comparison between backends measures nothing. This module is the opposite
case, and exists only to be measured — a bug behind a chain of guards, where each guard must be
satisfied before the next is even reached.

That shape is what coverage guidance is for. A blind draw needs all `n` guards to hit at once
(probability `256⁻ⁿ`); a coverage-guided fuzzer sees each newly-reached guard as new coverage, saves
that input, and mutates onward from it — so it banks one guard at a time and pays roughly `n · 256`
instead of `256ⁿ`. `fuzz-run/compare-backends.sh` measures the gap; `fuzz-run/README.md` records it.

Real programs have this shape wherever a bug sits behind a parser, a magic value, or a sequence of
state transitions. It is synthetic here so the exponent is a knob rather than a guess.
-/

namespace BasaltFuzz.Staged

open Basalt.Fuzz RandomChoice

/-- The needle each stage must draw. Any fixed value in `[0, 255]` does; the point is that one draw
in 256 advances a stage. -/
abbrev needle : Nat := 7

/-- `n` guards in series: draw a byte, and stop early unless it is `needle`. Fails only when all `n`
draws hit, so the failure is `256ⁿ` deep for a blind sampler but reachable incrementally by one that
gets credit for each stage it newly reaches.

The `break` is load-bearing: it is what makes the guards *nested* rather than independent. Without it
all `n` bytes would be drawn every run, each stage would be reached on every input, and no new
coverage would distinguish a partial match — collapsing the benchmark to blind search for every
backend. -/
def propChain [Gen G] (n : Nat) : G TestOutcome := do
  let mut ok := 0
  for _ in [0:n] do
    if (← chooseNat 0 255) == needle then ok := ok + 1 else break
  checkWith (ok < n) (fun () => s!"stages={ok} of {n}")

end BasaltFuzz.Staged
