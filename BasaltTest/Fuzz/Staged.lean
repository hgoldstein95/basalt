/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
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
knob. Two shapes, differing in what a stage costs — a specific byte value (`propChain`) or merely a
byte (`propLong`) — so one measures search and the other buffer length.
`fuzz-run/compare-backends.sh` and `fuzz-run/compare-grow.sh` run the comparisons and
`fuzz-run/README.md` records them.

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
def propChain [Gen G] (n : Nat) : PropM G Unit := do
  let mut ok := 0
  for _ in [0:n] do
    if (← generate (chooseNat 0 255)) == needle then ok := ok + 1 else break
  check (ok < n) s!"stages={ok} of {n}"

/-- The second value that ends `propLong`'s run at position `i`, drawn from `[1, 3]` by the top of a
golden-ratio multiplicative hash (`40503 ≈ 2¹⁶/φ`), which is aperiodic over the lengths we run.

It has to *vary* with the position, or one mutation ends the benchmark. A constant terminator leaves
every other byte value acceptable everywhere, so a single `InsertRepeatedBytes` of any acceptable byte
satisfies 128 positions at once — measured: `long-16` then failed in 4 runs. A terminator periodic in
`i` falls the same way to `CopyPart` of an aligned block. -/
def stopAt (i : Nat) : Nat := i * 40503 % 65536 / 21846 + 1

/-- Build a run of elements, ending it at a terminator (`0` or `stopAt i`, so half the draws), and
fail on reaching `n` of them. The benchmark for `--grow` (`fuzz-run/README.md`), and the mirror image
of `propChain`: there a position needs one *specific* byte value out of 256, here it needs one of two
out of four, so per-byte correctness is cheap and the cost that remains is *having* `n` bytes to draw
from.

Zero-extension is what makes it a clean measurement of length, and why `0` terminates at every
position rather than only where the hash says so. Past the end of the buffer every draw is `0`, so a
starved run ends exactly at the end of its buffer and reports a deficit of precisely one byte: "one
more element would have been possible". `len` is therefore bounded by the buffer size, and a blind
sampler needs `2⁻ⁿ` on top of a buffer that long. -/
def propLong [Gen G] (n : Nat) : PropM G Unit := do
  let mut len := 0
  for i in [0:n] do
    let d ← generate (chooseNat 0 3)
    if d == 0 || d == stopAt i then break else len := len + 1
  check (len < n) s!"length={len} of {n}"

end Staged
