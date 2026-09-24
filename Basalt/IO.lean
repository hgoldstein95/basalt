/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt.RandomChoice
import SplitMix.IO

/-!
# The `IO` Interpretation

`RandomChoice IO` draws with `SplitMix.Gen.randNat` on the process-wide `ioGen`, so a running
generator is exactly uniform given the PRNG and a draw allocates nothing.
-/

/-- The generator every `IO` draw advances, seeded from system entropy at initialization; reseed it
with `ioGen.set (SplitMix.ofSeed n)`. Not thread-safe, like the `SplitMix.Gen` it is. -/
initialize ioGen : SplitMix.Gen ← do SplitMix.Gen.new (← SplitMix.newIO)

/-- `IO` is an instance of `RandomChoice` via `SplitMix.Gen.randNat`, whose result carries its own
bound, so the draw needs no clamp. -/
instance : RandomChoice IO where
  choose lo hi h := do
    let ⟨x, hx⟩ ← ioGen.randNat lo hi
    pure (ULift.up ⟨x, by omega⟩)
