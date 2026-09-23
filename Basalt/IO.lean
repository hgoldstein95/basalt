/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt.Random
import Basalt.RandomChoice

/-!
# The `IO` Interpretation

`RandomChoice IO` draws with `stdChoose` on `IO.stdGenRef`, so a running generator is exactly
uniform given the PRNG and is seeded by `IO.setRandSeed`.
-/

/-- `IO` is an instance of `RandomChoice` via `stdChoose` on the generator state `IO.rand` uses,
so the draw's bound comes from `stdChoose_mem` instead of a clamp. -/
instance : RandomChoice IO where
  choose lo hi h := do
    let gen ← IO.stdGenRef.get
    let r := stdChoose gen lo hi
    IO.stdGenRef.set r.2
    pure (ULift.up ⟨r.1, stdChoose_mem gen h⟩)
