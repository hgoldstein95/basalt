/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt.RandomChoice

open RandomChoice

/-!
# IO Interpretation

This file establishes the infrastructure necessary to make a `Gen` instance for `IO`.

## Main Definitions

- `RandomChoice IO` — The only definiton needed is `choose`, which is implemented simply via
  `IO.rand`.
-/

/-- `IO` is an instance of `RandomChoice` via `IO.rand`. -/
instance : RandomChoice IO where
  choose lo hi h := do
    let r ← IO.rand lo hi
    pure (ULift.up ⟨min hi (max lo r), by omega⟩)
