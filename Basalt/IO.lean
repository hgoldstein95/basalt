/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt.RandomChoice

open RandomChoice

/-!
# IO Interpretations

This file establishes the infrastructure necessary to make a `Gen` instance for `IO`.

There are two `IO`-flavored interpretations:

| monad | `choose` via | uniform? | draws per `choose` |
|---|---|---|---|
| `IO` | `IO.rand` | to within `1 ± 1/1000` | 1 while `k ≲ 2^21`, more beyond |
| `UniformIO` | `IO.getRandomBytes` + rejection | exactly | 1 per attempt, expected `< 2` |

`IO` remains the default because it is fast: a pure PRNG step, no syscall. `UniformIO` is the
interpretation to reach for when you want the running generator to actually match what the `SPMF`
interpretation says it does.

## Main Definitions

- `RandomChoice IO` — the default, via `IO.rand`.
- `UniformIO` — an `IO` synonym whose `RandomChoice` instance is exactly uniform.
- `UniformIO.run` — recover the underlying `IO` action.
-/

/-- `IO` is an instance of `RandomChoice` via `IO.rand`. -/
instance : RandomChoice IO where
  choose lo hi h := do
    let r ← IO.rand lo hi
    pure (ULift.up ⟨min hi (max lo r), by omega⟩)

/-! ## The exactly-uniform interpretation -/

/-- `IO`, reinterpreted so that `choose` is exactly uniform. -/
def UniformIO (α : Type) : Type := IO α

namespace UniformIO

instance : ∀ α, Inhabited (UniformIO α) := fun _ => inferInstanceAs (Inhabited (IO _))
instance : Monad UniformIO := inferInstanceAs (Monad IO)
instance : ∀ α, Lean.Order.CCPO (UniformIO α) := fun _ => inferInstanceAs (Lean.Order.CCPO (IO _))
instance : Lean.Order.MonoBind UniformIO := inferInstanceAs (Lean.Order.MonoBind IO)

/-- Recover the underlying `IO` action. -/
def run (x : UniformIO α) : IO α := x

/-- The number of bits needed to represent every value `< k`. Zero when `k ≤ 1`, since a single
  possible outcome carries no information. -/
def bitsFor (k : Nat) : Nat :=
  if k ≤ 1 then 0 else (k - 1).log2 + 1

/-- Interpret a `ByteArray` as a big-endian natural number. -/
def natFromBytes (bs : ByteArray) : Nat :=
  bs.foldl (fun acc b => acc * 256 + b.toNat) 0

/-- Draw a uniform value in `[0, k)` by rejection sampling over `IO.getRandomBytes`. -/
partial def uniformLt (k : Nat) : IO Nat := do
  let n := bitsFor k
  let nbytes := (n + 7) / 8
  let rec loop : IO Nat := do
    let bs ← IO.getRandomBytes nbytes.toUSize
    let v := natFromBytes bs % 2 ^ n
    if v < k then pure v else loop
  loop

/-- `UniformIO` draws by rejection sampling over `IO.getRandomBytes`, so each value is exactly
  uniform and each attempt is exactly one read from the OS entropy source. -/
instance : RandomChoice UniformIO where
  choose lo hi h := do
    let v ← uniformLt (hi - lo + 1)
    pure (ULift.up ⟨min hi (lo + v), by omega⟩)

end UniformIO
