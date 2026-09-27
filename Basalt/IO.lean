/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import SplitMix.IO
import Basalt.IO.SplitMix
import Basalt.RandomChoice

/-!
# The `IO` Interpretation

Sampling from a generator with `ioGen`, a C implementation of SplitMix, and what such a run means:
`IOModel`, the same draws on the state threaded purely, which `toIO` runs against `ioGen`. The law
`IsFaithful` (`Basalt/IO/Laws.lean`) relates a generator here to its `SPMF` distribution; what it
leaves out is `idealized_faithful`'s (`Basalt/IO/Faithful.lean`).
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

/-- What running at `IO` means: `ioGen`'s state threaded purely, drawn from as `ioGen` is. -/
abbrev IOModel := WordModel SplitMix

/-- The rest of a run of `toIO`, once the model has run from `ioGen`'s state: the final state
written back and the value returned, or, where the model diverged, `EST.bot`. -/
noncomputable def IOModel.finish : Option (α × SplitMix) → IO α
  | some (a, s') => (ioGen.set s' : IO Unit) >>= fun _ => pure a
  | none => Lean.Order.EST.bot

/-- `m` run from `ioGen`'s current state, which it then writes back with the final state. -/
noncomputable def IOModel.toIO (m : IOModel α) : IO α :=
  (ioGen.get : IO SplitMix) >>= fun s => IOModel.finish (m.run s)
