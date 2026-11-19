/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Michael Hicks
-/
module

public import Basalt.Fuzz.Encoding
public import Basalt.PBT.Property

/-!
# The `FuzzGen` interpretation

`FuzzGen` is an executable interpretation of `Gen` whose `choose` results are decided by an external
coverage-guided fuzzer rather than by a PRNG: the fuzzer proposes a byte buffer, `choose` reads
bytes from it to select each value, and coverage of the generator and the property guides its
mutations ("parametric fuzzing"). Each `choose` is a *draw*, which has a *range* `[lo, hi]`, the
bytes it reads (the fewest that cover the range, starting at the *cursor*; read big-endian they are
its `raw`), and the *value* it returns, `lo + raw % (hi - lo + 1)`. The cursor so ends a run at the
number of bytes the run read; the byte format, both ways, is `Basalt/Fuzz/Encoding.lean`'s. Because
`choose` is total, a whole fuzzer input is a pure function `ByteArray → FuzzResult` (`runOne`). A
hybrid campaign's random rounds run at a second interpretation, `RecordGen`
(`Basalt/Fuzz/Record.lean`), which draws each value at random and writes bytes that this one decodes
back to it, so that a random test can be handed to libFuzzer as an input.
-/

public section

namespace Basalt.Fuzz

open Basalt.PBT

/-- State threaded through one fuzzer input: the fuzzer-controlled byte buffer and a read cursor.
The cursor is *not* clamped to the buffer, so how far it overshoots is the input's unmet demand
(`FuzzResult.deficit`). -/
structure FuzzState where
  buffer : ByteArray
  cursor : Nat

/-- A fuzzer-driven interpretation of `Gen`: `choose` reads bytes from an externally supplied buffer.

The `Option` base is there to adjoin the bottom element `partial_fixpoint` needs, which the raw state
`α × FuzzState` has no source of for an arbitrary `α`. It is a compile-time device only: a productive
generator always yields `some`, and a divergent one loops (caught by libFuzzer's `-timeout`) rather
than returning `none`. -/
abbrev FuzzGen (α : Type) := StateT FuzzState Option α

instance : Inhabited (FuzzGen α) :=
  ⟨fun _ => none⟩

/-- Read `n` bytes big-endian as a `Nat` at the cursor, and advance it (`readBEFrom`, so `0` past the
end of the buffer). The cursor advances past the end too, so the overshoot survives as the run's
`deficit`. -/
@[expose] def readNat (s : FuzzState) (n : Nat) : Nat × FuzzState :=
  (readBEFrom s.buffer 0 s.cursor n, { s with cursor := s.cursor + n })

/-- `choose` consumes `bytesFor (hi - lo + 1)` bytes and reduces them into `[lo, hi]`. Total. -/
instance : RandomChoice FuzzGen where
  choose lo hi h := do
    let s ← get
    let range := hi - lo + 1
    let (raw, s') := readNat s (bytesFor range)
    set s'
    have := Nat.mod_lt raw (show range > 0 by omega)
    pure (ULift.up ⟨lo + raw % range, by omega⟩)

/-- `FuzzGen` has everything a generator needs. -/
example : Gen FuzzGen := inferInstance

/-- What one input produced: its outcome, and how many bytes it read (`cursor`, past the end
included). -/
structure FuzzResult where
  outcome : TestOutcome
  cursor : Nat
  deriving Inhabited

/-- How many of the bytes a run read its input of `size` bytes did not have: the zeros it read past
the end. -/
@[expose] def FuzzResult.deficit (r : FuzzResult) (size : Nat) : Nat := r.cursor - size

/-- Run a property on one input buffer — the pure core the C bridge calls per input. The `none` case
is the `partial_fixpoint` bottom, unreachable for a productive generator; we map it to `discard` for
totality, with nothing read to report. -/
def runOne (T : PropM FuzzGen Unit) (bytes : ByteArray) : FuzzResult :=
  match (runProp T).run { buffer := bytes, cursor := 0 } with
  | some (outcome, s) => { outcome, cursor := s.cursor }
  | none              => { outcome := Except.error .discard, cursor := 0 }

end Basalt.Fuzz
