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
back to it, so that a random test can be handed to libFuzzer as an input. Under `--cmp` a run also
records its draws' ranges (`FuzzState.trace`), so that the C bridge can find, in an input, a draw to
write a value the program compared into.
-/

public section

namespace Basalt.Fuzz

open Basalt.PBT

/-- State threaded through one fuzzer input: the fuzzer-controlled byte buffer, a read cursor, and,
under `--cmp`, a trace of its draws' ranges. The cursor is *not* clamped to the buffer, so how far
it overshoots is the input's unmet demand (`FuzzResult.deficit`). -/
structure FuzzState where
  buffer : ByteArray
  cursor : Nat
  /-- The ranges of the run's draws, when it records them (`--cmp`, which needs them to find a draw
  in an input to plant a value into): each draw of more than one outcome as two varints
  (`pushVarint`, `Basalt/Fuzz/Encoding.lean`), `lo` and `hi - lo`. The draw's bytes start where the
  previous draw's end, and its value is decoded from them, so neither is recorded; most draws cost
  two bytes. `decode` (`Basalt/Fuzz/Encoding.lean`) recovers the draws from it. -/
  trace : Option ByteArray := none

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

/-- One draw in `[lo, hi]`, `choose`'s step: read `bytesFor (hi - lo + 1)` bytes, and append the
draw's bounds to `FuzzState.trace` if the run records. `raw` is returned; the value is
`lo + raw % (hi - lo + 1)`. -/
@[expose] def drawStep (lo hi : Nat) (s : FuzzState) : Nat × FuzzState :=
  let range := hi - lo + 1
  match s with
  | { buffer, cursor, trace := some t } =>
    -- The trace is taken out of the state before the read, whose result pair would otherwise share
    -- it, so that it is unshared and the pushes happen in place.
    let (raw, s) := readNat { buffer, cursor } (bytesFor range)
    (raw, { s with trace := some (if range ≤ 1 then t else pushVarint (pushVarint t lo) (hi - lo)) })
  | s => readNat s (bytesFor range)

/-- `choose` is one draw (`drawStep`): it reads `bytesFor (hi - lo + 1)` bytes, recording the draw
under `--cmp`, and reduces them into `[lo, hi]`. Total. -/
instance : RandomChoice FuzzGen where
  choose lo hi h := do
    let raw ← modifyGet (drawStep lo hi)
    have := Nat.mod_lt raw (show hi - lo + 1 > 0 by omega)
    pure (ULift.up ⟨lo + raw % (hi - lo + 1), by omega⟩)

/-- `FuzzGen` has everything a generator needs. -/
example : Gen FuzzGen := inferInstance

/-- What one input produced: its outcome, and how many bytes it read (`cursor`, past the end
included). -/
structure FuzzResult where
  outcome : TestOutcome
  cursor : Nat
  /-- The draws' ranges, if recorded (`FuzzState.trace`). -/
  trace : ByteArray := .empty
  deriving Inhabited

/-- How many of the bytes a run read its input of `size` bytes did not have: the zeros it read past
the end. -/
@[expose] def FuzzResult.deficit (r : FuzzResult) (size : Nat) : Nat := r.cursor - size

/-- Run a property on one input buffer — the pure core the C bridge calls per input. The `none` case
is the `partial_fixpoint` bottom, unreachable for a productive generator; we map it to `discard` for
totality, with nothing read to report. `traced` records the draws' ranges. -/
def runOne (T : PropM FuzzGen Unit) (bytes : ByteArray) (traced : Bool := false) : FuzzResult :=
  let s0 : FuzzState :=
    { buffer := bytes, cursor := 0, trace := if traced then some (.emptyWithCapacity 256) else none }
  match (runProp T).run s0 with
  | some (outcome, s) => { outcome, cursor := s.cursor, trace := s.trace.getD .empty }
  | none              => { outcome := Except.error .discard, cursor := 0 }

/-! ## Tracing agrees with `decode`

`decode_drawStep` shows that a run's trace is the format `decode` reads
(`Basalt/Fuzz/Encoding.lean`): each draw a run makes appends exactly that draw to what its trace
decodes to. -/

private theorem bytesFor_one : bytesFor 1 = 0 := by decide

/-- **Decoding agrees with the run, draw by draw.** If a run's trace so far holds the entries `es`
and its cursor is where their bytes end, one more draw in `[lo, hi]` (one `choose`) leaves a trace
that decodes to what it did before, then (for a draw of more than one outcome) the new draw: its
range, its offset (the cursor before it), and the value `choose` returns. Its cursor ends after the
new draw's bytes, so the hypotheses hold again. -/
theorem decode_drawStep (lo hi : Nat) (h : lo ≤ hi) (s : FuzzState) (es : List (Nat × Nat))
    (ht : s.trace = some (encode .empty es)) (hc : s.cursor = offsetAfter es) :
    let r := drawStep lo hi s
    let es' := if hi - lo + 1 ≤ 1 then es else es ++ [(lo, hi - lo)]
    r.2.buffer = s.buffer ∧ r.2.cursor = offsetAfter es' ∧ r.2.trace = some (encode .empty es') ∧
      decode (encode .empty es') s.buffer =
        decode (encode .empty es) s.buffer ++
          (if hi - lo + 1 ≤ 1 then [] else [⟨lo, hi, s.cursor, lo + r.1 % (hi - lo + 1)⟩]) := by
  obtain ⟨buffer, cursor, trace⟩ := s
  simp only at ht hc
  subst ht
  simp only [drawStep, readNat]
  have hoff : ∀ es : List (Nat × Nat), offsetAfter (es ++ [(lo, hi - lo)]) =
      offsetAfter es + bytesFor (hi - lo + 1) := by
    intro es
    induction es with
    | nil => simp [offsetAfter]
    | cons e es ih => obtain ⟨_, _⟩ := e; simp only [List.cons_append, offsetAfter, ih]; omega
  by_cases hr : hi - lo + 1 ≤ 1
  · have : bytesFor (hi - lo + 1) = 0 := by rw [show hi - lo + 1 = 1 by omega]; exact bytesFor_one
    simp [hr, this, hc]
  · simp only [hr, ite_false]
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp
    · simp [hoff, hc]
    · simp [encode_snoc]
    · rw [decode_encode, decode_encode, specFrom_snoc]
      simp [← hc, show lo + (hi - lo) = hi by omega, drawValue]

end Basalt.Fuzz
