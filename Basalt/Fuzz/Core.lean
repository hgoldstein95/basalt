/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Michael Hicks
-/
import Basalt.PBT.Property

open Lean.Order

/-!
# The `FuzzGen` interpretation

`FuzzGen` is an executable interpretation of `Gen` whose `choose` results are decided by an external
coverage-guided fuzzer rather than by a PRNG: the fuzzer proposes a byte buffer, `choose` reads bytes
from it to select each value, and coverage of the generator and the property guides its mutations
("parametric fuzzing"). Because `choose` is total, a whole fuzzer input is a pure function
`ByteArray → TestOutcome` (`runOne`).
-/

namespace Basalt.Fuzz

open Basalt.PBT

/-- State threaded through one fuzzer input: the fuzzer-controlled byte buffer and a read cursor. -/
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

/-! ### `Option` as a flat order with `none` as bottom -/

instance instPartialOrderOption : PartialOrder (Option α) :=
  FlatOrder.instOrder (b := none)

instance instCCPOOption : CCPO (Option α) :=
  FlatOrder.instCCPO (b := none)

instance : MonoBind Option where
  bind_mono_left h := by
    cases h with
    | bot => exact FlatOrder.rel.bot
    | refl => exact FlatOrder.rel.refl
  bind_mono_right h := by
    cases ‹Option _› with
    | none => exact FlatOrder.rel.refl
    | some a => exact h a

/-! ### Reading choices from the byte buffer -/

/-- Bits needed to distinguish `k` outcomes (0 when `k ≤ 1`). -/
def bitsFor (k : Nat) : Nat :=
  if k ≤ 1 then 0 else (k - 1).log2 + 1

/-- Bytes needed to distinguish `k` outcomes: the smallest count covering `bitsFor k`. Reading the
*fewest* bytes per range keeps a tight, mutation-friendly map from input bytes to choices. -/
def bytesFor (k : Nat) : Nat := (bitsFor k + 7) / 8

/-- Read one byte, advancing the cursor. Past the end of the buffer, read `0`: the buffer is
zero-extended rather than exhausted, which is what keeps `choose` total (`fuzz-run/README.md` records
what this costs and what a custom mutator would buy instead). -/
def readByte (s : FuzzState) : UInt8 × FuzzState :=
  let b := if s.cursor < s.buffer.size then s.buffer.get! s.cursor else 0
  (b, { s with cursor := s.cursor + 1 })

/-- Read `n` bytes big-endian as a `Nat`, advancing the cursor (zero-filling past end-of-buffer). -/
def readNat (s : FuzzState) (n : Nat) : Nat × FuzzState := Id.run do
  let mut acc := 0
  let mut st := s
  for _ in [0:n] do
    let (b, st') := readByte st
    acc := acc * 256 + b.toNat
    st := st'
  return (acc, st)

/-- `choose` consumes `bytesFor (hi - lo + 1)` bytes and reduces them into `[lo, hi]`. Total. -/
instance : RandomChoice FuzzGen where
  choose lo hi h := do
    let s ← get
    let range := hi - lo + 1
    let (raw, s') := readNat s (bytesFor range)
    set s'
    let v := lo + raw % range
    pure (ULift.up ⟨min hi (max lo v), by omega⟩)

/-- `FuzzGen` has everything a generator needs. -/
example : Gen FuzzGen := inferInstance

/-- Run a property on one input buffer — the pure core the C bridge calls per input. The `none` case
is the `partial_fixpoint` bottom, unreachable for a productive generator; we map it to `discard` for
totality. -/
def runOne (T : FuzzGen TestOutcome) (bytes : ByteArray) : TestOutcome :=
  match T.run { buffer := bytes, cursor := 0 } with
  | some (outcome, _) => outcome
  | none              => .discard

end Basalt.Fuzz
