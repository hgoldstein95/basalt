/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt.RandomChoice
import SplitMix.Native

/-!
# SplitMix's Range Reduction

`SplitMix.randNatRef` is a range reduction over one primitive, `nextUInt64`. Here it is over any
`word`, and `WordModel σ` draws by it from a source of words: on SplitMix's words a draw that
terminates is `randNatRef`'s (`WordModel.choose_run_splitMix`, `Basalt/IO/Approx.lean`), and on
uniform ones it is `SPMF`'s (`Basalt/IO/Choose.lean`).
-/

section via

open Lean.Order

variable {m : Type → Type} [Monad m] (word : m UInt64)

/-- `SplitMix.drawDigits`: one masked leading digit, then `rest` full digits, most significant
first. -/
def drawDigitsVia (mask : UInt64) (rest : Nat) : m Nat := do
  let x ← word
  go (x &&& mask).toNat rest
where
  go (acc : Nat) : Nat → m Nat
    | 0 => pure acc
    | n + 1 => do
      let x ← word
      go ((acc <<< 64) ||| x.toNat) n

/-- `SplitMix.boundedLoop`: redraw `cand` until it is at most `range`. -/
def rejectVia [∀ α, Inhabited (m α)] [∀ α, CCPO (m α)] [MonoBind m] (cand : m Nat) (range : Nat) :
    m {x : Nat // x ≤ range} := do
  let x ← cand
  if h : x ≤ range then pure ⟨x, h⟩ else rejectVia cand range
partial_fixpoint

/-- `SplitMix.randNatRef` on a nonempty range, drawing from `word`. -/
def chooseVia [∀ α, Inhabited (m α)] [∀ α, CCPO (m α)] [MonoBind m] (lo hi : Nat) (h : lo ≤ hi) :
    m (ULift {x : Nat // lo ≤ x ∧ x ≤ hi}) :=
  if lo < hi then
    let shape := SplitMix.rangeShape (hi - lo)
    (fun i => ULift.up ⟨lo + i.val, by omega, by have := i.property; omega⟩) <$>
      rejectVia (drawDigitsVia word shape.1 shape.2) (hi - lo)
  else pure (ULift.up ⟨lo, Nat.le_refl lo, h⟩)

end via

/-- A source of 64-bit words: a PRNG's state and its step. -/
class WordSource (σ : Type) where
  next : σ → UInt64 × σ

instance : WordSource SplitMix := ⟨SplitMix.nextUInt64⟩

/-- Drawing from a word source's state, threaded purely. `none` is divergence, the bottom
`partial_fixpoint` needs. -/
abbrev WordModel (σ : Type) := StateT σ Option

instance : Inhabited (WordModel σ α) := ⟨fun _ => none⟩

/-- A draw is SplitMix's range reduction on the source's words. -/
instance [WordSource σ] : RandomChoice (WordModel σ) where
  choose := chooseVia fun s => some (WordSource.next s)
