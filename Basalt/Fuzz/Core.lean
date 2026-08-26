/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Michael Hicks
-/
import Basalt.Gen

open Lean.Order

/-!
# The `FuzzGen` interpretation

`FuzzGen` is an executable interpretation of `Gen` whose `choose` results are decided by an external
coverage-guided fuzzer (libFuzzer) rather than by a PRNG: the fuzzer proposes a byte buffer, and
`choose` reads bytes from it to select each value. This is "parametric fuzzing" — the fuzzer
explores the parameter space of choices that defines a generator's output, guided by code coverage.

`choose` is total: it never fails and never limits itself with fuel. Past the end of the buffer it
reads zeros, so a whole fuzzer input is a *pure*, deterministic function `ByteArray → TestOutcome`
(`runOne`). The base monad is `Option` purely to give `partial_fixpoint` an adjoined bottom element
(`none`) — `∀ α, CCPO (FuzzGen α)` has no other source, since the raw state `α × FuzzState` has no
least element for an arbitrary `α`. `none` is a compile-time device only: a productive generator
always yields `some`, and a divergent one loops (caught by libFuzzer's `-timeout`) rather than
returning `none`, so the `none` case is never observed at runtime. Termination is the generator's
own concern (via `partial_fixpoint`).
-/

namespace Basalt.Fuzz

/-- State threaded through one fuzzer input: the fuzzer-controlled byte buffer and a read cursor. -/
structure FuzzState where
  buffer : ByteArray
  cursor : Nat

/-- A fuzzer-driven interpretation of `Gen`: `choose` reads bytes from an externally supplied
buffer. The `Option` base is only a carrier for the `partial_fixpoint` bottom (`none`; see the
module docstring); `choose` is total, so a whole test iteration is a pure function of the input
bytes. -/
abbrev FuzzGen (α : Type) := StateT FuzzState Option α

instance : Inhabited (FuzzGen α) :=
  ⟨fun _ => none⟩

/-! ### Order-theoretic instances on `Option`

A flat order with `none` as bottom, giving `FuzzGen` its `CCPO`/`MonoBind` via the standard `StateT`
lifts — the same recipe as `GenStats`/`Basalt.PlausibleGen`, with `Option` chosen because it *is*
the "adjoin a bottom" construction. -/

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

/-- Read one byte, advancing the cursor. Past the end of the buffer, read `0` (deterministic). -/
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

/-! ### Properties and running one input -/

/-- The result of a property on one input, and of a whole campaign (`Fuzz.go`). Per input: `pass`
(satisfied), `fail` (with a lazily rendered counterexample), `discard` (a precondition rejected it).
Per campaign: `pass` = every executed input passed, `fail` = the counterexample found, `discard` =
no input ever ran a full test. -/
inductive TestOutcome where
  | pass
  | fail (render : Unit → String)
  | discard

/-- The leaf of a property: `pass` iff `b`, with no counterexample detail. -/
def check [Gen G] (b : Bool) : G TestOutcome :=
  pure (if b then .pass else .fail (fun () => "(no counterexample detail)"))

/-- Like `check`, but attaches a rendered counterexample on failure. Build the description from the
values drawn earlier in the `do` block (e.g. `fun () => s!"x={x}, y={y}"`). -/
def checkWith [Gen G] (b : Bool) (render : Unit → String) : G TestOutcome :=
  pure (if b then .pass else .fail render)

/-- A precondition: reject this input (`discard`) unless `c` holds. Inside a property `do` block the
equivalent early-return idiom — `if !c then return .discard` — reads best and short-circuits the
rest; `assume` is the terminal-position convenience. -/
def assume [Gen G] (c : Bool) : G TestOutcome :=
  pure (if c then .pass else .discard)

/-- Single-input convenience. `forAll gen p` is exactly `do let a ← gen; checkWith (p a) (…repr a…)`.

A property is just a `G TestOutcome`, so **you compose inputs with ordinary monadic `do`** — no
special combinator is needed for multiple or dependent inputs, and preconditions are a plain
`return .discard`:

```
def prop [Gen G] : G TestOutcome := do
  let t  ← genTree          -- draw as many inputs as you like, monadically
  let k1 ← chooseNat 0 15
  let k2 ← chooseNat 0 15
  if k1 == k2 then return .discard          -- precondition (short-circuits)
  checkWith (post t k1 k2) (fun () => s!"t={reprStr t}, k1={k1}, k2={k2}")
```

The same term runs at any `Gen` (e.g. `Plausible.Gen`), not just `FuzzGen`. See
`BasaltFuzz/BuggyBST.lean` for worked, runnable examples. -/
def forAll [Repr α] [Gen G] (gen : G α) (p : α → Bool) : G TestOutcome := do
  let a ← gen
  checkWith (p a) (fun () => reprStr a)

/-- Run the property on one input buffer — the pure core the C bridge calls per input. The `none`
case is the `partial_fixpoint` bottom, unreachable for a productive generator (see the module
docstring); we map it to `discard` for totality. -/
def runOne (T : FuzzGen TestOutcome) (bytes : ByteArray) : TestOutcome :=
  match T.run { buffer := bytes, cursor := 0 } with
  | some (outcome, _) => outcome
  | none              => .discard

end Basalt.Fuzz
