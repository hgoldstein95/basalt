/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt.IO
import Basalt.PBT.Property
import BasaltExamples.ArbChar
import BasaltExamples.ArbList
import BasaltExamples.ArbNat
import BasaltExamples.ArbString
import BasaltExamples.BST
import BasaltExamples.BST.Weighted
import BasaltExamples.Heap

/-! # Exercising `IO` Interpretations

Samples from `IO` generators, just to make sure that the interpretations are relatively reasonable.
-/

/-- Run `gen` in `IO` `n` times purely for effect, then report the (deterministic) count. -/
def exercise (n : Nat) (gen : IO α) : IO Unit := do
  for _ in [0:n] do
    let _ ← gen
  IO.println s!"drew {n} samples"

/-! ## The default `IO` interpretation -/

/-- info: drew 10 samples -/
#guard_msgs in #eval exercise 10 ArbChar.Char.arbitrary

/-- info: drew 10 samples -/
#guard_msgs in #eval exercise 10 ArbNat.Nat.arbitrary

/-- info: drew 10 samples -/
#guard_msgs in #eval exercise 10 ArbList.List.arbitrary

/-- info: drew 10 samples -/
#guard_msgs in #eval exercise 10 ArbList.List.arbitrary'

/-- info: drew 10 samples -/
#guard_msgs in #eval exercise 10 ArbString.String.arbitrary

#guard_msgs(drop info) in
#eval (for _ in [0:10] do
  IO.println <| repr (← ArbString.NonEmptyString.arbitrary) : IO Unit)

/- `genBST` can be run in `IO`. -/
/-- info: drew 10 samples -/
#guard_msgs in #eval exercise 10 (BST.Tree.genBST 0 10)

/- `genWeightedBST` can be run in `IO`. -/
/-- info: drew 10 samples -/
#guard_msgs in #eval exercise 10 (BST.Tree.genWeightedBST 0 10)

/- `genHeap` can be run in `IO`. -/
/-- info: drew 10 samples -/
#guard_msgs in #eval exercise 10 (Heap.Tree.genHeap 0)

/- Degenerate, rejection-heavy, and wide ranges all behave: `lo = hi` is forced, a range just past
   a power of two rejects about half its draws, and a range far past `UInt64.MAX` takes SplitMix's
   slow path across several outputs. -/
/-- info: true true true -/
#guard_msgs in
#eval (do
  let a := (← RandomChoice.choose (m := IO) 7 7 (by omega)).down.val
  let mut b := true
  for _ in [0:100] do
    let v := (← RandomChoice.choose (m := IO) 0 (2 ^ 30) (by omega)).down.val
    b := b && v ≤ 2 ^ 30
  let lo : Nat := 2 ^ 70
  let hi : Nat := 2 ^ 70 + 2 ^ 65
  let c := (← RandomChoice.choose (m := IO) lo hi (by omega)).down.val
  IO.println s!"{a == 7} {b} {lo ≤ c && c ≤ hi}" : IO Unit)

/-! ## `IO` executes `IOModel`

`IsFaithful.approx` proves this given `IOModel.IOGenLaws`; here the compiled C is run against the
model. From one seed, `n` runs at `IO` must produce the same values and leave `ioGen` in the same
state as threading that state through `IOModel` by hand. -/

open Basalt.PBT in
private def renderOutcome : TestOutcome → String
  | .ok () => "pass"
  | .error (.fail r) => s!"fail: {r}"
  | .error .discard => "discard"

/-- Whether `n` runs of `x` at `IO` from `seed` agree with `n` steps of `IOModel` from it. -/
def executesModel (x : {G : Type → Type} → [Gen G] → G α) (render : α → String) (n : Nat)
    (seed : UInt64) : IO Bool := do
  ioGen.set (SplitMix.ofSeed seed)
  let executed ← (List.range n).mapM fun _ => x (G := IO)
  let final ← ioGen.get
  let mut s := SplitMix.ofSeed seed
  let mut modeled := #[]
  for _ in [0:n] do
    let some (a, s') := (x (G := IOModel)).run s | return false
    modeled := modeled.push a
    s := s'
  return executed.map render == modeled.toList.map render && final == s

open Basalt.PBT in
/-- info: true -/
#guard_msgs in
#eval do
  let mut ok := true
  for seed in [0, 1, 2026] do
    ok := ok && (← executesModel ArbNat.Nat.arbitrary reprStr 200 seed)
    ok := ok && (← executesModel ArbList.List.arbitrary reprStr 200 seed)
    ok := ok && (← executesModel ArbString.String.arbitrary reprStr 200 seed)
    ok := ok && (← executesModel (BST.Tree.genBST 0 100) reprStr 200 seed)
    ok := ok && (← executesModel (BST.Tree.genWeightedBST 0 100) reprStr 200 seed)
    -- A tuned generator executes code `@[tunable]` builds, with its weights read at runtime.
    ok := ok && (← executesModel (BST.Tree.genWeightedBST.tuned ⟨#[(5, 0), (1, 0)]⟩ 0 100)
      reprStr 200 seed)
    -- Wide and bignum ranges take SplitMix's slow path.
    ok := ok && (← executesModel (chooseNat (2 ^ 70) (2 ^ 70 + 2 ^ 65)) reprStr 200 seed)
    -- A property that fails, discards, and passes: the outcome and its counterexample agree too.
    ok := ok && (← executesModel (runProp (forAll (chooseNat 0 99) fun x => do
      assume (x % 3 != 0)
      check (x < 90) s!"x={x}")) renderOutcome 200 seed)
  IO.println ok

/-! ## `OptionT` over `IO`

The `OptionT` lift (`Basalt/OptionT.lean`) makes any generator monad into one, so `Gen` resolves at
`OptionT G` and every generator term can be reinterpreted there. This is the interpretation of a
filtering generator; a total generator term run through it never fails, so every draw is `some`. -/

example : Gen (OptionT IO) := inferInstance

/-- Run `gen` at `OptionT IO` `n` times and report how many draws succeeded — all of them, for a
total generator. -/
def exerciseOptionT (n : Nat) (gen : OptionT IO α) : IO Unit := do
  let mut somes := 0
  for _ in [0:n] do
    if (← gen.run).isSome then somes := somes + 1
  IO.println s!"{somes}/{n} some"

/-- info: 10/10 some -/
#guard_msgs in #eval exerciseOptionT 10 (ArbNat.Nat.arbitrary : OptionT IO Nat)

/-- info: 10/10 some -/
#guard_msgs in #eval exerciseOptionT 10 (BST.Tree.genBST 0 10 : OptionT IO (BST.Tree Int))
