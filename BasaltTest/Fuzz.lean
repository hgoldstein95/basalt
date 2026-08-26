/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Michael Hicks
-/
import Basalt.Fuzz.Core
import Basalt.Combinators
import BasaltExamples.BST

/-!
# `FuzzGen` regression tests

Deterministic checks of the byte → choice mapping, run purely (no fuzzer): `runOne` on fixed byte
arrays must produce fixed outcomes. Pins the contract that a corpus byte maps to a specific choice.
-/

open Basalt.Fuzz RandomChoice

/-- Build an input buffer from a byte list. -/
private def bytes (l : List UInt8) : ByteArray := ⟨l.toArray⟩

private def render : TestOutcome → String
  | .pass => "pass"
  | .fail r => s!"fail: {r ()}"
  | .discard => "discard"

/- A single choice in `[0,9]` consumes one byte and reduces mod 10; the property is `· < 9`. -/
private def propLt9 : FuzzGen TestOutcome := forAll (chooseNat 0 9) (· < 9)

/- Byte `9` → value `9` → property `9 < 9` fails, and the counterexample renders as `9`. -/
/-- info: fail: 9 -/
#guard_msgs in #eval IO.println (render (runOne propLt9 (bytes [9])))

/- Byte `3` → value `3` → passes. -/
/-- info: pass -/
#guard_msgs in #eval IO.println (render (runOne propLt9 (bytes [3])))

/- Empty buffer with the `zero` fallback → value `0` → passes. -/
/-- info: pass -/
#guard_msgs in #eval IO.println (render (runOne propLt9 (bytes [])))

/- `pick` reads one byte and takes bit 0: even → first branch, odd → second. -/
private def propPick : FuzzGen TestOutcome :=
  forAll (pick (fun () => pure 100) (fun () => pure 200)) (fun n => n == 100)

/- Even byte selects the first branch (`100`), so `n == 100` holds. -/
/-- info: pass -/
#guard_msgs in #eval IO.println (render (runOne propPick (bytes [8])))

/- Odd byte selects the second branch (`200`), so `n == 100` fails. -/
/-- info: fail: 200 -/
#guard_msgs in #eval IO.println (render (runOne propPick (bytes [9])))

/- The same polymorphic generator (`genBST`) runs at `FuzzGen`; a correct property never fails. -/
private def propBSTsizeNonneg : FuzzGen TestOutcome :=
  forAll (BST.Tree.genBST 0 20) (fun t => t.size ≥ 0)

/- A run driven by a fixed buffer terminates with `pass`. -/
/-- info: pass -/
#guard_msgs in #eval IO.println (render (runOne propBSTsizeNonneg (bytes [1,5,1,3,0,0,0,0])))

/- Composition: a two-input property with a precondition, built with ordinary monadic `do` — two
`chooseNat 0 9` draws (one byte each), an equality precondition, then `checkWith (x < y)`. -/
private def propTwo : FuzzGen TestOutcome := do
  let x ← chooseNat 0 9
  let y ← chooseNat 0 9
  if x == y then return .discard
  checkWith (x < y) (fun () => s!"x={x}, y={y}")

/- Distinct, ordered: bytes `3,7` → `x=3,y=7` → `3 < 7` holds. -/
/-- info: pass -/
#guard_msgs in #eval IO.println (render (runOne propTwo (bytes [3, 7])))

/- Distinct, mis-ordered: bytes `7,3` → `x=7,y=3` → fails, rendering both drawn inputs. -/
/-- info: fail: x=7, y=3 -/
#guard_msgs in #eval IO.println (render (runOne propTwo (bytes [7, 3])))

/- Equal: bytes `5,5` → the precondition rejects the input (`discard`). -/
/-- info: discard -/
#guard_msgs in #eval IO.println (render (runOne propTwo (bytes [5, 5])))
