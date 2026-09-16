/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Michael Hicks
-/
import Basalt.Fuzz.Runner
import Basalt.Combinators
import BasaltExamples.BST
import BasaltTest.Fuzz.BuggyBST

/-!
# `FuzzGen` regression tests

Deterministic checks of the byte → choice mapping, run purely (no fuzzer): `runOne` on fixed byte
arrays must produce fixed outcomes. Pins the contract that a corpus byte maps to a specific choice.
-/

open Basalt.Fuzz Basalt.PBT RandomChoice

/-- Build an input buffer from a byte list. -/
private def bytes (l : List UInt8) : ByteArray := ⟨l.toArray⟩

private def render : TestOutcome → String
  | .ok () => "pass"
  | .error (.fail r) => s!"fail: {r}"
  | .error .discard => "discard"

/- A single choice in `[0,9]` consumes one byte and reduces mod 10; the property is `· < 9`. -/
private def propLt9 : PropM FuzzGen Unit := forAll (chooseNat 0 9) (· < 9)

/- Byte `9` → value `9`, so `9 < 9` fails and renders the drawn value. -/
/-- info: fail: 9 -/
#guard_msgs in #eval IO.println (render (runOne propLt9 (bytes [9])))

/- Byte `3` → value `3`. -/
/-- info: pass -/
#guard_msgs in #eval IO.println (render (runOne propLt9 (bytes [3])))

/- Empty buffer takes the zero-extension path → value `0`. -/
/-- info: pass -/
#guard_msgs in #eval IO.println (render (runOne propLt9 (bytes [])))

/- `pick` reads one byte and takes bit 0: even → first branch, odd → second. -/
private def propPick : PropM FuzzGen Unit :=
  forAll (pick (fun () => pure 100) (fun () => pure 200)) (fun n => n == 100)

/- Even byte → first branch. -/
/-- info: pass -/
#guard_msgs in #eval IO.println (render (runOne propPick (bytes [8])))

/- Odd byte → second branch. -/
/-- info: fail: 200 -/
#guard_msgs in #eval IO.println (render (runOne propPick (bytes [9])))

/- A recursive polymorphic generator from `BasaltExamples/` runs at `FuzzGen` and terminates on a
fixed buffer. -/
private def propBSTsizeNonneg : PropM FuzzGen Unit :=
  forAll (BST.Tree.genBST 0 20) (fun t => t.size ≥ 0)

/-- info: pass -/
#guard_msgs in #eval IO.println (render (runOne propBSTsizeNonneg (bytes [1,5,1,3,0,0,0,0])))

/- Two draws (one byte each), a precondition, then `check` — plain monadic `do`. -/
private def propTwo : PropM FuzzGen Unit := do
  let x ← generate (chooseNat 0 9)
  let y ← generate (chooseNat 0 9)
  assume (x != y)
  check (x < y) s!"x={x}, y={y}"

/- Ordered: `x=3, y=7`. -/
/-- info: pass -/
#guard_msgs in #eval IO.println (render (runOne propTwo (bytes [3, 7])))

/- Mis-ordered: `x=7, y=3`, rendering both drawn inputs. -/
/-- info: fail: x=7, y=3 -/
#guard_msgs in #eval IO.println (render (runOne propTwo (bytes [7, 3])))

/- Equal: the precondition rejects the input. -/
/-- info: discard -/
#guard_msgs in #eval IO.println (render (runOne propTwo (bytes [5, 5])))

/-! ### One property, every backend

`basalt-fuzz --backend=` rests on one registry entry (a `Basalt.PBT.Property`) running at `FuzzGen`,
`IO`, and `Plausible.Gen`. These pin that, so a monomorphic property or a missing `Gen` instance is a
build failure here rather than a link error in the opt-in executable. -/

private def propAnyBackend : Property := fun _ => do
  let x ← generate (chooseNat 0 9)
  check (x ≤ 9) s!"x={x}"

/- `x ≤ 9` holds for every draw, so the outcome is `pass` whatever the backend chooses. -/
/-- info: pass -/
#guard_msgs in #eval IO.println (render (runOne (propAnyBackend FuzzGen) (bytes [4])))

/-- info: pass -/
#guard_msgs in #eval do IO.println (render (← runProp (propAnyBackend IO)))

/-- info: pass -/
#guard_msgs in
#eval do IO.println (render (← Plausible.Gen.run (runProp (propAnyBackend Plausible.Gen)) 0))

-- (Omitted on the 4.29 backport: the genBST drift-pins require the Int-keyed BasaltExamples/BST
-- rework, which is unrelated 4.33-line work.)
