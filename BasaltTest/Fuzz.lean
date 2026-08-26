/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Michael Hicks
-/
import Basalt.Fuzz.Runner
import Basalt.Combinators
import BasaltExamples.BST
import BasaltFuzz.BuggyBST

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

/-! ### One property, every backend

`basalt-fuzz --backend=` rests on a property being runnable at `FuzzGen`, `IO`, and `Plausible.Gen`
from a single registry entry (`Basalt.Fuzz.Property`). These pin that: a monomorphic property, or a
missing `Gen` instance, is a build failure here rather than a link error in the opt-in executable. -/

private def propAnyBackend : Property := fun _ => do
  let x ← chooseNat 0 9
  checkWith (x ≤ 9) (fun () => s!"x={x}")

/- The registry's own type accepts it, and it runs at all three interpretations. `x ≤ 9` holds for
every draw, so the outcome is `pass` whatever the backend's choices are. -/
/-- info: pass -/
#guard_msgs in #eval IO.println (render (runOne (propAnyBackend FuzzGen) (bytes [4])))

/-- info: pass -/
#guard_msgs in #eval do IO.println (render (← propAnyBackend IO))

/-- info: pass -/
#guard_msgs in #eval do IO.println (render (← Plausible.Gen.run (propAnyBackend Plausible.Gen) 0))

/-! ### The fuzz target's `genBST` is the proved one

`BasaltFuzz/BuggyBST.lean` restates `BasaltExamples/BST`'s `Tree.genBST` instead of importing it,
because importing that module would pull Mathlib into the executable's link closure
(`BasaltFuzz/DESIGN.md` §8). What the copy buys — that the fuzzed generator is the one proved sound,
complete, terminating, and cost-bounded — is only true while the two agree, so it is checked here
rather than asserted in a comment: both are `[Gen G]` terms, so running them at `FuzzGen` on the same
bytes must give the same tree. This test is the reason a drift between them is a build failure. -/

/- Both trees print through a compact `(left key right)` / `.` s-expression rather than `Repr`, so a
pin is one line and a mismatch is legible. Structure is preserved, unlike `toList`, which is not
injective on trees and so would pass on two differently-shaped trees with the same keys. -/
private def showOrig : BST.Tree Nat → String
  | .leaf => "."
  | .node l x r => s!"({showOrig l} {x} {showOrig r})"

private def showCopy : BasaltFuzz.BuggyBST.Tree → String
  | .leaf => "."
  | .node l x r => s!"({showCopy l} {x} {showCopy r})"

/- Runs both generators on one buffer and reports whether the trees coincide, printing the shared
tree so a mismatch shows what each produced rather than just `false`. -/
private def agreeOn (bs : List UInt8) : String :=
  let lo := BasaltFuzz.BuggyBST.loKey
  let hi := BasaltFuzz.BuggyBST.hiKey
  let orig : FuzzGen String := showOrig <$> BST.Tree.genBST lo hi
  let copy : FuzzGen String := showCopy <$> BasaltFuzz.BuggyBST.genBST lo hi
  let run (g : FuzzGen String) : Option String := (g.run ⟨⟨bs.toArray⟩, 0⟩).map (·.1)
  match run orig, run copy with
  | some a, some b => if a == b then s!"agree: {a}" else s!"DIFFER: example={a} fuzz={b}"
  | _, _ => "one generator failed to produce a value"

/- A buffer that drives several `pick`/`chooseNat` steps: both generators consume the bytes in the
same order and build the same tree. -/
/-- info: agree: ((. 3 .) 4 .) -/
#guard_msgs in #eval IO.println (agreeOn [1, 3, 1, 2, 0, 0, 0, 0])

/- The empty buffer takes the zero-fill path in both (`pick` → first branch → `leaf`). -/
/-- info: agree: . -/
#guard_msgs in #eval IO.println (agreeOn [])

/- A longer buffer, exercising deeper recursion on both sides. -/
/-- info: agree: ((. 6 (. 7 .)) 8 .) -/
#guard_msgs in #eval IO.println (agreeOn [1, 7, 1, 5, 0, 1, 6, 0, 0, 1, 9, 0, 0])

/- A tree branching on both sides at depth two, so the pin covers both recursive calls rather than
just the left spine. -/
/-- info: agree: (((. 3 .) 5 .) 9 (. 10 (. 11 .))) -/
#guard_msgs in #eval IO.println (agreeOn [1, 8, 1, 4, 1, 2, 0, 0, 0, 1, 12, 1, 10, 0, 0, 0])
