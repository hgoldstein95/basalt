import BasaltExamples.ArbChar
import BasaltExamples.ArbNat
import BasaltExamples.ArbList
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

/- `genBST` can be run in `IO`. -/
/-- info: drew 10 samples -/
#guard_msgs in #eval exercise 10 (BST.Tree.genBST 0 10)

/- `genWeightedBST` can be run in `IO`. -/
/-- info: drew 10 samples -/
#guard_msgs in #eval exercise 10 (BST.Tree.genWeightedBST 0 10)

/- `genHeap` can be run in `IO`. -/
/-- info: drew 10 samples -/
#guard_msgs in #eval exercise 10 (Heap.Tree.genHeap 0)

/-! ## `UniformIO`

The same generator terms run at the exactly-uniform interpretation. -/

/-- `Gen` resolves for `UniformIO`, so any generator term can be interpreted there. -/
example : Gen UniformIO := inferInstance

/-- info: drew 10 samples -/
#guard_msgs in #eval exercise 10 (ArbNat.Nat.arbitrary : UniformIO Nat).run

/-- info: drew 10 samples -/
#guard_msgs in #eval exercise 10 (BST.Tree.genBST 0 10 : UniformIO (BST.Tree Nat)).run

/-- info: drew 10 samples -/
#guard_msgs in #eval exercise 10 (Heap.Tree.genHeap 0 : UniformIO Heap.Tree).run

/- Degenerate and wide ranges both behave: `lo = hi` is forced, and a range far past
   `UInt64.MAX` still lands in bounds. -/
/-- info: true true -/
#guard_msgs in
#eval (do
  let a := (← RandomChoice.choose (m := UniformIO) 7 7 (by omega)).down.val
  let lo : Nat := 2 ^ 70
  let hi : Nat := 2 ^ 70 + 2 ^ 65
  let b := (← RandomChoice.choose (m := UniformIO) lo hi (by omega)).down.val
  IO.println s!"{a == 7} {lo ≤ b && b ≤ hi}" : UniformIO Unit).run
