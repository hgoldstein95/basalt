import BasaltExamples.ArbChar
import BasaltExamples.ArbNat
import BasaltExamples.ArbList
import BasaltExamples.ArbString
import BasaltExamples.BST
import BasaltExamples.Heap

#guard_msgs(drop info) in
#eval (for _ in [0:20] do
  IO.println <| repr (← ArbChar.Char.arbitrary) : IO Unit)

#guard_msgs(drop info) in
#eval (for _ in [0:20] do
  IO.println <| repr (← ArbNat.Nat.arbitrary) : IO Unit)

#guard_msgs(drop info) in
#eval (for _ in [0:20] do
  IO.println <| repr (← ArbList.List.arbitrary) : IO Unit)

#guard_msgs(drop info) in
#eval (for _ in [0:10] do
  IO.println <| repr (← ArbList.List.arbitrary') : IO Unit)

#guard_msgs(drop info) in
#eval (for _ in [0:10] do
  IO.println <| repr (← ArbString.String.arbitrary) : IO Unit)

/- `genBST` can be run in `IO`. -/
#guard_msgs(drop info) in
#eval (for _ in [0:20] do
  IO.println <| repr (← BST.Tree.genBST 0 10) : IO Unit)

/- `genWeightedBST` can be run in `IO` and indeed generates
    non-empty trees more frequently than leaves (by inspection) -/
#guard_msgs(drop info) in
#eval (for _ in [0:10] do
  IO.println <| repr (← BST.Tree.genWeightedBST 0 10) : IO Unit)

/- `genHeap` can be run in `IO`. -/
#guard_msgs(drop info) in
#eval (for _ in [0:20] do
  IO.println <| repr (← Heap.Tree.genHeap 0) : IO Unit)

/-! ## `UniformIO`

The same generator terms run at the exactly-uniform interpretation. -/

/- `Gen` resolves for `UniformIO`, so any generator term can be interpreted there. -/
example : Gen UniformIO := inferInstance

#guard_msgs(drop info) in
#eval (do
  for _ in [0:20] do
    IO.println <| repr (← ArbNat.Nat.arbitrary) : UniformIO Unit).run

#guard_msgs(drop info) in
#eval (do
  for _ in [0:20] do
    IO.println <| repr (← BST.Tree.genBST 0 10) : UniformIO Unit).run

#guard_msgs(drop info) in
#eval (do
  for _ in [0:20] do
    IO.println <| repr (← Heap.Tree.genHeap 0) : UniformIO Unit).run

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
