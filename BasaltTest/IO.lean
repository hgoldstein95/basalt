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

#guard_msgs(drop info) in
#eval (for _ in [0:10] do
  IO.println <| repr (← ArbString.NonEmptyString.arbitrary) : IO Unit)

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
