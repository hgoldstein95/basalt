import BasaltExamples.BST
import BasaltExamples.Heap

/- `genBST` can be run in `PlausibleGen`. -/
#guard_msgs(drop info) in
#eval (for _ in [0:20] do
  IO.println <| repr (← Plausible.Gen.run (BST.Tree.genBST (G := Plausible.Gen) 0 10) 10) : IO Unit)

/- `genHeap` can be run in `PlausibleGen`. -/
#guard_msgs(drop info) in
#eval (for _ in [0:20] do
  IO.println <| repr (← Plausible.Gen.run (Heap.Tree.genHeap (G := Plausible.Gen) 0) 10) : IO Unit)
