import BasaltExamples.BST
import BasaltExamples.Heap
import BasaltExamples.ArbString
import BasaltExamples.ArbNat

/- `genBST` can be run in `PlausibleGen`. -/
#guard_msgs(drop info) in
#eval (for _ in [0:20] do
  IO.println <| repr (← Plausible.Gen.run (BST.Tree.genBST (G := Plausible.Gen) 0 10) 10) : IO Unit)

/- `genHeap` can be run in `PlausibleGen`.
    Note: on Lean 4.29 (where the Lean interpreter's default stack size is smaller compared to Lean 4.33),
    trying to run this generator with `fuel = 10` causes stack overflow, so on Lean 4.29,
    we lower the fuel to 3. -/
#guard_msgs(drop info) in
#eval (for _ in [0:10] do
  IO.println <| repr (← Plausible.Gen.run (Heap.Tree.genHeap (G := Plausible.Gen) 0) 3) : IO Unit)

/- `NonEmptyString.arbitrary` can be run in `PlausibleGen`. -/
#guard_msgs(drop info) in
#eval (for _ in [0:5] do
  IO.println <| repr (← Plausible.Gen.run (ArbString.NonEmptyString.arbitrary (G := Plausible.Gen)) 10) : IO Unit)

/- `nonEmptyListOf Nat.arbirary` can be run in `PlausibleGen`.  -/
#guard_msgs(drop info) in
#eval (for _ in [0:5] do
  IO.println <| repr (← Plausible.Gen.run (nonEmptyListOf ArbNat.Nat.arbitrary (G := Plausible.Gen)) 10) : IO Unit)
