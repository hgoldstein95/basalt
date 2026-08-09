/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import BasaltExamples.BST
import BasaltExamples.Heap
import BasaltExamples.ArbString
import BasaltExamples.ArbNat

/-!
# Exercising the `Plausible.Gen` Interpretation

Samples from generators at `Plausible.Gen`, just to make sure the interpretation runs.
-/

/- `genBST` can be run in `PlausibleGen`. -/
#guard_msgs(drop info) in
#eval (for _ in [0:20] do
  IO.println <| repr (← Plausible.Gen.run (BST.Tree.genBST (G := Plausible.Gen) 0 10) 10) : IO Unit)

/- `genHeap` can be run in `PlausibleGen`. -/
#guard_msgs(drop info) in
#eval (for _ in [0:10] do
  IO.println <| repr (← Plausible.Gen.run (Heap.Tree.genHeap (G := Plausible.Gen) 0) 10) : IO Unit)

/- `NonEmptyString.arbitrary` can be run in `PlausibleGen`. -/
#guard_msgs(drop info) in
#eval (for _ in [0:5] do
  IO.println <| repr (← Plausible.Gen.run (ArbString.NonEmptyString.arbitrary (G := Plausible.Gen)) 10) : IO Unit)

/- `nonEmptyListOf Nat.arbirary` can be run in `PlausibleGen`.  -/
#guard_msgs(drop info) in
#eval (for _ in [0:5] do
  IO.println <| repr (← Plausible.Gen.run (nonEmptyListOf ArbNat.Nat.arbitrary (G := Plausible.Gen)) 10) : IO Unit)
