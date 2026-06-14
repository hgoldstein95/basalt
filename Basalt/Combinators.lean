import Basalt.Gen
import Basalt.Helpers
import Basalt.RandomChoice

open Lean.Order

/-!
# Generator Combinators

This file defines various generator combinators:
- `elements`: generates an element from a non-empty list at random
- `oneOf`: picks from a list of generators uniformly at random selection
- `frequency`: like `oneOf`, but performs weighted random selection
- `frequencyAux`: helper function that traverses the list of weights
   to select a generator for a given random index
-/

open List

/-- Generates an element of the list `xs` at random -/
def elements [Gen G] [Inhabited α] (xs : List α) : G α := do
  let i ← ULift.down <$> RandomChoice.choose 0 (xs.length - 1) (by omega)
  return xs[i]!

/-- Picks one of the generators in `gs` at random. -/
def oneOf [Gen G] (gs : List (Unit → G α)) : G α := do
  let i ← ULift.down <$> RandomChoice.choose 0 (gs.length - 1) (by omega)
  gs[i]! ()

/-- `frequency` picks a generator from the list `gs` according to the weights in `gs`.
    This combinators also takes an additional hypothesis that the sum of the weights
    in the list is non-zero (this is discharged via `omega` by default). -/
def frequency [Gen G] (gs : List (Nat × (Unit → G α)))
  (_h : 0 < List.sum (List.map Prod.fst gs) := by omega) : G α := do
  let total := List.sum $ List.map Prod.fst gs
  let n ← ULift.down <$> RandomChoice.choose 0 (total - 1) (by omega)
  if hn : n < total then frequencyAux gs n hn else default
