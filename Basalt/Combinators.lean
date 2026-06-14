import Basalt.Gen
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

/-- `frequencyAux default xs n` chooses a weight & a generator `(k, gen)` from the list `xs` such that `n < k`.
     This function expects a proof `h : n < sum(xs)`, which makes the empty-list case in
     the pattern-match irrefutable, since `n < 0` is `False` (this is discharged
     immediately by `contradiction`). -/
def frequencyAux [Gen G] (xs : List (Nat × (Unit → G α))) (n : Nat)
    (h : n < List.sum (List.map Prod.fst xs)) : G α :=
  match xs with
  | [] => by contradiction
  | (k, x) :: xs =>
    if hlt : n < k then
      x ()
    else
      frequencyAux xs (n - k) (by dsimp at h; omega)

/-- `frequency` picks a generator from the list `gs` according to the weights in `gs`.
    This combinators also takes an additional hypothesis that the sum of the weights
    in the list is non-zero (this is discharged via `omega` by default). -/
def frequency [Gen G] (gs : List (Nat × (Unit → G α)))
  (_h : 0 < List.sum (List.map Prod.fst gs) := by omega) : G α := do
  let total := List.sum $ List.map Prod.fst gs
  let n ← ULift.down <$> RandomChoice.choose 0 (total - 1) (by omega)
  -- Note: `n % total = n`, since `n` is returned from `RandomChoice.0 (total - 1)`,
  -- so we know that `n < total`
  frequencyAux gs (n % total) (by apply Nat.mod_lt; assumption)
