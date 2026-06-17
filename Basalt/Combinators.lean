/-
Copyright (c) 2026 Harrison Goldstein & Ernest Ng. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein & Ernest Ng
-/

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

namespace Helpers

/-- Helper function for the `frequency` combinator:
    `frequencyAux xs n` chooses a weight & a generator `(k, gen)` from the list `xs` such that `n < k`.
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

end Helpers

/-- Generates an element of the list `xs` at random.
    This combinator takes as input a proof that `xs` is non-empty. -/
def elements [Gen G] (xs : List α) (hne : xs ≠ []) : G α := do
  let ⟨i, ⟨ hge, hle ⟩⟩ ← ULift.down <$> RandomChoice.choose 0 (xs.length - 1) (by omega)
  -- Obtain a proof that the list indexing is in-bounds
  have hlen : 0 < xs.length := by
    apply length_pos_iff.mpr
    assumption
  have hlt : i < xs.length := by omega
  return xs[i]'hlt

/-- Picks one of the generators in `gs` at random.
    This combinator takes as input a proof that `xs` is non-empty. -/
def oneOf [Gen G] (gs : List (Unit → G α)) (hne : gs ≠ []) : G α := do
  let ⟨i, ⟨ hge, hle ⟩⟩ ← ULift.down <$> RandomChoice.choose 0 (gs.length - 1) (by omega)
  -- Obtain a proof that the list indexing is in-bounds
  have hlen : 0 < gs.length := by
    apply length_pos_iff.mpr
    assumption
  have hlt : i < gs.length := by omega
  -- This let-definition is necessary, as Lean has trouble parsing `gs[i]'hlt ()`
  let thunked_gen := gs[i]'hlt
  thunked_gen ()

/-- `frequency` picks a generator from the list `gs` according to the weights in `gs`.
    This combinators also takes an additional hypothesis that the sum of the weights
    in the list is non-zero (this is discharged via `omega` by default). -/
def frequency [Gen G] (gs : List (Nat × (Unit → G α)))
  (_h : 0 < List.sum (List.map Prod.fst gs) := by omega) : G α := do
  let total := List.sum $ List.map Prod.fst gs
  let n ← ULift.down <$> RandomChoice.choose 0 (total - 1) (by omega)
  if hn : n < total then Helpers.frequencyAux gs n hn else default
