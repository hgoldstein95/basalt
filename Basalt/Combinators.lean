import Basalt.Gen
import Basalt.RandomChoice

/-!
# Generator Combinators

This file defines combinators for composing generators: `oneOf` (uniform random selection) and
`frequency` (weighted random selection).

## Monotonicity and `partial_fixpoint`

Recursive generators use `partial_fixpoint` to define coinductive computations. The
`partial_fixpoint` tactic requires an automatic proof that the generator body is monotone with
respect to the CCPO ordering. Lean's core ships `@[partial_fixpoint_monotone]` lemmas for standard
monadic operations (`bind`, `map`, `pure`, `ite`, etc.), and Basalt adds `monotone_pick` in
`RandomChoice.lean`.

To use `oneOf` or `frequency` inside a `partial_fixpoint` definition, corresponding
`@[partial_fixpoint_monotone]` lemmas are needed so the tactic can automatically discharge the
monotonicity obligation. Without them, `partial_fixpoint` will fail with a monotonicity error.

## Main Definitions

- `oneOf` — Picks one of the generators in a list uniformly at random.
- `frequency` — Picks a generator from a weighted list according to the given weights.
- `frequencyAux` — (private) Helper that walks the weight list to select a generator for a given
  random index.
-/

open List

/-- Picks one of the generators in `gs` at random. -/
@[reducible]
def oneOf [Gen G] (gs : List (Unit → G α)) : G α := do
  let i ← ULift.down <$> RandomChoice.choose 0 (gs.length - 1) (by omega)
  gs[i]! ()



/-- `frequencyAux default xs n` chooses a weight & a generator `(k, gen)` from the list `xs` such that `n < k`.
    If `xs` is empty, the `default` generator with weight 0 is returned.  -/
@[reducible]
def frequencyAux [Gen G] (default : G α) (xs : List (Nat × (Unit → G α))) (n : Nat) : Nat × G α :=
  match xs with
  | [] => (0, default)
  | (k, x) :: xs =>
    if n < k then
      (k, x ())
    else
      frequencyAux default xs (n - k)


/-- `frequency` picks a generator from the list `gs` according to the weights in `gs`.
    If `gs` is empty, the `default` generator is returned.  -/
@[reducible]
def frequency [Gen G] (gs : List (Nat × (Unit → G α)))
  (_h : 0 < List.sum (List.map Prod.fst gs) := by omega) : G α := do
  let total := List.sum $ List.map Prod.fst gs
  let n ← ULift.down <$> RandomChoice.choose 0 (total - 1) (by omega)
  (frequencyAux default gs n).snd


