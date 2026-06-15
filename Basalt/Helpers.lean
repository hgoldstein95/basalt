

import Basalt.Gen

/-!
# Helpers

This file contains some miscellaneous helper functions.

-/

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
