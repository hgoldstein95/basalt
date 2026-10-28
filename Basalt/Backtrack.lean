/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Segev Elazar-Mittelman
-/
module

public import Basalt.Fail
public import Basalt.Enum.Finite
public import Basalt.Sized

/-!
# Weighted Backtracking

`backtrack` tries weighted branches in a random order, without replacement, until one does not fail.
It is a class because what that means depends on the interpretation: a search where failure can be
observed (`OptionT G`), and the union of the branches at an enumeration (`Finite`).
-/

@[expose] public section

namespace Basalt

/-- Try the branches, each drawn with probability proportional to its weight among those not yet
tried, until one does not fail; fail if every one does. A branch of weight `0` is never tried.

Not `Alternative`: `x <|> y` tries `x` first, so an enumeration reading it as a union would list
values of `y` its distribution never produces. Here every branch of positive weight is tried first
with positive probability, so its values are exactly the branches' values, and an enumeration may
read it as their union (`EnumeratesSome.backtrack`). -/
class Backtrack (G : Type → Type) where
  backtrack {α : Type} : List (Nat × (Unit → G α)) → G α

namespace Backtrack

variable {G : Type → Type} {α β : Type}

/-- The total weight. -/
def sumWeights (gs : List (Nat × β)) : Nat := (gs.map Prod.fst).sum

/-- The entry whose weight interval contains `n`, its weight, and the others; `none` past the total
weight. -/
def pickDrop : List (Nat × β) → Nat → Option (Nat × β × List (Nat × β))
  | [], _ => none
  | (k, g) :: rest, n =>
    if n < k then some (k, g, rest)
    else (pickDrop rest (n - k)).map fun (k', g', rest') => (k', g', (k, g) :: rest')

open RandomChoice in
/-- The search, with failure observed as `none`: draw a branch by weight, and on `none` draw again
from the rest. Structural on a fuel of the number of branches. -/
def search [Monad G] [RandomChoice G] : Nat → List (Nat × (Unit → OptionT G α)) → OptionT G α
  | _, [] => failure
  | 0, _ => failure
  | fuel + 1, gs@(_ :: _) => OptionT.mk do
    let n ← choose 0 (sumWeights gs - 1) (Nat.zero_le _)
    match pickDrop gs n.down.val with
    | none => pure none
    | some (_, g, rest) =>
      match ← (g ()).run with
      | some a => pure (some a)
      | none => (search fuel rest).run

/-- Where failure is `none`, the search itself. -/
instance instOptionT [Monad G] [RandomChoice G] : Backtrack (OptionT G) where
  backtrack gs := search gs.length gs

/-- At an enumeration, the branches of positive weight, side by side. Running the search here
instead would enumerate the search: one path per unit of weight and per order of retries, each
repeating the values of the branches it tries. -/
instance instFinite : Backtrack Finite where
  backtrack gs := Finite.flatten (gs.filterMap fun (w, g) => if w = 0 then none else some (g ()))

/-- At every size, the backtracking of the branches at that size. -/
instance instWithSize [Backtrack G] : Backtrack (WithSize G) where
  backtrack gs n := Backtrack.backtrack (gs.map fun (w, g) => (w, fun _ => (g ()).run n))

end Backtrack

end Basalt
