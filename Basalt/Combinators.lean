import Basalt.Gen
import Basalt.RandomChoice

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


-- TODO: figure out how we should implement `frequency` (port the helper functions from `Plausible.Gen`?
-- since we want to these generators to be generic over `Gen` and not specifically `Plausible.Gen`)
