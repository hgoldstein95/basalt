import Basalt.RandomChoice

open Lean.Order

/-!
# Generator Representation

This file defines the top-level interface of PBT generators.
-/

/-- Our representation of generators abstracts over a number of type-classes, each of which provides
  some important set of generator operations:
- `Monad`: Generators compose monadically.
- `RandomChoice`: Generators can express discrete random choices.
- `Inhabited`: Generators can fail; there is a bottom value that represents non-termination and
  other failures.
- `CCPO` and `MonoBind`: Generators are partially-ordered and admit Knaster-Tarski fixed-points.
  Generators that do not terminate structurally, or at all, are still expressable. (The monad's bind
  operation should respect the partial order.)

**NOTE**: I'm not sure this is actually right. This doesn't work well with higher-order generators,
and it also makes `Gen` a `Type → Type 1`, which feels odd.
-/
def Gen (α : Type) :=
  ∀ {m : Type → Type}
    [∀ α, Inhabited (m α)]
    [Monad m]
    [RandomChoice m]
    [∀ α, CCPO (m α)]
    [MonoBind m],
    m α
