import Basalt.Gen
import Basalt.RandomChoice

open Lean.Order

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

### Why `oneOf` needs fixed-arity monotonicity lemmas

A general `monotone_oneOf` theorem for arbitrary-length lists is difficult for two reasons:

1. **Universe constraints**: A general statement like
   `∀ (gs : List (α → m β)), ... → monotone (fun a => oneOf (gs.map ...))` fails to elaborate
   because `Gen (g : Type u → Type v)` allows different input/output universes, while the
   `monotone` definition and `PartialOrder` instances require these to align. The concrete
   fixed-arity versions avoid this because Lean can infer all universes from the literal list.

2. **The tactic works by syntactic matching**: The `partial_fixpoint` tactic looks at the user's
   code and tries to unify it against the conclusion of `@[partial_fixpoint_monotone]` theorems.
   When a user writes `oneOf [fun () => self, fun () => pure 0]`, the tactic sees a literal
   2-element list and matches it against `monotone_oneOf₂`. A single general theorem quantifying
   over `gs : List ...` would require the tactic to decompose the literal list into that abstract
   form, which it cannot do.

## Main Definitions

- `oneOf` — Picks one of the generators in a list uniformly at random.
- `frequency` — Picks a generator from a weighted list according to the given weights.
- `frequencyAux` — (private) Helper that walks the weight list to select a generator for a given
  random index.
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

/-- `oneOf` is monotone if all generators in the list are monotone.
Fixed-arity versions are provided because the `partial_fixpoint` tactic needs to match against
concrete list literals. The proof strategy is the same for all: the `choose` call is constant,
and each list element is either monotone (by hypothesis) or constant (by `monotone_const`).

These are intended to be used in the construction of `partial_fixpoint`, and not meant to be used
otherwise. -/
@[partial_fixpoint_monotone]
theorem monotone_oneOf₂
    [Gen m]
    [∀ α, PartialOrder (m α)]
    [MonoBind m]
    [PartialOrder α]
    {x₁ x₂ : (α → m β)}
    (h₁ : monotone (fun a => x₁ a))
    (h₂ : monotone (fun a => x₂ a)) :
    monotone (fun (a : α) => oneOf [fun () => x₁ a, fun () => x₂ a]) := by
  unfold oneOf
  apply monotone_bind
  · intro _ _ _; apply Lean.Order.PartialOrder.rel_refl
  · refine monotone_of_monotone_apply _ fun i => ?_
    match i with
    | 0 => simp; exact h₁
    | 1 => simp; exact h₂
    | _ + 2 => simp; apply monotone_const

@[partial_fixpoint_monotone]
theorem monotone_oneOf₃
    [Gen m]
    [∀ α, PartialOrder (m α)]
    [MonoBind m]
    [PartialOrder α]
    {x₁ x₂ x₃ : (α → m β)}
    (h₁ : monotone (fun a => x₁ a))
    (h₂ : monotone (fun a => x₂ a))
    (h₃ : monotone (fun a => x₃ a)) :
    monotone (fun (a : α) => oneOf [fun () => x₁ a, fun () => x₂ a, fun () => x₃ a]) := by
  unfold oneOf
  apply monotone_bind
  · intro _ _ _; apply Lean.Order.PartialOrder.rel_refl
  · refine monotone_of_monotone_apply _ fun i => ?_
    match i with
    | 0 => simp; exact h₁
    | 1 => simp; exact h₂
    | 2 => simp; exact h₃
    | _ + 3 => simp; apply monotone_const

/-- `frequencyAux default xs n` chooses a weight & a generator `(k, gen)` from the list `xs` such that `n < k`.
    If `xs` is empty, the `default` generator with weight 0 is returned.  -/
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
def frequency [Gen G] (gs : List (Nat × (Unit → G α)))
  (_h : 0 < List.sum (List.map Prod.fst gs) := by omega) : G α := do
  let total := List.sum $ List.map Prod.fst gs
  let n ← ULift.down <$> RandomChoice.choose 0 (total - 1) (by omega)
  (frequencyAux default gs n).snd
