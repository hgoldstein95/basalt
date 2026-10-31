/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
module

public import Basalt.Gen

/-!
# A Relation Between Two Monads

`GenRel M N R` says the relation `R` between generators at `M` and at `N` is closed under the host
constructs, a draw, `default` on the `M` side, and fixpoint induction on it. It sits below the
generator walker, whose registries name it (`Basalt/Walk/Attr.lean`); what follows from it is in
`Basalt/GenRel.lean`.
-/

public section

/-- `R` relates one generator at `M` and at `N` construct by construct. `admissible` is what
fixpoint induction on the `M` side asks, for a recursive combinator. -/
structure GenRel (M N : Type → Type) [Gen M] [Gen N] (R : ∀ {α : Type}, M α → N α → Prop) :
    Prop where
  pure : ∀ {α : Type} (a : α), R (Pure.pure a) (Pure.pure a)
  bind : ∀ {α β : Type} {y : M α} {x : N α} {k' : α → M β} {k : α → N β},
    (∀ a, R (k' a) (k a)) → R y x → R (y >>= k') (x >>= k)
  map : ∀ {α β : Type} {y : M α} {x : N α} (f : α → β), R y x → R (f <$> y) (f <$> x)
  default : ∀ {α : Type} (x : N α), R Inhabited.default x
  choose : ∀ (lo hi : Nat) (h : lo ≤ hi),
    R (RandomChoice.choose lo hi h) (RandomChoice.choose lo hi h)
  admissible : ∀ {α : Type} (x : N α), Lean.Order.admissible fun y : M α => R y x
