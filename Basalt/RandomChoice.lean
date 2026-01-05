open Lean.Order

/-!
# Abstracting Over Random Choices

This file defines a type class and associated operations for random choices.
-/

class RandomChoice (m : Type → Type) where
  /-- An inclusive choice over a nonempty range of natural numbers. -/
  choose : (lo hi : Nat) → (h : lo ≤ hi) → m Nat

/-- A uniform binary choice. -/
def RandomChoice.pick [Monad m] [RandomChoice m] (x y : Unit → m α) := do
  if (← choose 0 1 (by simp)) == 0 then x () else y ()

/-- A weighted binary choice. -/
def RandomChoice.coin [Monad m] [RandomChoice m] (r : Rat) : m Bool := do
  if (← choose 0 r.den (by simp)) < r.num then pure true else pure false

@[partial_fixpoint_monotone]
theorem RandomChoice.monotone_pick
    [∀ α, PartialOrder (m α)]
    [Monad m]
    [MonoBind m]
    [RandomChoice m]
    [PartialOrder α]
    {x y : (α → m β)}
    (hx : monotone (fun a => x a))
    (hy : monotone (fun a => y a)) :
    monotone (fun (a : α) => pick (fun () => x a) (fun () => y a)) := by
  simp [pick]
  apply monotone_bind
  . apply monotone_const
  . refine monotone_of_monotone_apply _ fun ref => ?_
    apply monotone_ite
    . assumption
    . assumption
