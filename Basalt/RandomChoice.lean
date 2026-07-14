/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
open Lean.Order

/-!
# Abstracting Over Random Choices

This file defines a type class and associated operations for random choices.
-/

class RandomChoice (m : Type u → Type v) where
  /-- An inclusive choice over a nonempty range of natural numbers. -/
  choose : (lo hi : Nat) → (h : lo ≤ hi) → m (ULift {x : Nat // lo ≤ x ∧ x ≤ hi})

/-- A uniform binary choice. -/
def RandomChoice.pick [Monad m] [RandomChoice m] (x y : Unit → m α) := do
  if (ULift.down (← choose 0 1 (by simp))).val == 0 then x () else y ()

/-- A weighted binary choice. -/
def RandomChoice.coin [Monad m] [RandomChoice m] (r : Rat) : m Bool := do
  if (ULift.down (← choose 0 (r.den - 1) (by simp))).val < r.num then pure true else pure false

/-- The `pick` combinator is `monotone` if its arguments are.

This is intended to be used in the construction of partial_fixpoint, and not meant to be used otherwise. -/
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
