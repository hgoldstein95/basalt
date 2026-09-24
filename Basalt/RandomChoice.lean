/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
/-!
# Abstracting Over Random Choices

This file defines a type class and associated operations for random choices.
-/

class RandomChoice (m : Type u → Type v) where
  /-- An inclusive choice over a nonempty range of natural numbers. -/
  choose : (lo hi : Nat) → (h : lo ≤ hi) → m (ULift {x : Nat // lo ≤ x ∧ x ≤ hi})

/-- A weighted binary choice. -/
def RandomChoice.coin [Monad m] [RandomChoice m] (r : Rat) : m Bool := do
  if (ULift.down (← choose 0 (r.den - 1) (by simp))).val < r.num then pure true else pure false
