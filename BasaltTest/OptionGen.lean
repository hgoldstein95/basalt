/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt

/-!
# A Derived Combinator With No Law

`biasedOptionGen` and `optionGen` are fixtures, not library combinators: they have no `@[gen_map]`
lemma and no law, so a walk has to unfold and traverse their bodies. `BasaltTest/Walk/Mass.lean`
and `BasaltTest/Walk/Cost.lean` pin that path.
-/

open Lean.Order RandomChoice

/-- Lifts a generator of `α`'s into a generator of `Option α`'s, which returns `some <$> g` with
probability `r`.

Note: we explicitly use `bind` instead of `<$>` in the body of this combinator, as there is no
monotonicity lemma for `<$>` in `Lean.Order`. -/
def biasedOptionGen [Gen G] (r : Rat) (g : G α) : G (Option α) := do
  if ← RandomChoice.coin r then do
    let x ← g
    pure (some x)
  else
    pure none

/-- Lifts a generator of `α`'s into a generator of `Option α`'s, which returns `none` with probability 1/2 -/
def optionGen [Gen G] (g : G α) : G (Option α) :=
  biasedOptionGen (1 / 2) g

/-- Lemma allowing us to use `biasedOptionGen` in functions marked as `partial_fixpoint`. -/
@[partial_fixpoint_monotone]
theorem monotone_biasedOptionGen [Gen G] [Lean.Order.PartialOrder γ]
    (g : γ → G α) (hg : monotone g) :
    monotone (fun x => biasedOptionGen r (g x)) := by
  unfold biasedOptionGen
  apply monotone_bind
  . apply Lean.Order.monotone_const
  . apply monotone_of_monotone_apply
    intro b
    cases b <;> simp
    . apply Lean.Order.monotone_const
    . apply monotone_bind
      . assumption
      . apply Lean.Order.monotone_const

/-- Lemma allowing us to use `optionGen` in functions marked as `partial_fixpoint` -/
@[partial_fixpoint_monotone]
theorem monotone_optionGen [Gen G] [Lean.Order.PartialOrder γ]
    (g : γ → G α) (hg : monotone g) :
    monotone (fun x => optionGen (g x)) := by
  unfold optionGen
  apply monotone_biasedOptionGen
  assumption

/-- A generator that draws an unbounded list of successes, exercising the two lemmas above. -/
def optionListOf [Gen G] (g : G α) : G (List α) := do
  match ← optionGen g with
  | none => pure []
  | some x => do
    let xs ← optionListOf g
    pure (x :: xs)
partial_fixpoint
