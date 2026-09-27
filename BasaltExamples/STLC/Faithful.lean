/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt.Tactic.Faithful
import BasaltExamples.STLC.Termination

/-!
# Faithfulness for `genTerm`

`genTerm` and `genZero` are faithful. `genZero` is defined by structural recursion, so its
relations are walked under an induction of their own.
-/

theorem genZero.faithful : IsFaithful (genZero Γ τ) where
  terminates := genZero.terminates
  below _ _ _ := by
    induction τ generalizing Γ with
    | Bool => unfold genZero; walk
    | Fun τ1 τ2 _ ih => unfold genZero; walk
  approx := by
    induction τ generalizing Γ with
    | Bool => unfold genZero; walk
    | Fun τ1 τ2 _ ih => unfold genZero; walk

theorem genTerm.faithful : IsFaithful (genTerm Γ τ) := by
  faithful_fixpoint [genTerm.terminates, genZero.faithful, genType.faithful]
