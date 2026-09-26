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
relations are `ideal_bound` and `io_bound` under an induction of their own.
-/

theorem genZero.faithful : IsFaithful (genZero Γ τ) where
  terminates := genZero.terminates
  below _ := by
    induction τ generalizing Γ with
    | Bool => unfold genZero; ideal_bound
    | Fun τ1 τ2 _ ih => unfold genZero; ideal_bound
  approx := by
    induction τ generalizing Γ with
    | Bool => unfold genZero; io_bound
    | Fun τ1 τ2 _ ih => unfold genZero; io_bound

theorem genTerm.faithful : IsFaithful (genTerm Γ τ) := by
  faithful_fixpoint [genTerm.terminates, genZero.faithful, genType.faithful]
