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
relations are `ideal_bound` and `io_bound` under an induction of their own. `Bool.arbitrary` and
`genBool` have no `.terminates` law, so they state the relations alone, which their callers' walks
use.
-/

theorem Bool.arbitrary.ideal [WordSource σ] (src : IdealSource σ) :
    src.Below Bool.arbitrary Bool.arbitrary := by
  ideal_fixpoint

theorem Bool.arbitrary.io : IOModel.Approx Bool.arbitrary Bool.arbitrary := by
  io_fixpoint

theorem genBool.ideal [WordSource σ] (src : IdealSource σ) : src.Below genBool genBool := by
  ideal_fixpoint

theorem genBool.io : IOModel.Approx genBool genBool := by
  io_fixpoint

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
  faithful_fixpoint
