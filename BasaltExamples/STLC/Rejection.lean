/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
module

import Mathlib.Tactic.Basify
public import Basalt
public import BasaltExamples.STLC.Distribution

/-!
# Rejecting Uninteresting Terms

`genTermSized` and `genTerm` retried until their term is not trivial, or not a useless abstraction,
with `suchThat`. Over `genTermSized` the loop keeps its source's distribution conditioned on
acceptance and costs a constant factor more on average; over `genTerm` it still terminates, and its
expected cost still has no finite bound.
-/

@[expose] public section

namespace STLC

open RandomChoice
open scoped ENNReal

/-! ## Deciding the events -/

/-- `Term.IsTrivial`, decided. -/
def Term.isTrivial : Term → _root_.Bool
  | .Bool _ => true
  | .Abs _ e => e.isTrivial
  | _ => false

theorem Term.isTrivial_iff {e : Term} : e.isTrivial = true ↔ e.IsTrivial := by
  induction e <;> simp [Term.isTrivial, Term.IsTrivial, *]

instance : DecidablePred Term.IsTrivial := fun _ => decidable_of_iff _ Term.isTrivial_iff

/-- `Term.Mentions`, decided. -/
def Term.mentions : Term → Nat → _root_.Bool
  | .Var j, i => j == i
  | .Bool _, _ => false
  | .App e1 e2, i => e1.mentions i || e2.mentions i
  | .Abs _ e, i => e.mentions (i + 1)

theorem Term.mentions_iff {e : Term} {i : Nat} : e.mentions i = true ↔ e.Mentions i := by
  induction e generalizing i <;> simp [Term.mentions, Term.Mentions, *]

/-- `Term.IsUselessAbs`, decided. -/
def Term.isUselessAbs : Term → _root_.Bool
  | .Abs _ e => !e.mentions 0
  | _ => false

theorem Term.isUselessAbs_iff {e : Term} : e.isUselessAbs = true ↔ e.IsUselessAbs := by
  cases e <;> simp [Term.isUselessAbs, Term.IsUselessAbs, ← Term.mentions_iff]

instance : DecidablePred Term.IsUselessAbs := fun _ => decidable_of_iff _ Term.isUselessAbs_iff

theorem prob_reject_trivial (g : SPMF Term) :
    SPMF.prob g {e | (!e.isTrivial) = false} = SPMF.prob g trivialTerms := by
  congr 1; ext e; simp [trivialTerms, Term.isTrivial_iff]

theorem prob_reject_useless (g : SPMF Term) :
    SPMF.prob g {e | (!e.isUselessAbs) = false} = SPMF.prob g uselessAbs := by
  congr 1; ext e; simp [uselessAbs, Term.isUselessAbs_iff]

/-- A bound over the chance of acceptance, as a multiple. -/
theorem div_one_sub_le_mul {T r k : ℝ≥0∞} (h : 1 ≤ k * (1 - r)) : T / (1 - r) ≤ k * T := by
  refine ENNReal.div_le_of_le_mul ?_
  calc T = T * 1 := (mul_one T).symm
    _ ≤ T * (k * (1 - r)) := by gcongr
    _ = k * T * (1 - r) := by ring

/-! ## Generators -/

/-- Draws from `genTermSized` until the term drawn is not trivial. -/
def genTermSizedNontrivial [Gen G] (n : Nat) (Γ : Ctx) (τ : Ty) : G Term :=
  suchThat (genTermSized n Γ τ) (!·.isTrivial)

/-- Draws from `genTermSized` until the term drawn is not a useless abstraction. -/
def genTermSizedUseful [Gen G] (n : Nat) (Γ : Ctx) (τ : Ty) : G Term :=
  suchThat (genTermSized n Γ τ) (!·.isUselessAbs)

/-- Draws from `genTerm` until the term drawn is not trivial. -/
def genTermNontrivial [Gen G] (Γ : Ctx) (τ : Ty) : G Term :=
  suchThat (genTerm Γ τ) (!·.isTrivial)

/-! ## Rejecting trivial terms from `genTermSized` -/

theorem genTermSizedNontrivial.sound :
    IsSoundFor (genTermSizedNontrivial n Γ τ) fun e => Typing Γ e τ ∧ ¬ e.IsTrivial := by
  rw [IsSoundFor.iff_obs]
  walk [genTermSized.sound.obs]
  all_goals simp_all [← Term.isTrivial_iff]

theorem genTermSizedNontrivial.terminates :
    IsAlmostSurelyTerminating (genTermSizedNontrivial (n + 2) Γ τ : SPMF Term) :=
  SPMF.isAlmostSurelyTerminating_suchThat genTermSized.terminates
    ((SPMF.prob_reject_eq_expect _ _).symm.trans_le
      ((prob_reject_trivial _).trans_le genTermSized.prob_trivial_le))
    (by basify; norm_num)

/-- `genTermSized` conditioned on a term that is not trivial. -/
theorem genTermSizedNontrivial.apply (e : Term) :
    (genTermSizedNontrivial n Γ τ : SPMF Term) e = if e.IsTrivial then 0 else
      (genTermSized n Γ τ : SPMF Term) e / (1 - SPMF.prob (genTermSized n Γ τ) trivialTerms) := by
  rw [genTermSizedNontrivial, SPMF.suchThat_apply, prob_reject_trivial]
  rcases h : e.isTrivial <;> simp [← Term.isTrivial_iff, h]

/-- A quarter more than `genTermSized`'s worst case: at most a fifth of its draws are rejected. -/
theorem genTermSizedNontrivial.expected_cost :
    IsExpectedCostBounded (genTermSizedNontrivial (n + 2) Γ τ : SPMF.Cost Term)
      (5 / 4 * termCost (n + 2)) := by
  refine (IsExpectedCostBounded.suchThat genTermSized.cost_faithful genTermSized.expected_cost
    ((prob_reject_trivial _).trans_le genTermSized.prob_trivial_le)).mono
    (div_one_sub_le_mul (by basify; norm_num))

/-! ## Rejecting useless abstractions from `genTermSized` -/

theorem genTermSizedUseful.sound :
    IsSoundFor (genTermSizedUseful n Γ τ) fun e => Typing Γ e τ ∧ ¬ e.IsUselessAbs := by
  rw [IsSoundFor.iff_obs]
  walk [genTermSized.sound.obs]
  all_goals simp_all [← Term.isUselessAbs_iff]

/-- At a function type, from size `1` and at every context: at most a third of the draws are
rejected (`genTermSized.prob_useless_fun_le`). -/
theorem genTermSizedUseful.terminates :
    IsAlmostSurelyTerminating (genTermSizedUseful (n + 1) Γ (.Fun τ1 τ2) : SPMF Term) :=
  SPMF.isAlmostSurelyTerminating_suchThat genTermSized.terminates
    ((SPMF.prob_reject_eq_expect _ _).symm.trans_le
      ((prob_reject_useless _).trans_le genTermSized.prob_useless_fun_le))
    (by basify; norm_num)

/-- `genTermSized` conditioned on a term that is not a useless abstraction. -/
theorem genTermSizedUseful.apply (e : Term) :
    (genTermSizedUseful n Γ τ : SPMF Term) e = if e.IsUselessAbs then 0 else
      (genTermSized n Γ τ : SPMF Term) e / (1 - SPMF.prob (genTermSized n Γ τ) uselessAbs) := by
  rw [genTermSizedUseful, SPMF.suchThat_apply, prob_reject_useless]
  rcases h : e.isUselessAbs <;> simp [← Term.isUselessAbs_iff, h]

/-- Half again `genTermSized`'s worst case, at every context and function type. -/
theorem genTermSizedUseful.expected_cost :
    IsExpectedCostBounded (genTermSizedUseful (n + 1) Γ (.Fun τ1 τ2) : SPMF.Cost Term)
      (3 / 2 * termCost (n + 1)) :=
  (IsExpectedCostBounded.suchThat genTermSized.cost_faithful genTermSized.expected_cost
    ((prob_reject_useless _).trans_le genTermSized.prob_useless_fun_le)).mono
    (div_one_sub_le_mul (by basify; norm_num))

/-- At closed functions on `Bool`, from size `2`: at most `5/21` of the draws are rejected
(`genTermSized.prob_useless_le`). -/
theorem genTermSizedUseful.expected_cost_closed :
    IsExpectedCostBounded (genTermSizedUseful (n + 2) [] (.Fun .Bool .Bool) : SPMF.Cost Term)
      (21 / 16 * termCost (n + 2)) :=
  (IsExpectedCostBounded.suchThat genTermSized.cost_faithful genTermSized.expected_cost
    ((prob_reject_useless _).trans_le genTermSized.prob_useless_le)).mono
    (div_one_sub_le_mul (by basify; norm_num))

/-! ## Rejecting trivial terms from `genTerm` -/

theorem genTermNontrivial.sound :
    IsSoundFor (genTermNontrivial Γ τ) fun e => Typing Γ e τ ∧ ¬ e.IsTrivial := by
  rw [IsSoundFor.iff_obs]
  walk [genTerm.sound_complete.sound.obs]
  all_goals simp_all [← Term.isTrivial_iff]

/-- At most two thirds of the draws are rejected (`genTerm.prob_trivial_le`). -/
theorem genTermNontrivial.terminates :
    IsAlmostSurelyTerminating (genTermNontrivial Γ τ : SPMF Term) :=
  SPMF.isAlmostSurelyTerminating_suchThat genTerm.terminates
    ((SPMF.prob_reject_eq_expect _ _).symm.trans_le
      ((prob_reject_trivial _).trans_le genTerm.prob_trivial_le))
    (by basify; norm_num)

/-- Rejection does not tame `genTerm`: its first draw alone has no finite expected cost
(`genTerm.not_expected_cost_bounded`), and that draw is accepted a third of the time or more. -/
theorem genTermNontrivial.not_expected_cost_bounded {B : ℝ≥0∞} (hB : B ≠ ⊤) :
    ¬ IsExpectedCostBounded (genTermNontrivial Γ τ : SPMF.Cost Term) B := by
  have hsum := SPMF.prob_accept_add_prob_reject (genTerm Γ τ : SPMF Term) (!·.isTrivial)
  rw [genTerm.terminates, prob_reject_trivial] at hsum
  have hrej := genTerm.prob_trivial_le (Γ := Γ) (τ := τ)
  refine IsExpectedCostBounded.not_suchThat genTerm.cost_faithful (pos_iff_ne_zero.mpr fun h0 => ?_)
    (fun _ hB => genTerm.not_expected_cost_bounded hB) hB
  rw [h0, zero_add] at hsum
  rw [hsum] at hrej
  revert hrej
  basify
  norm_num

end STLC
