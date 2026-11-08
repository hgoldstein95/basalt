/-
Copyright (c) 2026 Harrison Goldstein & Ernest Ng. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein & Ernest Ng
-/
module

import Mathlib.Tactic.Basify
public import Basalt
public import BasaltExamples.STLC.GenTerm

/-!
# Almost-Sure Termination for `genTerm`

`genTerm` is critical: with an empty context at a function type its branches are `genZero`, an
application (two recursive calls), and an abstraction (one), so its mean offspring is `1`. It
terminates almost surely; its expected cost has no finite bound
(`genTerm.not_expected_cost_bounded`, `STLC/Cost.lean`).
-/

@[expose] public section

namespace STLC

theorem genZero.terminates : IsAlmostSurelyTerminating (genZero Γ τ) := by
  induction τ generalizing Γ with
  | Bool => rw [IsAlmostSurelyTerminating.iff_obs, genZero]; walk; norm_num [ENNReal.div_self]
  | Fun τ1 τ2 _ ih2 => rw [IsAlmostSurelyTerminating.iff_obs, genZero]; walk [ih2.obs]; rfl

theorem genTerm.terminates : IsAlmostSurelyTerminating (genTerm Γ τ) := by
  mass_fixpoint [genZero.terminates.obs, genType.terminates.obs]
    using SPMF.LfpIsOne.poly ![1 / 3, 1 / 3, 1 / 3]
  all_goals simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, Fin.val_zero, Fin.val_one, Fin.val_two,
    pow_zero, pow_one, mul_one]
  all_goals
    split
    all_goals
      norm_num only [List.sum_cons, List.sum_nil, List.length_cons, List.length_nil]
      basify
      nlinarith

end STLC
