/-
Copyright (c) 2026 Harrison Goldstein & Ernest Ng. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein & Ernest Ng
-/
import Basalt
import BasaltExamples.STLC.GenTerm

/-!
# Almost-Sure Termination for `genTerm`

`genTerm` is critical: with an empty context at a function type its branches are `genZero`, an
application (two recursive calls), and an abstraction (one), so its mean offspring is `1`. It
terminates almost surely, with infinite expected size.
-/

theorem genZero.terminates : IsAlmostSurelyTerminating (genZero Γ τ) := by
  induction τ generalizing Γ with
  | Bool => apply SPMF.IsPMF.of_one_le; rw [genZero]; mass_bound; norm_num [ENNReal.div_self]
  | Fun τ1 τ2 _ ih2 => apply SPMF.IsPMF.of_one_le; rw [genZero]; mass_bound [ih2]; rfl

theorem genTerm.terminates : IsAlmostSurelyTerminating (genTerm Γ τ) := by
  mass_fixpoint [genZero.terminates, genType.terminates]
    using SPMF.LfpIsOne.quadratic (a := 1 / 3) (b := 1 / 3) (d := 1 / 3)
    (by ennreal_to_real; norm_num) (by ennreal_to_real; norm_num) (by norm_num)
  all_goals
    split
    all_goals
      norm_num [ENNReal.div_self]
      ennreal_to_real
      nlinarith [c.toReal_nonneg, ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using hc1)]
