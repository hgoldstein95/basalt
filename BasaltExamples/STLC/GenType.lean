/-
Copyright (c) 2026 Harrison Goldstein & Ernest Ng. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein & Ernest Ng
-/
import Basalt
import BasaltExamples.STLC.Syntax

/-!
# Arbitrary STLC Types

`genType` generates an arbitrary `Ty`. Its two branches are a leaf and two recursive calls, so it is
critical, like `AllTwoTree.genTree`: almost surely terminating, with infinite expected size.
-/

open RandomChoice

/-- Generates an arbitrary type. -/
def genType [Gen G] : G Ty :=
  oneOf! [
    fun _ => pure .Bool,
    fun _ => do
      let τ1 ← genType
      let τ2 ← genType
      return .Fun τ1 τ2]
partial_fixpoint

theorem genType.sound_complete : IsSoundAndComplete genType (fun _ => True) := by
  refine .intro ?sound ?complete
  case sound => rw [IsSoundFor.iff_obs]; walk fixpoint
  case complete =>
    intro τ
    induction τ with
    | Bool => intro _; rw [genType, SPMF.mem_support_iff_may]; walk
    | Fun τ1 τ2 ih1 ih2 =>
      intro _
      rw [genType, SPMF.mem_support_iff_may]; walk
      exact ⟨τ1, ih1 trivial, τ2, ih2 trivial, rfl⟩

theorem genType.terminates : IsAlmostSurelyTerminating genType := by
  mass_fixpoint using SPMF.LfpIsOne.quadratic (a := 1 / 2) (b := 0) (d := 1 / 2)
    (by ennreal_to_real; norm_num) (by ennreal_to_real; norm_num) (by norm_num)
  simp [sq, ENNReal.div_eq_inv_mul, mul_add]

theorem genType.cost_bounded : IsCostBounded genType Ty.size := by
  rw [IsCostBounded.iff_obs]
  walk fixpoint
  all_goals simp only [Ty.size] at *; omega

theorem genType.faithful : IsFaithful genType := by
  faithful_fixpoint [genType.terminates]
