/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Batteries.Data.Char
import Basalt
import BasaltExamples.ArbChar.Def

open RandomChoice

/-!
# Arbitrary Characters

Correctness proofs for `Char.arbitrary` (defined in `BasaltExamples/ArbChar.Def`), which draws a
uniformly random alphanumeric character. Because it is a single `elements` draw over a fixed list,
it is not recursive: it always terminates and costs exactly one choice.
-/

namespace ArbChar

private theorem alphanumChars_eq_filter :
    ∀ c : Char, c ∈ alphanumChars ↔ c.isAlphanum = true := by native_decide

theorem Char.arbitrary.sound_complete :
    IsSoundAndComplete Char.arbitrary (fun c => c.isAlphanum = true) := by
  refine .intro ?sound ?complete
  case sound =>
    sound_fixpoint
    exact (alphanumChars_eq_filter c).mp h_c
  case complete =>
    intro c hc
    rw [Char.arbitrary]; complete_bound
    exact (alphanumChars_eq_filter c).mpr hc

theorem Char.arbitrary.terminates : IsAlmostSurelyTerminating Char.arbitrary := by
  mass_fixpoint using SPMF.LfpIsOne.one
  simp

theorem Char.arbitrary.cost_bounded :
    IsCostBounded Char.arbitrary (fun _ => 1) := by
  cost_fixpoint
  omega

end ArbChar
