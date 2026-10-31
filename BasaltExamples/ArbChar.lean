/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
module

public import Basalt
public import BasaltExamples.ArbChar.Def
meta import BasaltExamples.ArbChar.Def

/-!
# Arbitrary Characters

Correctness proofs for `Char.arbitrary` (defined in `BasaltExamples/ArbChar.Def`), which draws a
uniformly random alphanumeric character. Because it is a single `elements` draw over a fixed list,
it is not recursive: it always terminates and costs exactly one choice.
-/

@[expose] public section

open RandomChoice

namespace ArbChar

private theorem alphanumChars_eq_filter (c : Char) :
    c ∈ alphanumChars ↔ c.isAlphanum = true := by
  by_cases hc : c.toNat < 128
  · have h : ∀ n : Fin 128, Char.ofNat n ∈ alphanumChars ↔ (Char.ofNat n).isAlphanum = true := by
      decide +kernel
    simpa using h ⟨c.toNat, hc⟩
  · have hall : alphanumChars.all (·.toNat < 128) := by decide
    have h1 : c ∉ alphanumChars := fun hm => hc (of_decide_eq_true (List.all_eq_true.mp hall c hm))
    have h2 : c.isAlphanum = false := by
      simp only [Char.toNat] at hc
      simp only [Char.isAlphanum, Char.isAlpha, Char.isDigit, Char.isUpper, Char.isLower]
      grind
    simp [h1, h2]

theorem Char.arbitrary.sound_complete :
    IsSoundAndComplete Char.arbitrary (fun c => c.isAlphanum = true) := by
  refine .intro ?sound ?complete
  case sound =>
    rw [IsSoundFor.iff_obs]
    walk fixpoint
    next c h_c => exact (alphanumChars_eq_filter c).mp h_c
  case complete =>
    intro c hc
    rw [Char.arbitrary, SPMF.mem_support_iff_may]; walk
    exact (alphanumChars_eq_filter c).mpr hc

theorem Char.arbitrary.terminates : IsAlmostSurelyTerminating Char.arbitrary := by
  mass_fixpoint using SPMF.LfpIsOne.one
  simp

theorem Char.arbitrary.cost_bounded :
    IsCostBounded Char.arbitrary (fun _ => 1) := by
  rw [IsCostBounded.iff_obs]
  walk fixpoint
  omega

theorem Char.arbitrary.faithful : IsFaithful Char.arbitrary := by
  faithful_fixpoint [Char.arbitrary.terminates]

end ArbChar
