/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Batteries.Data.Char
import Basalt
import BasaltExamples.ArbChar
import BasaltExamples.ArbString.Def

/-!
# Arbitrary Strings

Correctness proofs for `String.arbitrary` (defined in `BasaltExamples/ArbString.Def`), an arbitrary
alphanumeric string. Each property is proved first for the underlying `genCharList` and then
transported across `String.ofList`. The `genCharList` proofs mirror `List.arbitrary`'s, with
`Char.arbitrary` in place of `Nat.arbitrary`.
-/

open RandomChoice ArbChar

namespace ArbString

/-- `String.arbitrary`'s support is exactly the set of alphanumeric strings -/
theorem String.arbitrary_support :
    IsSoundAndComplete String.arbitrary (fun s => ∀ c ∈ s.toList, c.isAlphanum = true) := by
  refine .intro ?sound ?complete
  case sound =>
    sound_fixpoint [Char.arbitrary.sound_complete]
    simp_all
  case complete =>
    intro s hs
    rw [String.arbitrary]; complete_bound [Char.arbitrary.sound_complete]
    exact ⟨s.toList, hs, String.ofList_toList⟩

/-- `NonEmptyString.arbitrary`'s support is exactly the set of
    *non-empty* alphanumeric strings -/
theorem NonEmptyString.arbitrary_support :
    IsSoundAndComplete NonEmptyString.arbitrary (fun s => !s.isEmpty ∧ ∀ c ∈ s.toList, c.isAlphanum = true) := by
  refine .intro ?sound ?complete
  case sound =>
    sound_fixpoint [Char.arbitrary.sound_complete]
    all_goals simp_all [String.isEmpty]
  case complete =>
    intro s ⟨hne, hs⟩
    rw [NonEmptyString.arbitrary]; complete_bound [Char.arbitrary.sound_complete]
    refine ⟨s.toList, ⟨?_, hs⟩, String.ofList_toList⟩
    simpa [String.isEmpty, String.toList_eq_nil_iff] using hne

theorem String.arbitrary.terminates : IsAlmostSurelyTerminating String.arbitrary := by
  mass_fixpoint using SPMF.LfpIsOne.one
  simp

/-- `NonEmptyString.arbitrary` almost surely terminates -/
theorem NonEmptyString.arbitrary.terminates :
    IsAlmostSurelyTerminating NonEmptyString.arbitrary := by
  mass_fixpoint using SPMF.LfpIsOne.one
  simp

theorem String.arbitrary.faithful : IsFaithful String.arbitrary := by
  faithful_fixpoint [String.arbitrary.terminates]

theorem NonEmptyString.arbitrary.faithful : IsFaithful NonEmptyString.arbitrary := by
  faithful_fixpoint [NonEmptyString.arbitrary.terminates]

/-- `listOf`'s bound with `Char.arbitrary`'s per-element cost of `1`: one `oneOf` and one character
per element, plus the `oneOf` that ends the list. -/
theorem String.arbitrary_cost :
    IsCostBounded String.arbitrary (fun s => 2 * s.length + 1) := by
  cost_fixpoint
  simp only [String.length_ofList, List.map_const', List.sum_replicate, smul_eq_mul] at *
  omega

/-- `String.arbitrary`'s bound less the final `oneOf`: `nonEmptyListOf` draws its last element
directly. -/
theorem NonEmptyString.arbitrary_cost :
    IsCostBounded NonEmptyString.arbitrary (fun s => 2 * s.length) := by
  cost_fixpoint
  simp only [String.length_ofList, List.map_const', List.sum_replicate, smul_eq_mul] at *
  omega

end ArbString
