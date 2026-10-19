/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
module

public import Batteries.Data.Char
public import Basalt
public import BasaltExamples.ArbChar
public import BasaltExamples.ArbString.Def

/-!
# Arbitrary Strings

Correctness proofs for `String.arbitrary` and `NonEmptyString.arbitrary` (defined in
`BasaltExamples/ArbString.Def`), arbitrary alphanumeric strings. Each property is proved directly on
`String.ofList` mapped over `listOf Char.arbitrary` or `nonEmptyListOf Char.arbitrary`, with
`Char.arbitrary`'s laws for the elements.
-/

@[expose] public section

open RandomChoice ArbChar

namespace ArbString

/-- `String.arbitrary`'s support is exactly the set of alphanumeric strings -/
theorem String.arbitrary_support :
    IsSoundAndComplete String.arbitrary (fun s => ∀ c ∈ s.toList, c.isAlphanum = true) := by
  refine .intro ?sound ?complete
  case sound =>
    rw [IsSoundFor.iff_obs]
    walk fixpoint [Char.arbitrary.sound_complete.sound.obs]
    simp_all
  case complete =>
    intro s hs
    rw [String.arbitrary, SPMF.mem_support_iff_may]
    walk [Char.arbitrary.sound_complete.complete.obs]
    exact ⟨s.toList, hs, String.ofList_toList⟩

/-- `NonEmptyString.arbitrary`'s support is exactly the set of
    *non-empty* alphanumeric strings -/
theorem NonEmptyString.arbitrary_support :
    IsSoundAndComplete NonEmptyString.arbitrary (fun s => !s.isEmpty ∧ ∀ c ∈ s.toList, c.isAlphanum = true) := by
  refine .intro ?sound ?complete
  case sound =>
    rw [IsSoundFor.iff_obs]
    walk fixpoint [Char.arbitrary.sound_complete.sound.obs]
    all_goals simp_all [String.isEmpty]
  case complete =>
    intro s ⟨hne, hs⟩
    rw [NonEmptyString.arbitrary, SPMF.mem_support_iff_may]
    walk [Char.arbitrary.sound_complete.complete.obs]
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
  rw [IsCostBounded.iff_obs]
  walk fixpoint
  simp only [String.length_ofList, List.map_const', List.sum_replicate, smul_eq_mul] at *
  omega

/-- `String.arbitrary`'s bound less the final `oneOf`: `nonEmptyListOf` draws its last element
directly. -/
theorem NonEmptyString.arbitrary_cost :
    IsCostBounded NonEmptyString.arbitrary (fun s => 2 * s.length) := by
  rw [IsCostBounded.iff_obs]
  walk fixpoint
  simp only [String.length_ofList, List.map_const', List.sum_replicate, smul_eq_mul] at *
  omega

end ArbString
