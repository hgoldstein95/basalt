/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt
import Batteries.Data.Char
import BasaltExamples.ArbChar
import BasaltExamples.ArbString.Def

open RandomChoice ArbChar

/-!
# Arbitrary Strings

Correctness proofs for `String.arbitrary` (defined in `BasaltExamples/ArbString.Def`), an arbitrary
alphanumeric string. Each property is proved first for the underlying `genCharList` and then
transported across `String.ofList`. The `genCharList` proofs mirror `List.arbitrary`'s, with
`Char.arbitrary` in place of `Nat.arbitrary`.
-/

namespace ArbString

/-- `String.arbitrary`'s support is exactly the set of alphanumeric strings -/
theorem String.arbitrary_support :
    IsSoundAndComplete String.arbitrary (fun s => ∀ c ∈ s.toList, c.isAlphanum = true) := by
  intro s
  simp only [String.arbitrary, SPMF.mem_support_map_iff]
  constructor
  · rintro ⟨cs, hcs, rfl⟩
    rw [SPMF.mem_support_listOf, Set.mem_ofPred_eq] at hcs
    intro c hc
    rw [String.toList_ofList] at hc
    specialize hcs c hc
    simpa [Char.arbitrary_mem_support] using hcs
  · intro h
    set cs := s.toList
    exists cs
    constructor
    . rw [SPMF.mem_support_listOf, Set.mem_ofPred_eq]
      intro c hmem
      simp [Char.arbitrary_mem_support]
      apply h
      assumption
    . rw [String.ofList_toList]

/-- `NonEmptyString.arbitrary`'s support is exactly the set of
    *non-empty* alphanumeric strings -/
theorem NonEmptyString.arbitrary_support :
    IsSoundAndComplete NonEmptyString.arbitrary (fun s => !s.isEmpty ∧ ∀ c ∈ s.toList, c.isAlphanum = true) := by
  intro s
  simp only [NonEmptyString.arbitrary, SPMF.mem_support_map_iff]
  constructor
  · rintro ⟨cs, hcs, rfl⟩
    rw [SPMF.mem_support_nonEmptylistOf] at hcs
    rw [Set.mem_ofPred_eq] at hcs
    obtain ⟨h1, h2⟩ := hcs
    constructor
    . rw [Bool.not_eq_true_eq_eq_false]
      simp [String.isEmpty]
      assumption
    . intro c hc
      rw [String.toList_ofList] at hc
      specialize h2 c hc
      simp [Char.arbitrary_mem_support] at h2
      assumption
  · intro h
    set cs := s.toList
    exists cs
    constructor
    . obtain ⟨hne, hc⟩ := h
      simp at hne
      subst cs
      rw [SPMF.support_nonEmptyListOf]
      rw [Set.mem_ofPred_eq]
      constructor
      . simpa [String.isEmpty, String.toList_eq_nil_iff] using hne
      . intro c hmem
        simp [Char.arbitrary_mem_support]
        apply hc
        assumption
    . rw [String.ofList_toList]

theorem String.arbitrary.terminates : IsAlmostSurelyTerminating String.arbitrary := by
  mass_fixpoint using SPMF.LfpIsOne.one
  simp

/-- `NonEmptyString.arbitrary` almost surely terminates -/
theorem NonEmptyString.arbitrary_terminates : IsAlmostSurelyTerminating NonEmptyString.arbitrary := by
  mass_fixpoint using SPMF.LfpIsOne.one
  simp

/-- `listOf`'s bound with `Char.arbitrary`'s per-element cost of `1`: one `pick` and one character
per element, plus the `pick` that ends the list. -/
theorem String.arbitrary_cost :
    IsCostBounded String.arbitrary (fun s => 2 * s.length + 1) := by
  cost_fixpoint
  simp only [String.length_ofList, List.map_const', List.sum_replicate, smul_eq_mul] at *
  omega

/-- `String.arbitrary`'s bound less the final `pick`: `nonEmptyListOf` draws its last element
directly. -/
theorem NonEmptyString.arbitrary_cost :
    IsCostBounded NonEmptyString.arbitrary (fun s => 2 * s.length) := by
  cost_fixpoint
  simp only [String.length_ofList, List.map_const', List.sum_replicate, smul_eq_mul] at *
  omega

end ArbString
