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
  unfold String.arbitrary IsAlmostSurelyTerminating SPMF.IsPMF
  rw [SPMF.mass_map]
  rw [SPMF.IsPMF_listOf]
  apply Char.arbitrary.terminates

/-- `NonEmptyString.arbitrary` almost surely terminates -/
theorem NonEmptyString.arbitrary_terminates : IsAlmostSurelyTerminating NonEmptyString.arbitrary := by
  unfold NonEmptyString.arbitrary IsAlmostSurelyTerminating SPMF.IsPMF
  rw [SPMF.mass_map]
  rw [SPMF.IsPMF_nonEmptyListOf]
  apply Char.arbitrary.terminates

/-- The cost bound comes from the generic `IsBounded_listOf` combinator lemma
    applied to `Char.arbitrary` (whose per-element cost is `1`):
    - `s.length` calls to `pick`
    - a cost of `(fun _ => 1) <$> s = s.length` for generating each element of the list,
    - plus `1` for the final `pick` to generate the end of the list,
    resulting in a total `2 * s.length + 1`. -/
theorem String.arbitrary_cost :
    IsCostBounded String.arbitrary (fun s => 2 * s.length + 1) := by
  unfold String.arbitrary IsCostBounded
  simp [IsBounded_iff]
  intro s cost cs hcs heq
  subst heq
  simp [String.length_ofList]
  have hcost : cost ≤ cs.length + ((fun _ => 1) <$> cs).sum + 1 := by
    apply IsBounded_iff.mp (IsBounded_listOf Char.arbitrary.cost_bounded) (cs, cost)
    assumption
  simp only [Functor.map, List.map_const', List.sum_replicate, smul_eq_mul, mul_one] at hcost
  omega

/-- The cost bound is the same as `String.arbitrary`, except its value is always 1 less
    since `NonEmptyString` doesn't need to call `pick` at the end
    to terminate the list after all elements have been generated
    (strings produced by this generator are always guaranteed to be non-empty). -/
theorem NonEmptyString.arbitrary_cost :
    IsCostBounded NonEmptyString.arbitrary (fun s => 2 * s.length) := by
  unfold NonEmptyString.arbitrary IsCostBounded
  simp [IsBounded_iff]
  intro s cost cs hcs heq
  subst heq
  simp [String.length_ofList]
  have hcost : cost ≤ cs.length + ((fun _ => 1) <$> cs).sum := by
    apply IsBounded_iff.mp (IsBounded_nonEmptyListOf Char.arbitrary.cost_bounded) (cs, cost)
    assumption
  simp only [Functor.map, List.map_const', List.sum_replicate, smul_eq_mul, mul_one] at hcost
  omega

end ArbString
