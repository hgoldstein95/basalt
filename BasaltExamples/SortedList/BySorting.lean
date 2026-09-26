/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt
import BasaltExamples.ArbList
import BasaltExamples.SortedList

/-!
# Sorted Lists by Sorting

`List.genSortedBySorting` generates a sorted list the indirect way: draw an arbitrary list
(`BasaltExamples/ArbList`) and sort it. It reaches exactly the lists `List.genSorted`
(`BasaltExamples/SortedList`) reaches by building them in order
(`List.support_genSortedBySorting_eq`), though not with the same probabilities; and being a
post-processing step over a generator whose laws are already proved, none of its three proofs needs
`fix_induct` or an induction on the generated value.
-/

open RandomChoice

namespace SortedList

/-- Generates a sorted list by generating an arbitrary list and sorting it. -/
def List.genSortedBySorting [Gen G] : G (List Nat) := do
  let xs ← ArbList.List.arbitrary
  return xs.mergeSort

/-- `List.sorted` is the chain form of `List.Pairwise`, which is the vocabulary the `mergeSort`
lemmas are stated in. -/
theorem List.sorted_iff_pairwise (xs : List Nat) : List.sorted xs ↔ xs.Pairwise (· ≤ ·) := by
  fun_induction List.sorted <;> simp_all [List.pairwise_cons]
  grind

/-- Soundness, before it meets the generator: sorting sorts. -/
theorem List.sorted_mergeSort (xs : List Nat) : List.sorted xs.mergeSort := by
  rw [List.sorted_iff_pairwise]
  simpa using List.pairwise_mergeSort (le := fun a b => a ≤ b) (by simp; omega) (by simp; omega) xs

/-- Completeness, before it meets the generator: sorting fixes an already-sorted list, so every
sorted list is the image of *itself*. -/
theorem List.mergeSort_of_sorted (h : List.sorted xs) : xs.mergeSort = xs :=
  List.mergeSort_of_pairwise (by simpa using (List.sorted_iff_pairwise xs).mp h)

theorem List.genSortedBySorting.sound_complete :
    IsSoundAndComplete List.genSortedBySorting List.sorted := by
  refine .intro ?sound ?complete
  case sound =>
    sound_fixpoint [ArbList.List.arbitrary.sound_complete]
    next xs _ => exact List.sorted_mergeSort xs
  case complete =>
    intro ys h
    rw [List.genSortedBySorting]; complete_bound [ArbList.List.arbitrary.sound_complete]
    exact ⟨ys, List.mergeSort_of_sorted h⟩

theorem List.genSortedBySorting.terminates :
    IsAlmostSurelyTerminating List.genSortedBySorting := by
  mass_fixpoint [ArbList.List.arbitrary.terminates] using SPMF.LfpIsOne.one
  simp

theorem List.genSortedBySorting.faithful : IsFaithful List.genSortedBySorting := by
  faithful_fixpoint [List.genSortedBySorting.terminates, ArbList.List.arbitrary.faithful]

/-- `List.arbitrary`'s own bound, read on the sorted output: `mergeSort` makes no random choices,
and being a permutation it changes neither the length nor the sum the bound is stated in. -/
theorem List.genSortedBySorting.cost_bounded :
    IsCostBounded List.genSortedBySorting (fun ys => 2 * ys.length + ys.sum + 1) := by
  cost_fixpoint [ArbList.List.arbitrary.cost_bounded]
  expose_names
  have hperm := List.mergeSort_perm xs (fun a b => a ≤ b)
  simp only [hperm.length_eq, hperm.sum_eq]
  omega

end SortedList
