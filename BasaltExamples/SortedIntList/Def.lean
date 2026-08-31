/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Mathlib.Data.List.Chain

/-!
# Sorted Integer Lists (definitions)

The validity predicates for the sorted linked lists of Dewey, Nichols and Hardekopf's
bounded-exhaustive benchmark: a non-decreasing `List Int` of at most `maxLen` elements drawn from
`[0, maxVal]`, and the specialization in which consecutive elements are at most `k` apart. Every
bound is explicit, so a generator can be complete for the whole predicate rather than for a
truncation of it.
-/

namespace SortedIntList

/-- Bounded sorted lists: at most `maxLen` elements, each in `[0, maxVal]`, non-decreasing. -/
def List.boundedSorted (maxLen : Nat) (maxVal : Int) (xs : List Int) : Prop :=
  xs.length ≤ maxLen ∧ (∀ x ∈ xs, 0 ≤ x ∧ x ≤ maxVal) ∧ xs.IsChain (· ≤ ·)

/-- The specialization: consecutive elements are separated by at most `k`, so `[0, 2, 5, 5]` is
valid for `k = 3`. The gap constrains adjacent *pairs* only; the first element is bounded by
`[0, maxVal]` alone. -/
def List.boundedGapped (k maxLen : Nat) (maxVal : Int) (xs : List Int) : Prop :=
  xs.length ≤ maxLen ∧ (∀ x ∈ xs, 0 ≤ x ∧ x ≤ maxVal) ∧
    xs.IsChain (fun x y => x ≤ y ∧ y - x ≤ (k : Int))

theorem List.boundedGapped.toBoundedSorted (h : List.boundedGapped k maxLen maxVal xs) :
    List.boundedSorted maxLen maxVal xs :=
  ⟨h.1, h.2.1, h.2.2.imp fun _ _ hxy => hxy.1⟩

end SortedIntList
