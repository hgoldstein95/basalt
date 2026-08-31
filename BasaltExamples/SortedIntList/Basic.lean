/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt
import BasaltExamples.SortedIntList.Def

open RandomChoice

/-!
# Bounded Sorted Lists

`List.genBoundedSorted` generates the sorted lists of `BasaltExamples/SortedIntList/Def`, drawing
each element from `[lo, maxVal]` and handing it on as the next lower bound. The recursion is
structural in a `Nat` bound on the remaining length, which is also the completeness bound: its
support is *every* list the predicate admits.
-/

namespace SortedIntList

/-- Generates a sorted list of at most `n` elements, all of them in `[lo, hi]`.

`stopOrGo` rather than `pick` at the stop-or-continue choice, so the length comes out uniform on
`[0, maxLen]` instead of geometric. -/
def List.genSortedFrom [Gen G] : Nat → Int → Int → G (List Int)
  | 0, _, _ => pure []
  | n + 1, lo, hi =>
    if h : lo ≤ hi then
      stopOrGo n
        (fun () => pure [])
        (fun () => do
          let x ← chooseInt lo hi h
          let xs ← List.genSortedFrom n x hi
          return x :: xs)
    else
      pure []

/-- Generates a bounded sorted list, i.e. one starting from the lower bound `0`. -/
def List.genBoundedSorted [Gen G] (maxLen : Nat) (maxVal : Int) : G (List Int) :=
  List.genSortedFrom maxLen 0 maxVal

/-- Prefixing a lower bound: `lo :: xs` is non-decreasing exactly when `xs` is and every element of
`xs` is at least `lo`. -/
theorem List.isChain_cons_le_iff {lo : Int} {xs : List Int} :
    (lo :: xs).IsChain (· ≤ ·) ↔ (∀ x ∈ xs, lo ≤ x) ∧ xs.IsChain (· ≤ ·) := by
  rw [List.isChain_iff_pairwise, List.pairwise_cons, List.isChain_iff_pairwise]

theorem List.genSortedFrom_mem_support (n : Nat) (lo hi : Int) (xs : List Int) :
    xs ∈ SPMF.support (List.genSortedFrom n lo hi) ↔
      xs.length ≤ n ∧ (∀ x ∈ xs, x ≤ hi) ∧ (lo :: xs).IsChain (· ≤ ·) := by
  induction n generalizing lo xs with
  | zero => cases xs <;> simp [List.genSortedFrom]
  | succ n ih =>
    simp only [List.genSortedFrom]
    support_simp [ih]
    cases xs <;> simp <;> grind

theorem List.genSortedFrom.terminates : ∀ (n : Nat) (lo hi : Int),
    IsAlmostSurelyTerminating (List.genSortedFrom n lo hi) := by
  intro n
  induction n with
  | zero => intro lo hi; rw [List.genSortedFrom]; exact SPMF.IsPMF_pure _
  | succ n ih =>
    intro lo hi
    rw [List.genSortedFrom]
    split
    · exact SPMF.IsPMF_stopOrGo (SPMF.IsPMF_pure _)
        (SPMF.IsPMF_bind (SPMF.IsPMF_chooseInt _ _ _) fun _ =>
          SPMF.IsPMF_bind (ih _ _) fun _ => SPMF.IsPMF_pure _)
    · exact SPMF.IsPMF_pure _

theorem List.genBoundedSorted.terminates (maxLen : Nat) (maxVal : Int) :
    IsAlmostSurelyTerminating (List.genBoundedSorted maxLen maxVal) :=
  List.genSortedFrom.terminates maxLen 0 maxVal

theorem List.genBoundedSorted.sound_complete :
    IsSoundAndComplete (List.genBoundedSorted maxLen maxVal)
      (List.boundedSorted maxLen maxVal) := by
  intro xs
  unfold List.genBoundedSorted List.boundedSorted
  rw [List.genSortedFrom_mem_support, List.isChain_cons_le_iff]
  grind

end SortedIntList
