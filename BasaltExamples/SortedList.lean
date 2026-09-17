/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt
import BasaltExamples.ArbNat

open RandomChoice ArbNat

/-!
# Sorted Lists

`List.genSorted` generates sorted `List Nat`s. It works by generating each element as the previous
one plus a `Nat.arbitrary` gap, threading the running lower bound `m` through the recursion:
`List.genSortedGt m` produces sorted lists whose every element is at least `m`; the recursion
*re-indexes the seed* (`genSortedGt x` for a new `x`), so `m` is the seed of its termination proof.
The public `genSorted` and its laws are the `m = 0` specializations.
-/

namespace SortedList

/-- Generates a sorted list whose every element is at least `m`: stop with `[]`, or draw a gap with
`Nat.arbitrary`, emit `m + gap`, and recurse with that as the new lower bound. -/
def List.genSortedGt [Gen G] (m : Nat) : G (List Nat) := do
  pick
    (fun () => pure [])
    (fun () => do
      let delta ← Nat.arbitrary
      let x := m + delta
      let xs ← List.genSortedGt x
      return x :: xs)
partial_fixpoint

/-- Generates an arbitrary sorted list, i.e. one with lower bound `0`. -/
def List.genSorted [Gen G] : G (List Nat) := List.genSortedGt 0

/-- The cost bound for `genSorted`. -/
def List.genSorted.costBound (xs : List Nat) : Nat :=
  xs.length + 1 + -- Cost of choosing `xs.length` cons-cells and one nil.
  xs.sum + xs.length -- Cost of choosing `xs.length` natural numbers `n`, each of which costs `n + 1`.

/-- The validity predicate: the list is (non-strictly) sorted. -/
def List.sorted (xs : List Nat) : Prop :=
  match xs with
  | [] => True
  | [_] => True
  | x :: y :: xs => x <= y ∧ List.sorted (y :: xs)

lemma List.sorted_cons_forall_le : List.sorted (x :: xs) → List.Forall (x ≤ ·) xs := by
  intro h
  induction xs
  case _ => simp
  case _ x xs ih => grind [= sorted.eq_def, sorted, List.forall_cons]

theorem List.genSortedGt_mem_support (xs : List Nat) (m : Nat) :
    xs ∈ SPMF.support (List.genSortedGt m) ↔ (List.sorted xs ∧ List.Forall (m ≤ ·) xs) := by
  fun_induction List.sorted generalizing m
  case _ =>
    unfold genSortedGt
    simp
  case _ x =>
    unfold genSortedGt
    simp
    constructor
    . grind
    . intro h
      exists x - m
      apply And.intro Nat.arbitrary_mem_support
      constructor
      . unfold genSortedGt
        simp
      . grind
  case _ x y xs ih =>
    unfold genSortedGt
    simp [ih, List.Forall, List.forall_cons]
    constructor
    . grind only [List.forall_iff_forall_mem, List.forall_cons]
    . intro h
      exists x - m
      grind only [
        List.forall_iff_forall_mem, List.Forall.eq_def, List.Forall.imp, List.sorted_cons_forall_le,
        sorted.eq_def, Nat.arbitrary_mem_support]

theorem List.genSortedGt.sound_complete :
    IsSoundAndComplete (List.genSortedGt m)
      (fun xs => List.sorted xs ∧ List.Forall (m ≤ ·) xs) :=
  fun xs => List.genSortedGt_mem_support xs m

theorem List.genSorted.sound_complete : IsSoundAndComplete List.genSorted List.sorted := by
  intro xs
  unfold genSorted
  simp [genSortedGt_mem_support, List.forall_iff_forall_mem]

theorem List.genSortedGt.terminates (m : Nat) : IsAlmostSurelyTerminating (List.genSortedGt m) := by
  mass_fixpoint using SPMF.LfpIsOne.affine (m := 1 / 2) (by norm_num)
  simp

theorem List.genSorted.terminates : IsAlmostSurelyTerminating List.genSorted :=
  List.genSortedGt.terminates 0

/-- Producing `xs` from `genSortedGt m` costs at most `xs.length + xs.sum + xs.length + 1` choices:
one per cons cell and the final nil, plus each element `n`'s `Nat.arbitrary` cost of `n + 1`. -/
theorem List.genSortedGt.cost_bounded :
    IsCostBounded (List.genSortedGt m) (fun xs => xs.length + xs.sum + xs.length + 1) := by
  cost_fixpoint
  all_goals simp only [List.length_nil, List.sum_nil, List.length_cons, List.sum_cons]; omega

theorem List.genSorted.cost_bounded :
    IsCostBounded List.genSorted List.genSorted.costBound :=
  IsBounded_mono List.genSortedGt.cost_bounded (by unfold genSorted.costBound; intro xs; omega)

end SortedList
