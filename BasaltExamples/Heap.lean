/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt
import BasaltExamples.ArbNat

open RandomChoice ArbNat

/-!
# Min-Heaps

`Tree.genHeap lo` generates arbitrary binary min-heaps whose values are all at least `lo`. It draws
each node's value as `lo` plus a `Nat.arbitrary` gap, then recurses on both children with that
value as the new lower bound. Like `SortedList`, the recursion re-indexes the seed; unlike it,
recursing on *two* children makes the mean offspring exactly `1`, so this is a **critical**
generator (almost surely terminating, infinite expected size).
-/

namespace Heap

/-- A binary tree with `Nat`-labelled nodes. -/
inductive Tree where
  | leaf : Tree
  | node : Tree → Nat → Tree → Tree
deriving Repr

/-- The number of nodes in the tree. -/
def Tree.size : Tree → Nat
  | leaf => 0
  | node l _ r => l.size + r.size + 1

/-- The sum of every value stored in the tree. -/
def Tree.sum : Tree → Nat
  | leaf => 0
  | node l x r => l.sum + x + r.sum

/-- A `Tree` is a min-heap bounded below by `lo` when every node's value is at
    least `lo` and each subtree is itself a min-heap bounded below by that node's
    value. -/
def Tree.isHeap (lo : Nat) : Tree → Prop
  | leaf => True
  | node l x r =>
    lo ≤ x ∧
    isHeap x l ∧
    isHeap x r

/-- Generates an arbitrary min-heap whose values are all at least `lo`. -/
def Tree.genHeap [Gen G] (lo : Nat) : G Tree :=
  pick
    (fun () => pure leaf)
    (fun () => do
      let delta ← Nat.arbitrary
      let x := lo + delta
      let l ← Tree.genHeap x
      let r ← Tree.genHeap x
      return node l x r)
partial_fixpoint

theorem Tree.genHeap.sound_complete :
    IsSoundAndComplete (Tree.genHeap lo) (Tree.isHeap lo) := by
  intro t
  induction t generalizing lo with
  | leaf =>
    rw [Tree.genHeap]
    simp [Tree.isHeap]
  | node l x r ihl ihr =>
    rw [Tree.genHeap]
    support_simp [Tree.isHeap, Tree.node.injEq, Nat.arbitrary_mem_support, true_and]
    constructor
    · rintro (h | ⟨d, l', hl', r', hr', hle, hld, hrd⟩)
      · simp at h
      · subst hld hle hrd
        exact ⟨by omega, ihl.mp hl', ihr.mp hr'⟩
    · rintro ⟨hle, hl, hr⟩
      right
      refine ⟨x - lo, l, ?_, r, ?_, rfl, by omega, rfl⟩
      · rw [show lo + (x - lo) = x by omega]; exact ihl.mpr hl
      · rw [show lo + (x - lo) = x by omega]; exact ihr.mpr hr

theorem Tree.genHeap.terminates : IsAlmostSurelyTerminating (Tree.genHeap lo) := by
  mass_fixpoint using SPMF.LfpIsOne.quadratic (a := 1 / 2) (b := 0) (d := 1 / 2)
    (by ennreal_to_real; norm_num) (by ennreal_to_real; norm_num) (by norm_num)
  simp [sq]

/-- The number of random choices is bounded by the tree's size and value-sum (no backtracking). -/
theorem Tree.genHeap.cost_bounded :
    IsCostBounded (Tree.genHeap lo) (fun t => 3 * t.size + t.sum + 1) := by
  cost_fixpoint
  all_goals simp only [Tree.size, Tree.sum]; omega

end Heap
