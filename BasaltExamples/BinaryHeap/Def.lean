/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt

/-!
# Array-Backed Binary Heaps

A binary min-heap in its imperative representation: a `List Nat` read as a complete binary tree,
the children of index `i` sitting at `2 * i + 1` and `2 * i + 2`. This module fixes the heap
invariant and encodes `dequeue` — remove the root, move the last element into it, sift that value
down — so that a generator's predicate can constrain the number of sift-down swaps.
-/

namespace BinaryHeap

/-- A heap is an array of values bounded by `maxVal` in which no element exceeds either of its
children under the implicit complete-tree indexing. -/
def IsHeap (maxVal : Nat) (a : List Nat) : Prop :=
  (∀ x ∈ a, x ≤ maxVal) ∧
  ∀ i, ∀ p ∈ a[i]?, (∀ l ∈ a[2 * i + 1]?, p ≤ l) ∧ (∀ r ∈ a[2 * i + 2]?, p ≤ r)

/-- The index and value of the smaller child of `i`, preferring the left child on a tie. -/
def minChild (a : List Nat) (i : Nat) : Option (Nat × Nat) :=
  match a[2 * i + 1]?, a[2 * i + 2]? with
  | none, _ => none
  | some l, none => some (2 * i + 1, l)
  | some l, some r => if r < l then some (2 * i + 2, r) else some (2 * i + 1, l)

/-- Sift `x` down into the hole at index `i`, returning the array and the number of swaps. Each
swap moves the smaller child up and follows it; `fuel` bounds the descent. -/
def siftDown : Nat → List Nat → Nat → Nat → List Nat × Nat
  | 0, a, i, x => (a.set i x, 0)
  | fuel + 1, a, i, x =>
    match minChild a i with
    | none => (a.set i x, 0)
    | some (j, y) =>
      if y < x then
        let r := siftDown fuel (a.set i y) j x
        (r.1, r.2 + 1)
      else
        (a.set i x, 0)

/-- Remove the minimum: the last element takes the root's place and sifts down. -/
def dequeue (a : List Nat) : List Nat × Nat :=
  match a.getLast? with
  | none => ([], 0)
  | some last => siftDown a.length a.dropLast 0 last

end BinaryHeap
