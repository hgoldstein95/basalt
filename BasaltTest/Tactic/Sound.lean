/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt
import BasaltExamples.BST
import BasaltExamples.Heap
import BasaltExamples.LeftistHeap

open RandomChoice

/-!
# The `sound_bound` and `sound_fixpoint` Contract

Pins the step `sound_fixpoint` leaves: the recursive function named after the generator, `ih` over
the arguments its recursive calls change, and one goal per path, stated on the value the path built
under the generator's own names.
-/

namespace SoundBoundTest

/-! A callee (`Nat.arbitrary`) is closed by its `.sound_complete` law. -/

/--
trace: genHeap : ℕ → SPMF Heap.Tree
ih : ∀ (lo : ℕ), IsSound (genHeap lo) (Heap.Tree.isHeap lo)
lo : ℕ
⊢ Heap.Tree.isHeap lo Heap.Tree.leaf

genHeap : ℕ → SPMF Heap.Tree
ih : ∀ (lo : ℕ), IsSound (genHeap lo) (Heap.Tree.isHeap lo)
lo delta : ℕ
h_delta : ⊤ delta
l : Heap.Tree
h_l : Heap.Tree.isHeap (lo + delta) l
r : Heap.Tree
h_r : Heap.Tree.isHeap (lo + delta) r
⊢ Heap.Tree.isHeap lo (l.node (lo + delta) r)
-/
#guard_msgs in
example : IsSound (Heap.Tree.genHeap lo) (Heap.Tree.isHeap lo) := by
  sound_fixpoint
  trace_state
  all_goals simp_all [Heap.Tree.isHeap]

/-! A `dite` on the seed, a `frequency`, and a `chooseInt` pivot. -/

/--
trace: genBST : ℤ → ℤ → SPMF (BST.Tree ℤ)
ih : ∀ (lo hi : ℤ), IsSound (genBST lo hi) (BST.Tree.isBST lo hi)
lo hi : ℤ
h : lo > hi
⊢ BST.Tree.isBST lo hi BST.Tree.leaf

genBST : ℤ → ℤ → SPMF (BST.Tree ℤ)
ih : ∀ (lo hi : ℤ), IsSound (genBST lo hi) (BST.Tree.isBST lo hi)
lo hi : ℤ
h : ¬lo > hi
⊢ BST.Tree.isBST lo hi BST.Tree.leaf

genBST : ℤ → ℤ → SPMF (BST.Tree ℤ)
ih : ∀ (lo hi : ℤ), IsSound (genBST lo hi) (BST.Tree.isBST lo hi)
lo hi : ℤ
h : ¬lo > hi
x : ℤ
h_x : lo ≤ x ∧ x ≤ hi
l : BST.Tree ℤ
h_l : BST.Tree.isBST lo (x - 1) l
r : BST.Tree ℤ
h_r : BST.Tree.isBST (x + 1) hi r
⊢ BST.Tree.isBST lo hi (l.node x r)
-/
#guard_msgs in
example : IsSound (BST.Tree.genBST lo hi) (BST.Tree.isBST lo hi) := by
  sound_fixpoint
  trace_state
  all_goals simp_all [BST.Tree.isBST]

/-! An `if` on two drawn values is two paths. -/

/--
trace: genLeftist : ℕ → SPMF LeftistHeap.Tree
ih : ∀ (lo : ℕ), IsSound (genLeftist lo) (LeftistHeap.Tree.isLeftist lo)
lo : ℕ
⊢ LeftistHeap.Tree.isLeftist lo LeftistHeap.Tree.leaf

genLeftist : ℕ → SPMF LeftistHeap.Tree
ih : ∀ (lo : ℕ), IsSound (genLeftist lo) (LeftistHeap.Tree.isLeftist lo)
lo delta : ℕ
h_delta : ⊤ delta
a : LeftistHeap.Tree
h_a : LeftistHeap.Tree.isLeftist (lo + delta) a
b : LeftistHeap.Tree
h_b : LeftistHeap.Tree.isLeftist (lo + delta) b
_h : b.rank ≤ a.rank
⊢ LeftistHeap.Tree.isLeftist lo (a.node (lo + delta) b)

genLeftist : ℕ → SPMF LeftistHeap.Tree
ih : ∀ (lo : ℕ), IsSound (genLeftist lo) (LeftistHeap.Tree.isLeftist lo)
lo delta : ℕ
h_delta : ⊤ delta
a : LeftistHeap.Tree
h_a : LeftistHeap.Tree.isLeftist (lo + delta) a
b : LeftistHeap.Tree
h_b : LeftistHeap.Tree.isLeftist (lo + delta) b
_h : ¬b.rank ≤ a.rank
⊢ LeftistHeap.Tree.isLeftist lo (b.node (lo + delta) a)
-/
#guard_msgs in
example : IsSound (LeftistHeap.Tree.genLeftist lo) (LeftistHeap.Tree.isLeftist lo) := by
  sound_fixpoint
  trace_state
  all_goals simp_all [LeftistHeap.Tree.isLeftist]
  all_goals omega

/-! A generator defined by `match` on its seed is split into its cases before the walk. -/

/--
trace: genLeftistOfRank : ℕ → ℕ → SPMF LeftistHeap.Tree
ih : ∀ (lo a : ℕ), IsSound (genLeftistOfRank lo a) fun t => LeftistHeap.Tree.isLeftist lo t ∧ t.rank = a
lo x : ℕ
⊢ LeftistHeap.Tree.isLeftist lo LeftistHeap.Tree.leaf

genLeftistOfRank : ℕ → ℕ → SPMF LeftistHeap.Tree
ih : ∀ (lo a : ℕ), IsSound (genLeftistOfRank lo a) fun t => LeftistHeap.Tree.isLeftist lo t ∧ t.rank = a
lo x : ℕ
⊢ LeftistHeap.Tree.leaf.rank = 0

genLeftistOfRank : ℕ → ℕ → SPMF LeftistHeap.Tree
ih : ∀ (lo a : ℕ), IsSound (genLeftistOfRank lo a) fun t => LeftistHeap.Tree.isLeftist lo t ∧ t.rank = a
lo x k delta : ℕ
h_delta : ⊤ delta
r : LeftistHeap.Tree
h_r : LeftistHeap.Tree.isLeftist (lo + delta) r ∧ r.rank = k
gap : ℕ
h_gap : ⊤ gap
l : LeftistHeap.Tree
h_l : LeftistHeap.Tree.isLeftist (lo + delta) l ∧ l.rank = k + gap
⊢ LeftistHeap.Tree.isLeftist lo (l.node (lo + delta) r)

genLeftistOfRank : ℕ → ℕ → SPMF LeftistHeap.Tree
ih : ∀ (lo a : ℕ), IsSound (genLeftistOfRank lo a) fun t => LeftistHeap.Tree.isLeftist lo t ∧ t.rank = a
lo x k delta : ℕ
h_delta : ⊤ delta
r : LeftistHeap.Tree
h_r : LeftistHeap.Tree.isLeftist (lo + delta) r ∧ r.rank = k
gap : ℕ
h_gap : ⊤ gap
l : LeftistHeap.Tree
h_l : LeftistHeap.Tree.isLeftist (lo + delta) l ∧ l.rank = k + gap
⊢ (l.node (lo + delta) r).rank = k.succ
-/
#guard_msgs in
example : IsSound (LeftistHeap.Tree.genLeftistOfRank lo k)
    (fun t => LeftistHeap.Tree.isLeftist lo t ∧ t.rank = k) := by
  sound_fixpoint
  trace_state
  all_goals simp_all [LeftistHeap.Tree.isLeftist, LeftistHeap.Tree.rank]

/-! A `match` on a drawn value is not entered. -/

/--
error: the walk does not enter a `match`:
  match x with
  | 0 => pure 0
  | n.succ => pure n
One on the generator's arguments is split before the walk when the generator is headed by it; one on a drawn value is not supported.
-/
#guard_msgs in
example : IsSound (ArbNat.Nat.arbitrary >>= fun x => match x with
    | 0 => Pure.pure 0 | n + 1 => Pure.pure n : SPMF Nat) (fun _ => True) := by
  sound_bound

/-! A callee that has only a half of the law is closed by that half. -/

def genTwo [Gen G] : G Nat := pure 2

theorem genTwo.sound : IsSound (genTwo (G := SPMF)) (· = 2) := by
  sound_fixpoint
  rfl

/--
trace: n : ℕ
h_n : n = 2
⊢ n + 1 = 3
-/
#guard_msgs in
example : IsSound (genTwo >>= fun n => pure (n + 1) : SPMF Nat) (· = 3) := by
  sound_bound
  trace_state
  omega

/-! The combined law is split by hand; the tactics take a half. -/

/--
error: sound_bound: expected a goal `IsSound (gen …) P`, got
  IsSoundAndComplete (Heap.Tree.genHeap lo) (Heap.Tree.isHeap lo)
Split the law into its halves first: `refine .intro ?sound ?complete`.
-/
#guard_msgs in
example : IsSoundAndComplete (Heap.Tree.genHeap lo) (Heap.Tree.isHeap lo) := by
  sound_fixpoint

end SoundBoundTest
