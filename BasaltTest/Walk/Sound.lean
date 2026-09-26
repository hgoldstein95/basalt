/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt
import BasaltExamples.BST
import BasaltExamples.Heap
import BasaltExamples.LeftistHeap

/-!
# The Soundness Walk Contract

Pins the step `walk fixpoint` leaves on `SPMF.alwaysObs.spec`: the recursive function named after
the generator, `ih` over the arguments its recursive calls change, and one goal per path, stated on
the value the path built under the generator's own names.
-/

open RandomChoice

namespace SoundBoundTest

/-! A callee (`Nat.arbitrary`) is closed by the `sound` half of its `.sound_complete` law, passed as
a fact on its observation. -/

/--
trace: genHeap : ℕ → SPMF Heap.Tree
ih : ∀ (lo : ℕ), SPMF.alwaysObs.spec (genHeap lo) (Heap.Tree.isHeap lo)
lo : ℕ
⊢ Heap.Tree.isHeap lo Heap.Tree.leaf

genHeap : ℕ → SPMF Heap.Tree
ih : ∀ (lo : ℕ), SPMF.alwaysObs.spec (genHeap lo) (Heap.Tree.isHeap lo)
lo delta✝ : ℕ
h_delta✝ : ⊤ delta✝
l✝ : Heap.Tree
h_l✝ : Heap.Tree.isHeap (lo + delta✝) l✝
r✝ : Heap.Tree
h_r✝ : Heap.Tree.isHeap (lo + delta✝) r✝
⊢ Heap.Tree.isHeap lo (l✝.node (lo + delta✝) r✝)
-/
#guard_msgs in
example : IsSoundFor (Heap.Tree.genHeap lo) (Heap.Tree.isHeap lo) := by
  rw [IsSoundFor.iff_obs]
  walk fixpoint [ArbNat.Nat.arbitrary.sound_complete.sound.obs]
  trace_state
  all_goals simp_all [Heap.Tree.isHeap]

/-! A `dite` on the seed, a `frequency`, and a `chooseInt` pivot. -/

/--
trace: genBST : ℤ → ℤ → SPMF (BST.Tree ℤ)
ih : ∀ (lo hi : ℤ), SPMF.alwaysObs.spec (genBST lo hi) (BST.Tree.isBST lo hi)
lo hi : ℤ
h✝ : lo > hi
⊢ BST.Tree.isBST lo hi BST.Tree.leaf

genBST : ℤ → ℤ → SPMF (BST.Tree ℤ)
ih : ∀ (lo hi : ℤ), SPMF.alwaysObs.spec (genBST lo hi) (BST.Tree.isBST lo hi)
lo hi : ℤ
h✝ : ¬lo > hi
⊢ BST.Tree.isBST lo hi BST.Tree.leaf

genBST : ℤ → ℤ → SPMF (BST.Tree ℤ)
ih : ∀ (lo hi : ℤ), SPMF.alwaysObs.spec (genBST lo hi) (BST.Tree.isBST lo hi)
lo hi : ℤ
h✝ : ¬lo > hi
x✝ : ℤ
h_x✝ : lo ≤ x✝ ∧ x✝ ≤ hi
l✝ : BST.Tree ℤ
h_l✝ : BST.Tree.isBST lo (x✝ - 1) l✝
r✝ : BST.Tree ℤ
h_r✝ : BST.Tree.isBST (x✝ + 1) hi r✝
⊢ BST.Tree.isBST lo hi (l✝.node x✝ r✝)
-/
#guard_msgs in
example : IsSoundFor (BST.Tree.genBST lo hi) (BST.Tree.isBST lo hi) := by
  rw [IsSoundFor.iff_obs]
  walk fixpoint
  trace_state
  all_goals simp_all [BST.Tree.isBST]

/-! An `if` on two drawn values is two paths. -/

/--
trace: genLeftist : ℕ → SPMF LeftistHeap.Tree
ih : ∀ (lo : ℕ), SPMF.alwaysObs.spec (genLeftist lo) (LeftistHeap.Tree.isLeftist lo)
lo : ℕ
⊢ LeftistHeap.Tree.isLeftist lo LeftistHeap.Tree.leaf

genLeftist : ℕ → SPMF LeftistHeap.Tree
ih : ∀ (lo : ℕ), SPMF.alwaysObs.spec (genLeftist lo) (LeftistHeap.Tree.isLeftist lo)
lo delta✝ : ℕ
h_delta✝ : ⊤ delta✝
a✝ : LeftistHeap.Tree
h_a✝ : LeftistHeap.Tree.isLeftist (lo + delta✝) a✝
b✝ : LeftistHeap.Tree
h_b✝ : LeftistHeap.Tree.isLeftist (lo + delta✝) b✝
_h✝ : b✝.rank ≤ a✝.rank
⊢ LeftistHeap.Tree.isLeftist lo (a✝.node (lo + delta✝) b✝)

genLeftist : ℕ → SPMF LeftistHeap.Tree
ih : ∀ (lo : ℕ), SPMF.alwaysObs.spec (genLeftist lo) (LeftistHeap.Tree.isLeftist lo)
lo delta✝ : ℕ
h_delta✝ : ⊤ delta✝
a✝ : LeftistHeap.Tree
h_a✝ : LeftistHeap.Tree.isLeftist (lo + delta✝) a✝
b✝ : LeftistHeap.Tree
h_b✝ : LeftistHeap.Tree.isLeftist (lo + delta✝) b✝
_h✝ : ¬b✝.rank ≤ a✝.rank
⊢ LeftistHeap.Tree.isLeftist lo (b✝.node (lo + delta✝) a✝)
-/
#guard_msgs in
example : IsSoundFor (LeftistHeap.Tree.genLeftist lo) (LeftistHeap.Tree.isLeftist lo) := by
  rw [IsSoundFor.iff_obs]
  walk fixpoint [ArbNat.Nat.arbitrary.sound_complete.sound.obs]
  trace_state
  all_goals simp_all [LeftistHeap.Tree.isLeftist]
  all_goals omega

/-! A generator defined by `match` on its seed is split into its cases before the walk. -/

/--
trace: genLeftistOfRank : ℕ → ℕ → SPMF LeftistHeap.Tree
ih : ∀ (lo a : ℕ), SPMF.alwaysObs.spec (genLeftistOfRank lo a) fun t => LeftistHeap.Tree.isLeftist lo t ∧ t.rank = a
lo x : ℕ
⊢ LeftistHeap.Tree.isLeftist lo LeftistHeap.Tree.leaf

genLeftistOfRank : ℕ → ℕ → SPMF LeftistHeap.Tree
ih : ∀ (lo a : ℕ), SPMF.alwaysObs.spec (genLeftistOfRank lo a) fun t => LeftistHeap.Tree.isLeftist lo t ∧ t.rank = a
lo x : ℕ
⊢ LeftistHeap.Tree.leaf.rank = 0

genLeftistOfRank : ℕ → ℕ → SPMF LeftistHeap.Tree
ih : ∀ (lo a : ℕ), SPMF.alwaysObs.spec (genLeftistOfRank lo a) fun t => LeftistHeap.Tree.isLeftist lo t ∧ t.rank = a
lo x k delta✝ : ℕ
h_delta✝ : ⊤ delta✝
r✝ : LeftistHeap.Tree
h_r✝ : LeftistHeap.Tree.isLeftist (lo + delta✝) r✝ ∧ r✝.rank = k
gap✝ : ℕ
h_gap✝ : ⊤ gap✝
l✝ : LeftistHeap.Tree
h_l✝ : LeftistHeap.Tree.isLeftist (lo + delta✝) l✝ ∧ l✝.rank = k + gap✝
⊢ LeftistHeap.Tree.isLeftist lo (l✝.node (lo + delta✝) r✝)

genLeftistOfRank : ℕ → ℕ → SPMF LeftistHeap.Tree
ih : ∀ (lo a : ℕ), SPMF.alwaysObs.spec (genLeftistOfRank lo a) fun t => LeftistHeap.Tree.isLeftist lo t ∧ t.rank = a
lo x k delta✝ : ℕ
h_delta✝ : ⊤ delta✝
r✝ : LeftistHeap.Tree
h_r✝ : LeftistHeap.Tree.isLeftist (lo + delta✝) r✝ ∧ r✝.rank = k
gap✝ : ℕ
h_gap✝ : ⊤ gap✝
l✝ : LeftistHeap.Tree
h_l✝ : LeftistHeap.Tree.isLeftist (lo + delta✝) l✝ ∧ l✝.rank = k + gap✝
⊢ (l✝.node (lo + delta✝) r✝).rank = k.succ
-/
#guard_msgs in
example : IsSoundFor (LeftistHeap.Tree.genLeftistOfRank lo k)
    (fun t => LeftistHeap.Tree.isLeftist lo t ∧ t.rank = k) := by
  rw [IsSoundFor.iff_obs]
  walk fixpoint [ArbNat.Nat.arbitrary.sound_complete.sound.obs]
  trace_state
  all_goals simp_all [LeftistHeap.Tree.isLeftist, LeftistHeap.Tree.rank]

/-! A `match` on a drawn value is not entered. -/

/--
error: the walk does not enter a `match`:
  match x with
  | 0 => pure 0
  | n.succ => pure n
One on the generator's arguments is split before the walk; one on a drawn value, or inside a helper the walk unfolds, is not supported.
-/
#guard_msgs in
example : IsSoundFor (ArbNat.Nat.arbitrary >>= fun x => match x with
    | 0 => Pure.pure 0 | n + 1 => Pure.pure n : SPMF Nat) (fun _ => True) := by
  rw [IsSoundFor.iff_obs]
  walk

/-! A `match` on an argument inside a branch is split before the walk, as one at the head is. -/

def genBelow [Gen G] (n : Nat) : G Nat :=
  oneOf [fun _ => pure 0, fun _ => match n with | 0 => pure 0 | k + 1 => genBelow k]
partial_fixpoint

/--
trace: genBelow : ℕ → SPMF ℕ
ih : ∀ (n : ℕ), SPMF.alwaysObs.spec (genBelow n) fun x => x ≤ n
n : ℕ
⊢ 0 ≤ 0

genBelow : ℕ → SPMF ℕ
ih : ∀ (n : ℕ), SPMF.alwaysObs.spec (genBelow n) fun x => x ≤ n
n : ℕ
⊢ 0 ≤ 0

genBelow : ℕ → SPMF ℕ
ih : ∀ (n : ℕ), SPMF.alwaysObs.spec (genBelow n) fun x => x ≤ n
n k : ℕ
⊢ 0 ≤ k.succ

genBelow : ℕ → SPMF ℕ
ih : ∀ (n : ℕ), SPMF.alwaysObs.spec (genBelow n) fun x => x ≤ n
n k x✝ : ℕ
h_x✝ : x✝ ≤ k
⊢ x✝ ≤ k.succ
-/
#guard_msgs in
example : IsSoundFor (genBelow n) (· ≤ n) := by
  rw [IsSoundFor.iff_obs]
  walk fixpoint
  trace_state
  all_goals omega

/-! One inside a helper is met only once the walk has unfolded it, and is not split. -/

def pickBelow [Gen G] (n : Nat) : G Nat := match n with | 0 => pure 0 | k + 1 => pure k

/--
error: the walk does not enter a `match`:
  match n with
  | 0 => pure 0
  | k.succ => pure k
One on the generator's arguments is split before the walk; one on a drawn value, or inside a helper the walk unfolds, is not supported.
(in the unfolding of `SoundBoundTest.pickBelow`)
-/
#guard_msgs in
example :
    IsSoundFor (oneOf [fun _ => pure 0, fun _ => pickBelow n] (by simp) : SPMF Nat) (· ≤ n) := by
  rw [IsSoundFor.iff_obs]
  walk

/-! A callee that has only a half of the law is closed by that half, passed as a fact. -/

def genTwo [Gen G] : G Nat := pure 2

theorem genTwo.sound : IsSoundFor (genTwo (G := SPMF)) (· = 2) := by
  rw [IsSoundFor.iff_obs]
  walk fixpoint
  rfl

/--
trace: n✝ : ℕ
h_n✝ : n✝ = 2
⊢ n✝ + 1 = 3
-/
#guard_msgs in
example : IsSoundFor (genTwo >>= fun n => pure (n + 1) : SPMF Nat) (· = 3) := by
  rw [IsSoundFor.iff_obs]
  walk [genTwo.sound.obs]
  trace_state
  omega

/-! `permutationOf` asks nothing of the postcondition: the value it draws carries its proof. -/

/--
trace: xs : List ℕ
a✝ : { ys // xs.Perm ys }
⊢ xs.Perm ↑a✝
-/
#guard_msgs in
example (xs : List Nat) : IsSoundFor ((·.1) <$> permutationOf xs : SPMF (List Nat)) xs.Perm := by
  rw [IsSoundFor.iff_obs]
  walk
  trace_state
  next a => exact a.2

/-! The combined law is split by hand; `walk` takes a half. -/

/--
error: walk: expected a statement on an observation, `O.spec (gen …) post`, `b ≤ O.spec (gen …) post`, or `O.spec (gen …) post ≤ b`, or a relation tagged `@[walk_rel]`, got
  IsSoundAndComplete (Heap.Tree.genHeap lo) (Heap.Tree.isHeap lo)
Split the law into its halves first: `refine .intro ?sound ?complete`.
-/
#guard_msgs in
example : IsSoundAndComplete (Heap.Tree.genHeap lo) (Heap.Tree.isHeap lo) := by
  walk fixpoint

/-! A law is walked on its observation: the goal is restated by `iff_obs` first, and a fact is
passed as `.obs`. -/

/--
error: walk: expected a statement on an observation, `O.spec (gen …) post`, `b ≤ O.spec (gen …) post`, or `O.spec (gen …) post ≤ b`, or a relation tagged `@[walk_rel]`, got
  IsSoundFor
    (do
      let n ← genTwo
      pure (n + 1))
    fun x => x = 3
Restate it on its observation first: `rw [IsSoundFor.iff_obs]`.
-/
#guard_msgs in
example : IsSoundFor (genTwo >>= fun n => pure (n + 1) : SPMF Nat) (· = 3) := by
  walk [genTwo.sound.obs]

/--
error: walk: the fact
  genTwo.sound
is stated as `IsSoundFor`; a walk takes facts stated on an observation. Pass `genTwo.sound.obs`.
-/
#guard_msgs in
example : IsSoundFor (genTwo >>= fun n => pure (n + 1) : SPMF Nat) (· = 3) := by
  rw [IsSoundFor.iff_obs]
  walk [genTwo.sound]

end SoundBoundTest
