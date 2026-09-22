/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt
import BasaltExamples.BST
import BasaltExamples.Heap
import BasaltExamples.SortedList

/-!
# The `complete_bound` Contract

Pins the precondition `complete_bound` leaves: an `∃` per draw under the generator's names, the
refuted branches pruned and the surviving ones not chosen between, and a recursive occurrence left as
itself. The recursive generators are copies of the cookbook's that carry no law, which the walk would
otherwise close a recursive occurrence with.
-/

open RandomChoice ArbNat

namespace CompleteBoundTest

/-! ## By an induction on the value

Both recursive occurrences must appear: a hypothesis of the induction that closed one as a leaf
would drop it from the precondition silently. -/

def genHeap [Gen G] (lo : Nat) : G Heap.Tree :=
  oneOf [
    fun _ => pure .leaf,
    fun _ => do
      let delta ← Nat.arbitrary
      let x := lo + delta
      let l ← genHeap x
      let r ← genHeap x
      return .node l x r]
partial_fixpoint

/--
trace: l r : Heap.Tree
ihl : ∀ {lo : ℕ}, Heap.Tree.isHeap lo l → l ∈ (genHeap lo).support
ihr : ∀ {lo : ℕ}, Heap.Tree.isHeap lo r → r ∈ (genHeap lo).support
lo d : ℕ
hle : lo ≤ lo + d
hl : Heap.Tree.isHeap (lo + d) l
hr : Heap.Tree.isHeap (lo + d) r
⊢ ∃ delta,
    ∃ l_1 ∈ (genHeap (lo + delta)).support,
      ∃ r_1 ∈ (genHeap (lo + delta)).support, l_1.node (lo + delta) r_1 = l.node (lo + d) r
-/
#guard_msgs in
example : IsSoundAndComplete (genHeap lo) (Heap.Tree.isHeap lo) := by
  refine .intro ?sound ?complete
  case sound =>
    sound_fixpoint
    all_goals simp_all [Heap.Tree.isHeap]
  case complete =>
    intro t
    induction t generalizing lo with
    | leaf => intro _; rw [genHeap]; complete_bound
    | node l x r ihl ihr =>
      intro ht
      obtain ⟨hle, hl, hr⟩ := ht
      obtain ⟨d, rfl⟩ : ∃ d, x = lo + d := ⟨x - lo, by omega⟩
      rw [genHeap]; complete_bound
      trace_state
      exact ⟨d, l, ihl hl, r, ihr hr, rfl⟩

def genBST [Gen G] (lo hi : Int) : G (BST.Tree Int) := do
  if h : lo > hi then
    return .leaf
  else
    frequency [
      (1, fun () => pure .leaf),
      (1, fun () => do
        let x ← chooseInt lo hi (by omega)
        let l ← genBST lo (x - 1)
        let r ← genBST (x + 1) hi
        return .node l x r)
    ] (by simp)
partial_fixpoint

/-! A conditional the walk cannot decide stays; the `frequency` branch that builds a `leaf` is
pruned, and the other's weight is decided. -/

/--
trace: l : BST.Tree ℤ
x : ℤ
r : BST.Tree ℤ
ihl : ∀ {lo hi : ℤ}, BST.Tree.isBST lo hi l → l ∈ (genBST lo hi).support
ihr : ∀ {lo hi : ℤ}, BST.Tree.isBST lo hi r → r ∈ (genBST lo hi).support
lo hi : ℤ
h1 : lo ≤ x
h2 : x ≤ hi
hl : BST.Tree.isBST lo (x - 1) l
hr : BST.Tree.isBST (x + 1) hi r
⊢ if h : lo > hi then False
  else
    ∃ x_1,
      (lo ≤ x_1 ∧ x_1 ≤ hi) ∧
        ∃ l_1 ∈ (genBST lo (x_1 - 1)).support, ∃ r_1 ∈ (genBST (x_1 + 1) hi).support, l_1.node x_1 r_1 = l.node x r
-/
#guard_msgs in
example : IsCompleteFor (genBST lo hi) (BST.Tree.isBST lo hi) := by
  intro t
  induction t generalizing lo hi with
  | leaf => intro _; rw [genBST]; complete_bound
  | node l x r ihl ihr =>
    intro ht
    obtain ⟨h1, h2, hl, hr⟩ := ht
    rw [genBST]; complete_bound
    trace_state
    rw [dif_neg (by omega)]
    exact ⟨x, ⟨h1, h2⟩, l, ihl hl, r, ihr hr, rfl⟩

/-! ## By a measure

The induction hypothesis of `IsCompleteFor.of_measure` closes the recursive occurrence, so the
precondition has no generator in it. -/

def genSortedGt [Gen G] (m : Nat) : G (List Nat) := do
  oneOf [
    fun _ => pure [],
    fun _ => do
      let delta ← Nat.arbitrary
      let x := m + delta
      let xs ← genSortedGt x
      return x :: xs]
partial_fixpoint

open SortedList in
/--
trace: m✝ n : ℕ
ih : ∀ (s : ℕ) (a : List ℕ), a.length < n → List.sorted a ∧ List.Forall (fun x => s ≤ x) a → a ∈ (genSortedGt s).support
m : ℕ
xs : List ℕ
hn : xs.length < n + 1
hP : List.sorted xs ∧ List.Forall (fun x => m ≤ x) xs
⊢ [] = xs ∨
    ∃ delta xs_1,
      (xs_1.length < n ∧ List.sorted xs_1 ∧ List.Forall (fun x => m + delta ≤ x) xs_1) ∧ (m + delta) :: xs_1 = xs
-/
#guard_msgs in
example : IsCompleteFor (genSortedGt m) (fun xs => List.sorted xs ∧ List.Forall (m ≤ ·) xs) := by
  apply IsCompleteFor.of_measure (fun _ xs => xs.length) fun n ih m xs hn hP => ?_
  rw [genSortedGt]; complete_bound
  trace_state
  match xs, hP with
  | [], _ => exact .inl rfl
  | x :: xs, ⟨hs, hf⟩ =>
    have hx : m ≤ x := List.forall_iff_forall_mem.mp hf x (by simp)
    obtain ⟨d, rfl⟩ : ∃ d, x = m + d := ⟨x - m, by omega⟩
    refine .inr ⟨d, xs, ⟨⟨by simpa using hn, ?_, List.sorted_cons_forall_le hs⟩, rfl⟩⟩
    cases xs with
    | nil => trivial
    | cons y ys => exact hs.2

/-! ## Every combinator -/

/-- One branch per combinator that takes no generator argument, a `frequency` branch of weight `0`,
and a `coin`. `Nat.arbitrary` is a callee: the tactic finds its `.sound_complete` law by name. -/
def gen [Gen G] (b : Bool) : G Nat := do
  let x ← oneOf [
    fun () => pure 0,
    fun () => frequency [(1, fun () => chooseNat 0 3), (0, fun () => elements [4, 5])],
    fun () => if b then Nat.arbitrary else (·.down.val) <$> choose 0 1 (by simp)
  ]
  let y ← oneOf [fun () => pure 1, fun () => chooseInt 0 2 >>= fun z => pure z.toNat]
  let c ← coin (1/3)
  return (if c then x + y else 0)

-- The weight-`0` branch is gone, and so are the coin's two reachability conditions.
/--
trace: b : Bool
n : ℕ
hn : n ≤ 1
⊢ ((0 + 1 = n ∨ 0 = n) ∨ ∃ z, (0 ≤ z ∧ z ≤ 2) ∧ (0 + z.toNat = n ∨ 0 = n)) ∨
    (∃ x, (0 ≤ x ∧ x ≤ 3) ∧ ((x + 1 = n ∨ 0 = n) ∨ ∃ z, (0 ≤ z ∧ z ≤ 2) ∧ (x + z.toNat = n ∨ 0 = n))) ∨
      if b = true then ∃ x, (x + 1 = n ∨ 0 = n) ∨ ∃ z, (0 ≤ z ∧ z ≤ 2) ∧ (x + z.toNat = n ∨ 0 = n)
      else ∃ x, (0 ≤ x ∧ x ≤ 1) ∧ ((x + 1 = n ∨ 0 = n) ∨ ∃ z, (0 ≤ z ∧ z ≤ 2) ∧ (x + z.toNat = n ∨ 0 = n))
-/
#guard_msgs in
example (b : Bool) (n : Nat) (hn : n ≤ 1) : n ∈ (gen b : SPMF Nat).support := by
  unfold gen
  complete_bound
  trace_state
  exact .inl (.inl (by omega))

/-! ## A generator nothing is known about

It stays in the precondition, where another walk fails. -/

/--
trace: g : SPMF ℕ
hg : 3 ∈ g.support
⊢ ∃ x, x ∈ g.support
-/
#guard_msgs in
example (g : SPMF Nat) (hg : 3 ∈ g.support) : 0 ∈ (g >>= fun _ => pure 0).support := by
  complete_bound
  trace_state
  exact ⟨3, hg⟩

/-! A callee that has only the `.complete` half of the law is reached through it. -/

def genTwo [Gen G] : G Nat := pure 2

theorem genTwo.complete : IsCompleteFor (genTwo (G := SPMF)) (· = 2) := by
  intro n hn
  rw [genTwo]; complete_bound
  exact hn.symm

/--
trace: ⊢ ∃ n, n = 2 ∧ n + 1 = 3
-/
#guard_msgs in
example : 3 ∈ (genTwo >>= fun n => pure (n + 1) : SPMF Nat).support := by
  complete_bound
  trace_state
  exact ⟨2, rfl, rfl⟩

/-! ## A run with its cost

At `SPMF.Cost` the value is a run, and the precondition carries the choices it took. A combinator
with no rule for this observation is left as itself, like any generator nothing is known about. -/

/--
trace: lo hi : ℤ
h : lo ≤ hi
k : ℕ
ih : (List.replicate k lo, 2 * k + 1) ∈ SPMF.support (listOf (chooseInt lo hi h))
⊢ [] = List.replicate (k + 1) lo ∧ 1 + 0 = 2 * (k + 1) + 1 ∨
    ∃ x,
      (lo ≤ x ∧ x ≤ hi) ∧
        ∃ xs n_xs,
          (xs, n_xs) ∈ SPMF.support (listOf (chooseInt lo hi h)) ∧
            x :: xs = List.replicate (k + 1) lo ∧ 1 + (1 + n_xs) = 2 * (k + 1) + 1
-/
#guard_msgs in
example {lo hi : Int} (h : lo ≤ hi) (k : Nat) :
    (List.replicate k lo, 2 * k + 1) ∈
      SPMF.support (listOf (chooseInt lo hi h) : SPMF.Cost (List Int)) := by
  induction k with
  | zero => rw [listOf]; complete_bound; exact .inl rfl
  | succ k ih =>
    rw [listOf]; complete_bound
    trace_state
    exact .inr ⟨lo, ⟨le_rfl, h⟩, _, _, ih, by simp [List.replicate_succ], by omega⟩

/--
error: complete_bound: expected a goal `a ∈ SPMF.support (gen …)` or `IsCompleteFor (gen …) P`, got
  IsSound (genHeap lo) (Heap.Tree.isHeap lo)
-/
#guard_msgs in
example : IsSound (genHeap lo) (Heap.Tree.isHeap lo) := by
  complete_bound

end CompleteBoundTest
