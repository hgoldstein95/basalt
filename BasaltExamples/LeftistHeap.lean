/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt.Combinators
import BasaltExamples.ArbNat

/-!
# Leftist Heaps

`Tree.genLeftist lo` generates leftist min-heaps with every value at least `lo`. Heap order is
threaded as a lower bound, as in `Heap.Tree.genHeap`; the leftist property couples siblings, so the
generator builds both children independently and then puts the higher-rank one on the left. That
`if` is the only difference from `genHeap` — including in the termination proof, which is
**critical** in the same way and the same text.
-/

open RandomChoice ArbNat

namespace LeftistHeap

inductive Tree where
  | leaf : Tree
  | node : Tree → Nat → Tree → Tree
deriving Repr

def Tree.size : Tree → Nat
  | leaf => 0
  | node l _ r => l.size + r.size + 1

def Tree.rank : Tree → Nat
  | leaf => 0
  | node _ _ r => r.rank + 1

def Tree.isLeftist (lo : Nat) : Tree → Prop
  | leaf => True
  | node l x r =>
    lo ≤ x ∧
    r.rank ≤ l.rank ∧
    isLeftist x l ∧
    isLeftist x r

def Tree.genLeftist [Gen G] (lo : Nat) : G Tree :=
  oneOf! [
    fun () => pure leaf,
    fun () => do
      let delta ← Nat.arbitrary
      let x := lo + delta
      let a ← Tree.genLeftist x
      let b ← Tree.genLeftist x
      if b.rank ≤ a.rank then
        return node a x b
      else
        return node b x a
  ]
partial_fixpoint

def Tree.genLeftistOfRank [Gen G] (lo : Nat) : Nat → G Tree
  | 0 => pure leaf
  | k + 1 => do
    let delta ← Nat.arbitrary
    let x := lo + delta
    let r ← Tree.genLeftistOfRank x k
    let gap ← Nat.arbitrary
    let l ← Tree.genLeftistOfRank x (k + gap)
    return node l x r
partial_fixpoint

theorem Tree.genLeftist.sound_complete :
    IsSoundAndComplete (Tree.genLeftist lo) (Tree.isLeftist lo) := by
  refine .intro ?sound ?complete
  case sound =>
    sound_fixpoint
    all_goals simp_all [Tree.isLeftist]
    all_goals omega
  case complete =>
    intro t
    induction t generalizing lo with
    | leaf => intro _; rw [Tree.genLeftist]; complete_bound
    | node l x r ihl ihr =>
      intro ⟨hle, hrank, hl, hr⟩
      obtain ⟨d, rfl⟩ : ∃ d, x = lo + d := ⟨x - lo, by omega⟩
      rw [Tree.genLeftist]; complete_bound
      exact ⟨d, l, ihl hl, r, ihr hr, by rw [ite_eq_left hrank]⟩

theorem Tree.genLeftistOfRank.sound_complete :
    IsSoundAndComplete (Tree.genLeftistOfRank lo k) (fun t => Tree.isLeftist lo t ∧ t.rank = k) := by
  refine .intro ?sound ?complete
  case sound =>
    sound_fixpoint
    all_goals simp_all [Tree.isLeftist, Tree.rank]
  case complete =>
    intro t
    induction t generalizing lo k with
    | leaf =>
      intro ⟨_, hk⟩
      obtain rfl : k = 0 := hk.symm
      rw [Tree.genLeftistOfRank]; complete_bound
    | node l x r ihl ihr =>
      intro ⟨⟨hle, hrank, hl, hr⟩, hk⟩
      obtain rfl : k = r.rank + 1 := hk.symm
      obtain ⟨d, rfl⟩ : ∃ d, x = lo + d := ⟨x - lo, by omega⟩
      rw [Tree.genLeftistOfRank]; complete_bound
      exact ⟨d, r, ihr ⟨hr, rfl⟩, l.rank - r.rank, l, ihl ⟨hl, by omega⟩, rfl⟩

theorem Tree.genLeftist.terminates : IsAlmostSurelyTerminating (Tree.genLeftist lo) := by
  mass_fixpoint using SPMF.LfpIsOne.quadratic (a := 1 / 2) (b := 0) (d := 1 / 2)
    (by ennreal_to_real; norm_num) (by ennreal_to_real; norm_num) (by norm_num)
  simp [sq, ENNReal.div_eq_inv_mul, mul_add]

end LeftistHeap
