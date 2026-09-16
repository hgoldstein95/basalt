/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt.Combinators
import BasaltExamples.ArbNat

open RandomChoice ArbNat

/-!
# Leftist Heaps

`Tree.genLeftist lo` generates leftist min-heaps with every value at least `lo`. Heap order is
threaded as a lower bound, as in `Heap.Tree.genHeap`; the leftist property couples siblings, so the
generator builds both children independently and then puts the higher-rank one on the left.
-/

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
  oneOf [
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
  intro t
  fun_induction Tree.isLeftist with
  | case1 lo =>
    constructor
    · solve_by_elim
    · unfold genLeftist; simp
  | case2 lo l x r ih_l ih_r =>
    unfold genLeftist
    simp
    constructor
    · grind
    · intro h
      exists (x - lo)
      constructor <;> grind only [Nat.arbitrary_mem_support]

theorem Tree.genLeftistOfRank.sound_complete :
    IsSoundAndComplete (Tree.genLeftistOfRank lo k) (fun t => Tree.isLeftist lo t ∧ t.rank = k) := by
  intro t
  induction t generalizing lo k with
  | leaf =>
    unfold genLeftistOfRank
    split <;> simp <;> grind [SPMF.mem_support_pure_iff, isLeftist.eq_def, rank]
  | node l x r ih_l ih_r =>
    unfold genLeftistOfRank
    split
    case _ => simp; grind [= isLeftist, = rank]
    case _ k =>
      simp
      constructor
      · grind only [rank, isLeftist]
      · intro h
        exists (x - lo)
        constructor
        · grind only [Nat.arbitrary_mem_support]
        · constructor
          · grind only [rank, isLeftist]
          · exists (l.rank - k)
            grind only [Nat.arbitrary_mem_support, eq_def, rank.eq_def, isLeftist.eq_def]

-- theorem Tree.genLeftist.terminates : IsAlmostSurelyTerminating (Tree.genLeftist lo) := by
--   refine SPMF.IsPMF_of_critical_family
--     (fun (lo : Nat) => (Tree.genLeftist lo : SPMF Tree))
--     (F := fun c => 1 / 2 + 1 / 2 * c ^ 2)
--     (fun c hle hge => ?_) ?_ lo
--   · rw [← ENNReal.toReal_eq_one_iff]
--     ennreal_to_real at hge   -- before `hle`: finiteness needs `c ≤ 1`
--     ennreal_to_real at hle
--     norm_num at hge hle
--     nlinarith [sq_nonneg (c.toReal - 1)]
--   · intro lo
--     conv_rhs => rw [Tree.genLeftist]
--     simp only [one_div, SPMF.mass_oneOf, List.map_cons, SPMF.mass_pure,
--       List.map_nil, List.sum_cons, List.sum_nil, add_zero, List.length_cons, List.length_nil,
--       zero_add, Nat.reduceAdd, Nat.cast_ofNat]
--     rw [ENNReal.le_div_iff_mul_le (by norm_num) (by norm_num), add_mul,
--       ENNReal.inv_mul_cancel (by norm_num) (by norm_num), mul_right_comm,
--       ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]
--     gcongr
--     rw [sq]
--     refine SPMF.mass_bind_ge_of_isPMF Nat.arbitrary.terminates (fun delta => ?_)
--     refine SPMF.mass_bind_ge_mul (SPMF.mass_ge_iInf _ (lo + delta)) (fun l => ?_)
--     simpa [SPMF.mass_bind_pure] using SPMF.mass_ge_iInf
--       (fun (lo : Nat) => (Tree.genLeftist lo : SPMF Tree)) (lo + delta)

end LeftistHeap
