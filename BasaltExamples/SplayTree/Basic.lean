/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import BasaltExamples.SplayTree.Def

open RandomChoice

/-!
# Splay Trees: the Basic Structure

`Tree.genBoundedBST n lo hi` generates the benchmark's basic structure — a search tree with at most
`n` internal nodes and keys in `[lo, hi]`. It draws the size first and defers to `Tree.genSizedBST`,
which produces a tree of *exactly* that size; the left-subtree split is in turn the more unbalanced
of two uniform draws. Both are choices of distribution only — every tree of `Tree.isBoundedBST`
stays reachable — and together they keep the output away from the trivial trees.
-/

namespace SplayTree

/-- A search tree on `[lo, hi]` holds at most one key per point of the interval. -/
theorem Tree.size_le_of_isBST {t : Tree} {lo hi : Int} (h : t.isBST lo hi) :
    (t.size : Int) ≤ max 0 (hi - lo + 1) := by
  induction t generalizing lo hi with
  | leaf => simp [Tree.size]
  | node l x r ihl ihr =>
    obtain ⟨hlo, hhi, hl, hr⟩ := h
    have hL := ihl hl
    have hR := ihr hr
    simp only [Tree.size]
    push_cast
    omega

/-- The more unbalanced of two candidate splits of `n`: whichever is further from `n / 2`, with
`Nat` subtraction supplying the absolute value. Since `unbalanced n k k = k`, every split remains
reachable, so tilting a draw this way shifts mass toward tall trees without narrowing a support. -/
def unbalanced (n k₁ k₂ : Nat) : Nat :=
  if (n - 2 * k₂) + (2 * k₂ - n) ≤ (n - 2 * k₁) + (2 * k₁ - n) then k₁ else k₂

theorem unbalanced_le {n k₁ k₂ : Nat} (h₁ : k₁ ≤ n) (h₂ : k₂ ≤ n) : unbalanced n k₁ k₂ ≤ n := by
  unfold unbalanced; split <;> assumption

@[simp]
theorem unbalanced_self (n k : Nat) : unbalanced n k k = k := by
  unfold unbalanced; simp

/-- A search tree with exactly `n` internal nodes and keys in `[lo, hi]`. -/
def Tree.isSizedBST (n : Nat) (lo hi : Int) (t : Tree) : Prop :=
  t.size = n ∧ t.isBST lo hi

/-- The bounded basic structure: a search tree with at most `n` internal nodes and keys in
`[lo, hi]`. -/
def Tree.isBoundedBST (n : Nat) (lo hi : Int) (t : Tree) : Prop :=
  t.size ≤ n ∧ t.isBST lo hi

/-- Generates a search tree with exactly `n` internal nodes and keys in `[lo, hi]`, which the
hypothesis says is wide enough to hold them. The two draws are the size `k` of the left subtree and
the offset `d` of the pivot within the window `[lo + k, hi - (n - k)]` that keeps both children
feasible; `RandomChoice.choose` rather than `chooseNat` because the recursive calls need those
bounds as proofs, not just as values. -/
def Tree.genSizedBST [Gen G] : (n : Nat) → (lo hi : Int) → (n : Int) ≤ max 0 (hi - lo + 1) → G Tree
  | 0, _, _, _ => pure leaf
  | n + 1, lo, hi, h => do
    let k₁ ← ULift.down <$> RandomChoice.choose 0 n (Nat.zero_le n)
    let k₂ ← ULift.down <$> RandomChoice.choose 0 n (Nat.zero_le n)
    let d ← ULift.down <$> RandomChoice.choose 0 (hi - lo - n).toNat (Nat.zero_le _)
    let k := unbalanced n k₁.1 k₂.1
    let l ← Tree.genSizedBST k lo (lo + k + d.1 - 1) (by omega)
    let r ← Tree.genSizedBST (n - k) (lo + k + d.1 + 1) hi
              (by have := unbalanced_le k₁.2.2 k₂.2.2; have := d.2.2; omega)
    pure (node l (lo + k + d.1) r)
termination_by n => n
decreasing_by all_goals (have := unbalanced_le k₁.2.2 k₂.2.2; omega)

theorem Tree.genSizedBST_mem_support (t : Tree) (n : Nat) (lo hi : Int)
    (h : (n : Int) ≤ max 0 (hi - lo + 1)) :
    t ∈ SPMF.support (Tree.genSizedBST n lo hi h) ↔ t.isSizedBST n lo hi := by
  induction t generalizing n lo hi with
  | leaf =>
    cases n with
    | zero => rw [Tree.genSizedBST]; simp [Tree.isSizedBST, Tree.isBST, Tree.size]
    | succ n =>
      rw [Tree.genSizedBST]
      simp [Tree.isSizedBST, Tree.size]
  | node l x r ihl ihr =>
    cases n with
    | zero => rw [Tree.genSizedBST]; simp [Tree.isSizedBST, Tree.size]
    | succ n =>
      rw [Tree.genSizedBST]
      simp [Tree.isSizedBST, Tree.isBST, Tree.size, ihl, ihr]
      constructor
      · rintro ⟨a, ha, b, hb, e, ⟨hls, hl⟩, ⟨hrs, hr⟩, he, rfl⟩
        have hK := unbalanced_le ha hb
        exact ⟨by omega, by omega, by omega, hl, hr⟩
      · rintro ⟨hs, hlo, hhi, hl, hr⟩
        have h1 := Tree.size_le_of_isBST hl
        have h2 := Tree.size_le_of_isBST hr
        refine ⟨l.size, by omega, l.size, by omega, (x - lo - l.size).toNat, ?_⟩
        rw [unbalanced_self]
        refine ⟨⟨rfl, ?_⟩, ⟨by omega, ?_⟩, by omega, by omega⟩
        · rw [show lo + (l.size : Int) + ((x - lo - l.size).toNat : Int) - 1 = x - 1 by omega]
          exact hl
        · rw [show lo + (l.size : Int) + ((x - lo - l.size).toNat : Int) + 1 = x + 1 by omega]
          exact hr

theorem Tree.genSizedBST.sound_complete {n : Nat} {lo hi : Int}
    (h : (n : Int) ≤ max 0 (hi - lo + 1)) :
    IsSoundAndComplete (Tree.genSizedBST n lo hi h) (Tree.isSizedBST n lo hi) :=
  fun t => Tree.genSizedBST_mem_support t n lo hi h

theorem Tree.genSizedBST.terminates :
    ∀ (n : Nat) (lo hi : Int) (h : (n : Int) ≤ max 0 (hi - lo + 1)),
      IsAlmostSurelyTerminating (Tree.genSizedBST n lo hi h) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => intro lo hi h; rw [Tree.genSizedBST]; exact SPMF.IsPMF_pure _
    | m + 1 =>
      intro lo hi h
      rw [Tree.genSizedBST]
      refine SPMF.IsPMF_bind (SPMF.IsPMF_map (SPMF.IsPMF_choose _ _ _)) fun k₁ => ?_
      refine SPMF.IsPMF_bind (SPMF.IsPMF_map (SPMF.IsPMF_choose _ _ _)) fun k₂ => ?_
      refine SPMF.IsPMF_bind (SPMF.IsPMF_map (SPMF.IsPMF_choose _ _ _)) fun d => ?_
      have hk : unbalanced m k₁.1 k₂.1 ≤ m := unbalanced_le k₁.2.2 k₂.2.2
      exact SPMF.IsPMF_bind (ih _ (by omega) _ _ _) fun _ =>
        SPMF.IsPMF_bind (ih _ (by omega) _ _ _) fun _ => SPMF.IsPMF_pure _

/-- Generates a search tree with at most `n` internal nodes and keys in `[lo, hi]`: draw the size,
then a tree of exactly that size. -/
def Tree.genBoundedBST [Gen G] (n : Nat) (lo hi : Int) : G Tree := do
  let m ← ULift.down <$> RandomChoice.choose 0 (min n (hi - lo + 1).toNat) (Nat.zero_le _)
  Tree.genSizedBST m.1 lo hi (by have := m.2.2; omega)

theorem Tree.genBoundedBST_mem_support (t : Tree) (n : Nat) (lo hi : Int) :
    t ∈ SPMF.support (Tree.genBoundedBST n lo hi) ↔ t.isBoundedBST n lo hi := by
  unfold Tree.genBoundedBST
  simp [Tree.genSizedBST_mem_support, Tree.isSizedBST, Tree.isBoundedBST]
  intro hbst _
  have := Tree.size_le_of_isBST hbst
  omega

theorem Tree.genBoundedBST.sound_complete :
    IsSoundAndComplete (Tree.genBoundedBST n lo hi) (Tree.isBoundedBST n lo hi) :=
  fun t => Tree.genBoundedBST_mem_support t n lo hi

theorem Tree.genBoundedBST.terminates (n : Nat) (lo hi : Int) :
    IsAlmostSurelyTerminating (Tree.genBoundedBST n lo hi) := by
  rw [Tree.genBoundedBST]
  exact SPMF.IsPMF_bind (SPMF.IsPMF_map (SPMF.IsPMF_choose _ _ _))
    fun _ => Tree.genSizedBST.terminates _ _ _ _

end SplayTree
