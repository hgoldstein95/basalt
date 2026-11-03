/-
Copyright (c) 2026 Harrison Goldstein & Ernest Ng. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Ernest Ng
-/
module

public import Basalt
public import BasaltExamples.BST

/-!
# Uniform Binary Search Trees

`Tree.genUniformBST lo m n` generates a BST with exactly `n` nodes where node values lie in the interval
`[lo, lo + m - 1]`. We prove that every such tree is generated equally likely (`Tree.genUniformBST.uniform`).
-/

@[expose] public section

open RandomChoice
open scoped ENNReal

namespace BST

/-- All ways to split a node over `m` keys and `n + 1` nodes -/
def splits (m n : Nat) : List (Nat × Fin (n + 1)) := List.range m ×ˢ List.finRange (n + 1)

theorem mem_splits {m n : Nat} {p : Nat × Fin (n + 1)} : p ∈ splits m n ↔ p.1 < m := by
  rw [splits, List.mem_product]; simp

/-- The no. of BSTs with `n` nodes over `m` consecutive keys. -/
def numBST (m : Nat) : Nat → Nat
  | 0 => 1
  | n + 1 => ((splits m n).map fun p => numBST p.1 p.2 * numBST (m - 1 - p.1) (n - p.2)).sum
termination_by n => n

/-- Generates a BST with `n` nodes, with node values from the interval `[lo, lo + m - 1]`:
   a split `p` with weight the number of trees it leaves, then a uniform tree for each side. -/
def Tree.genUniformBST [Gen G] (lo : Int) (m : Nat) (n : Nat) : G (Tree Int) :=
  match n with
  | 0 => pure .leaf
  | n + 1 =>
    if h : 0 < numBST m (n + 1) then
      frequency ((splits m n).map fun p =>
        (numBST p.1 p.2 * numBST (m - 1 - p.1) (n - p.2), fun _ => do
          let l ← Tree.genUniformBST lo p.1 p.2
          let r ← Tree.genUniformBST (lo + p.1 + 1) (m - 1 - p.1) (n - p.2)
          return .node l (lo + p.1) r))
        (by rw [numBST] at h; simpa [Function.comp_def] using h)
    else pure .leaf
termination_by n

theorem nodup_splits (m n : Nat) : (splits m n).Nodup :=
  List.nodup_range.product (List.nodup_finRange _)

theorem numBST_pos {m n : Nat} (h : n ≤ m) : 0 < numBST m n := by
  induction n using Nat.strong_induction_on generalizing m with
  | _ n ih =>
  match n with
  | 0 => simp [numBST]
  | n + 1 =>
    rw [numBST]
    refine Nat.lt_of_lt_of_le ?_ (List.le_sum_of_mem (List.mem_map_of_mem
      (f := fun p : Nat × Fin (n + 1) => numBST p.1 p.2 * numBST (m - 1 - p.1) (n - p.2))
      (mem_splits.mpr (show (n, Fin.last n).1 < m by simp; omega))))
    simpa [numBST] using @ih n (by omega) n le_rfl

/-- The trees `Tree.genUniformBST lo m n` is uniform over: search trees with `n` nodes and keys in
`[lo, lo + m - 1]`. -/
def Tree.IsBSTOfSize (lo : Int) (m n : Nat) (t : Tree Int) : Prop :=
  t.isBST lo (lo + m - 1) ∧ t.size = n

theorem Tree.isBST.size_le {lo hi : Int} {t : Tree Int} (h : t.isBST lo hi) :
    t.size ≤ (hi - lo + 1).toNat := by
  induction t generalizing lo hi with
  | leaf => simp [Tree.size]
  | node l x r ihl ihr =>
    obtain ⟨h1, h2, hl, hr⟩ := h
    have := ihl hl
    have := ihr hr
    simp only [Tree.size]
    omega

theorem Tree.IsBSTOfSize.numBST_pos {lo : Int} {m n : Nat} {t : Tree Int}
    (h : t.IsBSTOfSize lo m n) : 0 < numBST m n :=
  BST.numBST_pos (by have := h.1.size_le; have := h.2; omega)

section uniform

variable {A B : SPMF (Tree Int)} {y : Int}

theorem node_bind_apply_leaf :
    (A >>= fun l => B >>= fun r => pure (Tree.node l y r)) Tree.leaf = 0 := by
  simp only [SPMF.bind_apply, SPMF.pure_apply]
  simp

theorem node_bind_apply_node (l r : Tree Int) (x : Int) :
    (A >>= fun l => B >>= fun r => pure (Tree.node l y r)) (Tree.node l x r)
      = if x = y then A l * B r else 0 := by
  simp only [SPMF.bind_apply, SPMF.pure_apply, Tree.node.injEq]
  split_ifs with h
  · subst h
    rw [tsum_eq_single l (fun a ha => by simp [Ne.symm ha]),
      tsum_eq_single r (fun b hb => by simp [Ne.symm hb])]
    simp
  · simp [h]

open Classical in

/-- Closed form expression for the probability of generating a particular BST -/
theorem Tree.genUniformBST_apply (t : Tree Int) :
    ∀ (lo : Int) (m n : Nat), 0 < numBST m n →
      (Tree.genUniformBST lo m n : SPMF (Tree Int)) t
        = if t.IsBSTOfSize lo m n then ((numBST m n : ℝ≥0∞))⁻¹ else 0 := by
  induction t with
  | leaf =>
    intro lo m n hpos
    cases n with
    | zero => simp [Tree.genUniformBST, Tree.IsBSTOfSize, Tree.isBST, Tree.size, numBST]
    | succ n =>
      rw [Tree.genUniformBST, dite_eq_left hpos, SPMF.frequency_apply]
      simp only [List.map_map, Function.comp_def, node_bind_apply_leaf, mul_zero]
      simp [Tree.IsBSTOfSize, Tree.size]
  | node l x r ihl ihr =>
    intro lo m n hpos
    cases n with
    | zero => simp [Tree.genUniformBST, Tree.IsBSTOfSize, Tree.size]
    | succ n =>
      rw [Tree.genUniformBST, dite_eq_left hpos, SPMF.frequency_apply]
      simp only [List.map_map, Function.comp_def, node_bind_apply_node]
      have hden : (List.map (fun p : Nat × Fin (n + 1) =>
          numBST p.1 p.2 * numBST (m - 1 - p.1) (n - p.2)) (splits m n)).sum = numBST m (n + 1) := by
        rw [numBST]
      rw [hden]
      -- Each split contributes `1` if it is the split of `node l x r`, and `0` otherwise.
      have hterm : ∀ p : Nat × Fin (n + 1),
          ((numBST p.1 p.2 * numBST (m - 1 - p.1) (n - p.2) : ℕ) : ℝ≥0∞) *
            (if x = lo + p.1 then
              (Tree.genUniformBST lo p.1 p.2 : SPMF (Tree Int)) l
                * (Tree.genUniformBST (lo + p.1 + 1) (m - 1 - p.1) (n - p.2) : SPMF (Tree Int)) r
            else 0)
          = if x = lo + p.1 ∧ l.IsBSTOfSize lo p.1 p.2
              ∧ r.IsBSTOfSize (lo + p.1 + 1) (m - 1 - p.1) (n - p.2) then 1 else 0 := by
        intro p
        by_cases hw : numBST p.1 p.2 * numBST (m - 1 - p.1) (n - p.2) = 0
        · rw [hw, Nat.cast_zero, zero_mul, ite_eq_right]
          rintro ⟨-, hl, hr⟩
          exact absurd hw (Nat.mul_ne_zero hl.numBST_pos.ne' hr.numBST_pos.ne')
        · have ha : 0 < numBST p.1 p.2 := Nat.pos_of_ne_zero (left_ne_zero_of_mul hw)
          have hb : 0 < numBST (m - 1 - p.1) (n - p.2) :=
            Nat.pos_of_ne_zero (right_ne_zero_of_mul hw)
          rw [ihl _ _ _ ha, ihr _ _ _ hb]
          by_cases hx : x = lo + p.1 <;> by_cases hl : l.IsBSTOfSize lo p.1 p.2 <;>
            by_cases hr : r.IsBSTOfSize (lo + p.1 + 1) (m - 1 - p.1) (n - p.2) <;>
            simp only [hx, hl, hr, ite_true, ite_false, true_and, false_and, and_false, mul_zero,
              zero_mul]
          rw [Nat.cast_mul, mul_mul_mul_comm, ENNReal.mul_inv_cancel (by simpa using ha.ne')
            (by simp), ENNReal.mul_inv_cancel (by simpa using hb.ne') (by simp), one_mul]
      simp only [hterm]
      rw [← List.sum_toFinset _ (nodup_splits m n)]
      -- The split of `node l x r`, when it is a search tree of the right size, is unique.
      have hC : ∀ p ∈ (splits m n).toFinset,
          (x = lo + p.1 ∧ l.IsBSTOfSize lo p.1 p.2
              ∧ r.IsBSTOfSize (lo + p.1 + 1) (m - 1 - p.1) (n - p.2))
            ↔ (Tree.node l x r).IsBSTOfSize lo m (n + 1)
              ∧ p.1 = (x - lo).toNat ∧ (p.2 : Nat) = l.size := by
        intro p hp
        have hp1 := mem_splits.mp (List.mem_toFinset.mp hp)
        have hp2 := p.2.isLt
        have e : lo + (p.1 : Int) + 1 + ((m - 1 - p.1 : Nat) : Int) - 1 = lo + m - 1 := by omega
        simp only [Tree.IsBSTOfSize, Tree.isBST, Tree.size, e]
        constructor
        · rintro ⟨rfl, ⟨hl, hls⟩, ⟨hr, hrs⟩⟩
          exact ⟨⟨⟨by omega, by omega, hl, hr⟩, by omega⟩, by omega, hls.symm⟩
        · rintro ⟨⟨⟨h1, h2, hl, hr⟩, hs⟩, hp1', hp2'⟩
          have ex : x = lo + p.1 := by omega
          subst ex
          exact ⟨rfl, ⟨hl, hp2'.symm⟩, ⟨hr, by omega⟩⟩
      by_cases hv : (Tree.node l x r).IsBSTOfSize lo m (n + 1)
      · have hls : l.size < n + 1 := by have := hv.2; simp only [Tree.size] at this; omega
        have hx : (x - lo).toNat < m := by
          have := hv.1; simp only [Tree.isBST] at this; omega
        set p₀ : Nat × Fin (n + 1) := ((x - lo).toNat, ⟨l.size, hls⟩)
        have hp₀ : p₀ ∈ (splits m n).toFinset := List.mem_toFinset.mpr (mem_splits.mpr hx)
        rw [Finset.sum_eq_single_of_mem p₀ hp₀, ite_eq_left ((hC p₀ hp₀).mpr ⟨hv, rfl, rfl⟩),
          ite_eq_left hv, one_div]
        intro q hq hne
        rw [ite_eq_right]
        intro hcq
        obtain ⟨-, h1, h2⟩ := (hC q hq).mp hcq
        exact hne (Prod.ext h1 (Fin.ext h2))
      · rw [Finset.sum_eq_zero, ite_eq_right hv, ENNReal.zero_div]
        intro q hq
        rw [ite_eq_right]
        exact fun hcq => hv ((hC q hq).mp hcq).1

end uniform

open Classical in
/-- `Tree.genUniformBST lo m n` generates a BST with `n` nodes and keys in
`[lo, lo + m - 1]` uniformly: each possible BST is generated with probability `1 / numBST m n`. -/
theorem Tree.genUniformBST.uniform {lo : Int} {m n : Nat} (h : n ≤ m) (t : Tree Int) :
    (Tree.genUniformBST lo m n : SPMF (Tree Int)) t
      = if t.IsBSTOfSize lo m n then ((numBST m n : ℝ≥0∞))⁻¹ else 0 :=
  Tree.genUniformBST_apply t lo m n (numBST_pos h)

end BST
