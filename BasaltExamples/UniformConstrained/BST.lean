/-
Copyright (c) 2026 Harrison Goldstein & Ernest Ng. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Ernest Ng
-/
module

public import BasaltExamples.BST.ByFiltering
public import BasaltExamples.UniformConstrained.Uniform

/-!
# Claessen et al.'s uniformly distributed BST generator

`bstSpace lo n d` is the space of all BSTs of height at most `d` with node values that
lie in the interval `[lo, lo + n - 1]`. (`Space`s are a concept from Claessen et al. paper)
Each unique tree is present exactly once in the space (`count_sized_bstSpace`).
We show that Claessen et al's rejection-based generator of BSTs (`uniformBST`)
samples uniformly over this space.
-/

@[expose] public section

open RandomChoice ENNReal

namespace UniformConstrained

deriving instance DecidableEq for BST.Tree

/-! ## The space of trees -/

/-- The height of a tree. -/
def treeHeight {α : Type} : BST.Tree α → Nat
  | .leaf => 0
  | .node l _ r => max (treeHeight l) (treeHeight r) + 1

/-- Every key of the tree lies in `[lo, lo + n - 1]`. -/
def keysIn (lo : Int) (n : Nat) : BST.Tree Int → Bool
  | .leaf => true
  | .node l x r => decide (lo ≤ x ∧ x < lo + n) && keysIn lo n l && keysIn lo n r

/-- The keys `[lo, lo + n - 1]`, each a value of size `0`. -/
def keySpace (lo : Int) : Nat → Space Int
  | 0 => .empty
  | n + 1 => .union (.pure lo) (keySpace (lo + 1) n)

/-- The node constructor on the pairs `bstSpace` builds. -/
def mkNode (p : (BST.Tree Int × Int) × BST.Tree Int) : BST.Tree Int := .node p.1.1 p.1.2 p.2

/-- The trees of height at most `d` with keys in `[lo, lo + n - 1]`; each node pays one unit, so a
tree's size in the space is its number of nodes. -/
def bstSpace (lo : Int) (n : Nat) : Nat → Space (BST.Tree Int)
  | 0 => .pure .leaf
  | d + 1 => .union (.pure .leaf)
      (.pay (.fmap mkNode (.prod (.prod (bstSpace lo n d) (keySpace lo n)) (bstSpace lo n d))))

/-! ## Each tree occurs once -/

theorem count_sized_prod {α β : Type} [DecidableEq α] [DecidableEq β] (A : Space α)
    (B : Space β) (k : Nat) (a : α) (b : β) :
    (Space.sized (.prod A B) k).toMultiset.count (a, b)
      = ∑ k₁ ∈ Finset.range (k + 1),
          (Space.sized A k₁).toMultiset.count a * (Space.sized B (k - k₁)).toMultiset.count b := by
  rw [Space.toMultiset_sized_prod, Multiset.count_sum']
  refine Finset.sum_congr rfl fun k₁ _ => ?_
  generalize (Space.sized A k₁).toMultiset = s
  generalize (Space.sized B (k - k₁)).toMultiset = t
  refine Multiset.induction_on s (by simp) fun a₀ s ih => ?_
  rw [Multiset.cons_product, Multiset.count_add, ih, Multiset.count_cons]
  by_cases h : a = a₀
  · subst h
    rw [Multiset.count_map_eq_count' _ _ (Prod.mk_right_injective a)]
    simp [Nat.add_mul, add_comm]
  · rw [Multiset.count_eq_zero.mpr (by simp [Ne.symm h])]; simp [h]

theorem count_sized_keySpace (lo : Int) (n k : Nat) (x : Int) :
    (Space.sized (keySpace lo n) k).toMultiset.count x
      = if k = 0 ∧ lo ≤ x ∧ x < lo + n then 1 else 0 := by
  induction n generalizing lo with
  | zero => simp [keySpace]
  | succ n ih =>
    rw [keySpace, Space.sized_union, FinSet.toMultiset_union, Multiset.count_add, ih]
    cases k with
    | zero =>
      simp only [Space.sized_pure_zero, FinSet.toMultiset_single, Multiset.count_singleton]
      by_cases hx : x = lo
      · subst hx; simp
      · simp only [hx, ite_false, zero_add, true_and]
        split_ifs <;> omega
    | succ k => simp

/-- **Each tree of height at most `d` with keys in range occurs exactly once in `bstSpace`, at its
size.** -/
theorem count_sized_bstSpace (lo : Int) (n : Nat) (d k : Nat) (t : BST.Tree Int) :
    (Space.sized (bstSpace lo n d) k).toMultiset.count t
      = if t.size = k ∧ treeHeight t ≤ d ∧ keysIn lo n t = true then 1 else 0 := by
  induction d generalizing k t with
  | zero =>
    cases k <;> cases t <;>
      simp [bstSpace, BST.Tree.size, treeHeight, keysIn]
  | succ d ih =>
    rw [bstSpace, Space.sized_union, FinSet.toMultiset_union, Multiset.count_add]
    cases k with
    | zero => cases t <;> simp [BST.Tree.size, treeHeight, keysIn]
    | succ k =>
      rw [Space.sized_pure_succ, Space.sized_pay_succ, Space.sized_fmap, FinSet.toMultiset_empty,
        FinSet.toMultiset_fmap, Multiset.count_zero, zero_add]
      cases t with
      | leaf =>
        rw [Multiset.count_eq_zero.mpr (by simp [Multiset.mem_map, mkNode])]
        simp [BST.Tree.size]
      | node l x r =>
        have hinj : Function.Injective mkNode := by
          rintro ⟨⟨_, _⟩, _⟩ ⟨⟨_, _⟩, _⟩ h
          simp only [mkNode, BST.Tree.node.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          rfl
        rw [show BST.Tree.node l x r = mkNode ((l, x), r) from rfl,
          Multiset.count_map_eq_count' _ _ hinj, count_sized_prod]
        -- The key costs nothing, so the left subtree takes the whole first share.
        have hinner : ∀ k₁, (Space.sized (.prod (bstSpace lo n d) (keySpace lo n)) k₁).toMultiset.count (l, x)
            = (if l.size = k₁ ∧ treeHeight l ≤ d ∧ keysIn lo n l = true then 1 else 0)
              * (if lo ≤ x ∧ x < lo + n then 1 else 0) := by
          intro k₁
          rw [count_sized_prod, Finset.sum_eq_single_of_mem k₁ (Finset.self_mem_range_succ k₁)]
          · rw [ih, count_sized_keySpace, Nat.sub_self]
            simp
          · intro k₂ hk₂ hne
            rw [count_sized_keySpace, ite_eq_right (by have := Finset.mem_range.mp hk₂; omega), mul_zero]
        simp only [hinner, ih]
        by_cases hls : l.size ≤ k
        · rw [Finset.sum_eq_single_of_mem l.size (Finset.mem_range.mpr (by omega))]
          · simp only [mkNode, BST.Tree.size, treeHeight, keysIn, Bool.and_eq_true,
              decide_eq_true_eq]
            split_ifs <;> simp_all <;> omega
          · intro k₁ _ hne
            rw [ite_eq_right (by omega), zero_mul, zero_mul]
        · rw [Finset.sum_eq_zero, ite_eq_right (by simp only [mkNode, BST.Tree.size]; omega)]
          intro k₁ hk₁
          rw [ite_eq_right (by have := Finset.mem_range.mp hk₁; omega), zero_mul, zero_mul]

/-! ## BSTs -/

theorem treeHeight_le_size (t : BST.Tree Int) : treeHeight t ≤ t.size := by
  induction t with
  | leaf => simp [treeHeight, BST.Tree.size]
  | node l x r ihl ihr => simp only [treeHeight, BST.Tree.size]; omega

theorem keysIn_of_isBST {a b lo : Int} {n : Nat} {t : BST.Tree Int} (h : t.isBST a b)
    (ha : lo ≤ a) (hb : b < lo + n) : keysIn lo n t = true := by
  induction t generalizing a b with
  | leaf => rfl
  | node l x r ihl ihr =>
    obtain ⟨h1, h2, hl, hr⟩ := h
    simp only [keysIn, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨⟨by omega, by omega⟩, ihl hl ha (by omega)⟩, ihr hr (by omega) hb⟩

/-- A right-leaning BST containing node values `lo, lo + 1, …, lo + k - 1` -/
def spine (lo : Int) : Nat → BST.Tree Int
  | 0 => .leaf
  | k + 1 => .node .leaf lo (spine (lo + 1) k)

theorem size_spine (lo : Int) (k : Nat) : (spine lo k).size = k := by
  induction k generalizing lo with
  | zero => rfl
  | succ k ih => simp [spine, BST.Tree.size, ih]

theorem isBST_spine {lo hi : Int} {k : Nat} (h : lo + k ≤ hi + 1) : (spine lo k).isBST lo hi := by
  induction k generalizing lo with
  | zero => rfl
  | succ k ih => exact ⟨le_rfl, by omega, rfl, ih (by omega)⟩

/-- The BST predicate over the keys of `bstSpace lo n`. -/
abbrev isBSTIn (lo : Int) (n : Nat) (t : BST.Tree Int) : Bool := t.isBSTb lo (lo + n - 1)

theorem spine_mem_allOfSize {lo : Int} {n k : Nat} (h : k ≤ n) :
    spine lo k ∈ allOfSize (bstSpace lo n k) k := by
  refine Multiset.count_pos.mp ?_
  rw [count_sized_bstSpace, ite_eq_left ⟨size_spine lo k,
    (treeHeight_le_size _).trans (size_spine lo k).le,
    keysIn_of_isBST (isBST_spine (hi := lo + n - 1) (by omega)) le_rfl (by omega)⟩]
  exact Nat.one_pos

/-- The paper's rejection sampling based generator of BSTs: `uniformFilter` over the trees with `k` nodes and
keys in `[lo, lo + n - 1]`, keeping the BSTs. -/
def uniformBST [Gen G] (lo : Int) (n k : Nat) (h : k ≤ n) : G (BST.Tree Int) :=
  uniformFilter (isBSTIn lo n) (bstSpace lo n k) k (by
    rw [← FinSet.card_toMultiset]
    exact Multiset.card_pos_iff_exists_mem.mpr ⟨_, spine_mem_allOfSize h⟩)

/-- **Theorem 1 in Claessen et al., instantiated for a BST generator** Each BST with `k` nodes and keys in `[lo, lo + n - 1]`
has probability `1 / m`, where `m` is the total number of such BSTs.  -/
theorem uniformBST_apply {lo : Int} {n k : Nat} (h : k ≤ n) (t : BST.Tree Int) :
    (uniformBST lo n k h : SPMF (BST.Tree Int)) t
      = if isBSTIn lo n t = true ∧ t.size = k then
          1 / ((satisfying (isBSTIn lo n) (bstSpace lo n k) k).card : ℝ≥0∞)
        else 0 := by
  have hb : 0 < (satisfying (isBSTIn lo n) (bstSpace lo n k) k).card :=
    Multiset.card_pos_iff_exists_mem.mpr ⟨spine lo k, Multiset.mem_filter.mpr
      ⟨spine_mem_allOfSize h, BST.Tree.isBSTb_iff.mpr (isBST_spine (by omega))⟩⟩
  rw [uniformBST, Theorem1 _ _ _ _ hb t, allOfSize, count_sized_bstSpace]
  by_cases hp : isBSTIn lo n t = true
  · by_cases hs : t.size = k
    · rw [ite_eq_left hp, ite_eq_left ⟨hs, hs ▸ treeHeight_le_size t,
        keysIn_of_isBST (BST.Tree.isBSTb_iff.mp hp) le_rfl (by omega)⟩, ite_eq_left ⟨hp, hs⟩]
      simp
    · rw [ite_eq_left hp, ite_eq_right (fun h' => hs h'.1), ite_eq_right (fun h' => hs h'.2)]
      simp
  · rw [ite_eq_right hp, ite_eq_right (fun h' => hp h'.1)]
    simp

/-- **Any two BSTs of the same size are equally likely.** -/
theorem uniformBST_uniform {lo : Int} {n k : Nat} (h : k ≤ n) {t₁ t₂ : BST.Tree Int}
    (h₁ : t₁.isBST lo (lo + n - 1)) (h₂ : t₂.isBST lo (lo + n - 1))
    (hs₁ : t₁.size = k) (hs₂ : t₂.size = k) :
    (uniformBST lo n k h : SPMF (BST.Tree Int)) t₁ = (uniformBST lo n k h : SPMF (BST.Tree Int)) t₂ := by
  rw [uniformBST_apply, uniformBST_apply, ite_eq_left ⟨BST.Tree.isBSTb_iff.mpr h₁, hs₁⟩,
    ite_eq_left ⟨BST.Tree.isBSTb_iff.mpr h₂, hs₂⟩]

end UniformConstrained
