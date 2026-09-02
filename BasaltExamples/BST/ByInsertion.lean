/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt
import BasaltExamples.BST

open RandomChoice

/-!
# Binary Search Trees by Insertion

`Tree.genBSTByInsertion` generates a search tree the indirect way: draw a list of keys from
`[lo, hi]` and insert them into `leaf` one after another, rather than shaping the tree directly like
`Tree.genBST` (`BasaltExamples/BST`). Both reach exactly `Tree.isBST lo hi`
(`Tree.support_genBSTByInsertion_eq`).

It is sound, complete, and almost surely terminating — but *not* cost bounded, and the failure is
inherent rather than an artifact of a loose bound: the draw has no length limit, and duplicate keys
collapse arbitrarily long draws onto the same tree, so no cost function of the output tree can exist
(`Tree.genBSTByInsertion.not_cost_bounded`).
-/

namespace BST

/-- Inserts a key into a search tree, ignoring keys that are already present. Ignoring them (rather
than, say, keeping both copies) is what keeps the output within `Tree.isBST`, whose left and right
bounds `x - 1` and `x + 1` exclude the key at every node. -/
def Tree.insert (t : Tree Int) (x : Int) : Tree Int :=
  match t with
  | leaf => node leaf x leaf
  | node l y r =>
    if x < y then node (l.insert x) y r
    else if y < x then node l y (r.insert x)
    else node l y r

/-- Generates a search tree with keys in `[lo, hi]` by drawing a list of keys and inserting them one
after another into the empty tree. -/
def Tree.genBSTByInsertion [Gen G] (lo hi : Int) (h : lo ≤ hi := by gen_side_condition) :
    G (Tree Int) := do
  let xs ← listOf (chooseInt lo hi h)
  return xs.foldl Tree.insert Tree.leaf

/-! ## Support -/

theorem Tree.isBST.insert {lo hi : Int} {t : Tree Int} (h : t.isBST lo hi) {x : Int}
    (hlo : lo ≤ x) (hhi : x ≤ hi) : (t.insert x).isBST lo hi := by
  induction t generalizing lo hi with
  | leaf => exact ⟨hlo, hhi, rfl, rfl⟩
  | node l y r ihl ihr =>
    obtain ⟨hly, hyh, hl, hr⟩ := h
    simp only [Tree.insert]
    split_ifs with h1 h2
    · exact ⟨hly, hyh, ihl hl hlo (by omega), hr⟩
    · exact ⟨hly, hyh, hl, ihr hr (by omega) hhi⟩
    · exact ⟨hly, hyh, hl, hr⟩

theorem Tree.isBST_foldl_insert {lo hi : Int} {t : Tree Int} (h : t.isBST lo hi) (xs : List Int)
    (hxs : ∀ x ∈ xs, lo ≤ x ∧ x ≤ hi) : (xs.foldl Tree.insert t).isBST lo hi := by
  induction xs generalizing t with
  | nil => exact h
  | cons x xs ih =>
    obtain ⟨hlo, hhi⟩ := hxs x (by simp)
    exact ih (h.insert hlo hhi) (fun y hy => hxs y (by simp [hy]))

/-- The keys of the tree, root first. This is the insertion order that rebuilds the tree, and hence
the completeness witness. -/
def Tree.preorder : Tree Int → List Int
  | leaf => []
  | node l x r => x :: (l.preorder ++ r.preorder)

theorem Tree.mem_preorder_bounds {lo hi : Int} {t : Tree Int} (h : t.isBST lo hi) :
    ∀ y ∈ t.preorder, lo ≤ y ∧ y ≤ hi := by
  induction t generalizing lo hi with
  | leaf => simp [Tree.preorder]
  | node l x r ihl ihr =>
    obtain ⟨hlo, hhi, hl, hr⟩ := h
    intro y hy
    simp only [Tree.preorder, List.mem_cons, List.mem_append] at hy
    rcases hy with rfl | hy | hy
    · exact ⟨hlo, hhi⟩
    · have := ihl hl y hy; omega
    · have := ihr hr y hy; omega

theorem Tree.foldl_insert_of_lt {l r : Tree Int} {x : Int} (ys : List Int)
    (h : ∀ y ∈ ys, y < x) :
    ys.foldl Tree.insert (node l x r) = node (ys.foldl Tree.insert l) x r := by
  induction ys generalizing l with
  | nil => rfl
  | cons y ys ih =>
    simp only [List.foldl_cons, Tree.insert, if_pos (h y (by simp))]
    exact ih (fun z hz => h z (by simp [hz]))

theorem Tree.foldl_insert_of_gt {l r : Tree Int} {x : Int} (ys : List Int)
    (h : ∀ y ∈ ys, x < y) :
    ys.foldl Tree.insert (node l x r) = node l x (ys.foldl Tree.insert r) := by
  induction ys generalizing r with
  | nil => rfl
  | cons y ys ih =>
    have hy := h y (by simp)
    simp only [List.foldl_cons, Tree.insert, if_neg (show ¬ y < x by omega), if_pos hy]
    exact ih (fun z hz => h z (by simp [hz]))

/-- Completeness in one lemma: inserting a tree's own keys in preorder rebuilds that tree, so every
search tree is reachable. The root goes in first, and the two subtrees then land on opposite sides
of it untouched — which is exactly what `foldl_insert_of_lt` and `foldl_insert_of_gt` say. -/
theorem Tree.foldl_insert_preorder {lo hi : Int} {t : Tree Int} (h : t.isBST lo hi) :
    t.preorder.foldl Tree.insert leaf = t := by
  induction t generalizing lo hi with
  | leaf => rfl
  | node l x r ihl ihr =>
    obtain ⟨hlo, hhi, hl, hr⟩ := h
    simp only [Tree.preorder, List.foldl_cons, List.foldl_append]
    rw [show Tree.insert leaf x = node leaf x leaf from rfl,
      Tree.foldl_insert_of_lt _ (fun y hy => by have := Tree.mem_preorder_bounds hl y hy; omega),
      ihl hl,
      Tree.foldl_insert_of_gt _ (fun y hy => by have := Tree.mem_preorder_bounds hr y hy; omega),
      ihr hr]

theorem Tree.genBSTByInsertion_mem_support {lo hi : Int} (h : lo ≤ hi) (t : Tree Int) :
    t ∈ SPMF.support (Tree.genBSTByInsertion lo hi h) ↔ t.isBST lo hi := by
  unfold Tree.genBSTByInsertion
  support_simp
  constructor
  · rintro ⟨xs, hxs, rfl⟩
    exact Tree.isBST_foldl_insert (t := Tree.leaf) rfl xs hxs
  · intro ht
    exact ⟨t.preorder, Tree.mem_preorder_bounds ht, (Tree.foldl_insert_preorder ht).symm⟩

theorem Tree.genBSTByInsertion.sound_complete {lo hi : Int} (h : lo ≤ hi) :
    IsSoundAndComplete (Tree.genBSTByInsertion lo hi h) (Tree.isBST lo hi) :=
  Tree.genBSTByInsertion_mem_support h

/-- Inserting a drawn list and shaping the tree directly reach the same trees. -/
theorem Tree.support_genBSTByInsertion_eq {lo hi : Int} (h : lo ≤ hi) :
    SPMF.support (Tree.genBSTByInsertion lo hi h) = SPMF.support (Tree.genBST lo hi) :=
  Set.ext fun t =>
    (Tree.genBSTByInsertion_mem_support h t).trans (Tree.genBST.sound_complete t).symm

/-! ## Termination -/

theorem Tree.genBSTByInsertion.terminates {lo hi : Int} (h : lo ≤ hi) :
    IsAlmostSurelyTerminating (Tree.genBSTByInsertion lo hi h) :=
  SPMF.IsPMF_bind_pure (SPMF.IsPMF_listOf (SPMF.mass_chooseInt lo hi h))

/-! ## Cost -/

/-- Every `lo` after the first is absorbed, so any number of them produces the same one-node tree.
This is the collapse that defeats any cost bound. -/
theorem Tree.foldl_insert_replicate (lo : Int) (k : Nat) :
    (List.replicate (k + 1) lo).foldl Tree.insert leaf = node leaf lo leaf := by
  rw [List.replicate_succ, List.foldl_cons]
  show (List.replicate k lo).foldl Tree.insert (node leaf lo leaf) = node leaf lo leaf
  induction k with
  | zero => rfl
  | succ k ih => simpa [List.replicate_succ, Tree.insert] using ih

/-- `listOf` reaches `k` copies of `lo` in `2 * k + 1` choices. Unlike a `cost_bounded` law this is
a *lower* bound — an exhibited run — which is what disproving a bound needs. -/
private theorem cost_mem_replicate {lo hi : Int} (h : lo ≤ hi) (k : Nat) :
    (List.replicate k lo, 2 * k + 1) ∈
      SPMF.support (listOf (chooseInt lo hi h) : SPMF.Cost (List Int)) := by
  induction k with
  | zero =>
    rw [listOf]
    cost_support_simp
    exact ⟨0, by omega, Or.inl ⟨rfl, rfl⟩⟩
  | succ k ih =>
    rw [listOf]
    cost_support_simp
    refine ⟨2 * k + 2, by omega, Or.inr ⟨lo, 1, 2 * k + 1, ⟨⟨le_rfl, h⟩, rfl⟩, ?_, by omega⟩⟩
    exact ⟨List.replicate k lo, 2 * k + 1, 0, ih, ⟨by simp [List.replicate_succ], rfl⟩, by omega⟩

/-- **There is no cost bound.** `IsCostBounded` charges a run to the value it produced, and this
generator can spend any number of choices to produce `node leaf lo leaf` — drawing `lo` again is
always possible and always absorbed. Bounding the *keys* with `chooseInt` does not help: what is
unbounded is the number of insertions, not the size of each one. A bound does exist on the drawn
list (`IsBounded_listOf`), and insertion discards exactly the information it is stated in. -/
theorem Tree.genBSTByInsertion.not_cost_bounded {lo hi : Int} (h : lo ≤ hi) (c : Tree Int → Nat) :
    ¬ IsCostBounded (Tree.genBSTByInsertion lo hi h) c := by
  intro hb
  set k := c (node leaf lo leaf) with hk
  have hmem : ((node leaf lo leaf : Tree Int), 2 * (k + 1) + 1)
      ∈ SPMF.support (Tree.genBSTByInsertion lo hi h : SPMF.Cost (Tree Int)) := by
    unfold Tree.genBSTByInsertion
    cost_support_simp
    exact ⟨List.replicate (k + 1) lo, 2 * (k + 1) + 1, 0, cost_mem_replicate h _,
      ⟨(Tree.foldl_insert_replicate lo k).symm, rfl⟩, by omega⟩
  have hle := IsBounded_iff.mp hb _ hmem
  dsimp only at hle
  omega

end BST
