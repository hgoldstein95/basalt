/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt
import BasaltExamples.BST.ByFiltering
import BasaltExamples.Nearly

/-!
# Nearly Binary Search Trees

`Tree.genNearlyBST` generates the trees that are not search trees but are one edit from one, each
with an edit that repairs it, where an edit relabels, inserts, or deletes a node (`Tree.Edit`). It
is `genNearly` (`BasaltExamples/Nearly.lean`) at `Tree.genBST` and a generator of edits,
`Tree.genEdit`, which draws no deletion because none breaks a search tree.
-/

open RandomChoice

namespace BST

/-! ## Edits -/

/-- One edit of a tree: relabel the root, insert a node above it, delete it when one of its children
is a leaf, or edit a subtree. -/
inductive Tree.Edit (α : Type) where
  | relabel (y : α) : Edit α
  | insertLeft (y : α) : Edit α
  | insertRight (y : α) : Edit α
  | deleteLeft : Edit α
  | deleteRight : Edit α
  | left (e : Edit α) : Edit α
  | right (e : Edit α) : Edit α
deriving Repr

/-- The edited tree, or `none` where the edit does not apply: there is no node to relabel, delete, or
descend into, or the node to delete has two children. -/
def Tree.Edit.apply : Tree.Edit α → Tree α → Option (Tree α)
  | relabel y, node l _ r => some (node l y r)
  | insertLeft y, t => some (node t y leaf)
  | insertRight y, t => some (node leaf y t)
  | deleteLeft, node t _ leaf => some t
  | deleteRight, node leaf _ t => some t
  | left e, node l x r => (e.apply l).map (node · x r)
  | right e, node l x r => (e.apply r).map (node l x ·)
  | _, _ => none

/-- Every key of the tree satisfies `K`. -/
def Tree.All (K : α → Prop) : Tree α → Prop
  | leaf => True
  | node l x r => K x ∧ l.All K ∧ r.All K

/-- `t` has keys in `[lo, hi]` and is not a search tree, and `e` makes it one. -/
def Tree.isNearlyBST (lo hi : Int) (t : Tree Int) (e : Tree.Edit Int) : Prop :=
  t.All (fun y => lo ≤ y ∧ y ≤ hi) ∧ Repairs Tree.Edit.apply (Tree.isBST lo hi) t e

/-! ## The generator -/

/-- Edits `t` at its root in a way that can break a search tree, a relabelling or an insertion with
a key from `[lo, hi]`, and returns the result with the edit that undoes it. -/
def Tree.genRootEdit [Gen G] (lo hi : Int) (h : lo ≤ hi) :
    Tree Int → G (Tree Int × Tree.Edit Int)
  | leaf => do
    let y ← chooseInt lo hi h
    oneOf! [
      fun _ => pure (node leaf y leaf, .deleteLeft),
      fun _ => pure (node leaf y leaf, .deleteRight)]
  | node l x r => do
    let y ← chooseInt lo hi h
    oneOf! [
      fun _ => pure (node l y r, .relabel x),
      fun _ => pure (node (node l x r) y leaf, .deleteLeft),
      fun _ => pure (node leaf y (node l x r), .deleteRight)]

/-- `Tree.genRootEdit` at a position chosen uniformly among the nodes and leaves of `t`. -/
def Tree.genEdit [Gen G] (lo hi : Int) (h : lo ≤ hi) : Tree Int → G (Tree Int × Tree.Edit Int)
  | leaf => Tree.genRootEdit lo hi h leaf
  | node l x r =>
    frequency! [
      (1, fun _ => Tree.genRootEdit lo hi h (node l x r)),
      (2 * l.size + 1, fun _ => do
        let c ← Tree.genEdit lo hi h l
        return (node c.1 x r, .left c.2)),
      (2 * r.size + 1, fun _ => do
        let c ← Tree.genEdit lo hi h r
        return (node l x c.1, .right c.2))
    ] (by simp)

/-- Generates a tree with keys in `[lo, hi]` that is not a search tree, with an edit that makes it
one. -/
def Tree.genNearlyBST [Gen G] (lo hi : Int) (h : lo ≤ hi := by gen_side_condition) :
    G (Tree Int × Tree.Edit Int) :=
  genNearly (Tree.genBST lo hi) (Tree.genEdit lo hi h) (Tree.isBSTb lo hi)

/-! ## Support -/

theorem Tree.isBST.mono {lo hi lo' hi' : Int} {t : Tree Int} (h : t.isBST lo hi) (hlo : lo' ≤ lo)
    (hhi : hi ≤ hi') : t.isBST lo' hi' := by
  induction t generalizing lo hi lo' hi' with
  | leaf => rfl
  | node l x r ihl ihr =>
    obtain ⟨h1, h2, hl, hr⟩ := h
    exact ⟨by omega, by omega, ihl hl hlo le_rfl, ihr hr le_rfl hhi⟩

theorem Tree.isBST.all {lo hi : Int} {t : Tree Int} (h : t.isBST lo hi) :
    t.All fun y => lo ≤ y ∧ y ≤ hi := by
  induction t generalizing lo hi with
  | leaf => trivial
  | node l x r ihl ihr =>
    obtain ⟨h1, h2, hl, hr⟩ := h
    exact ⟨⟨h1, h2⟩, ihl (hl.mono le_rfl (by omega)), ihr (hr.mono (by omega) le_rfl)⟩

theorem Tree.isBST.deleteLeft {lo hi y : Int} {t : Tree Int} (h : (node t y leaf).isBST lo hi) :
    t.isBST lo hi :=
  h.2.2.1.mono le_rfl (by have := h.2.1; omega)

theorem Tree.isBST.deleteRight {lo hi y : Int} {t : Tree Int} (h : (node leaf y t).isBST lo hi) :
    t.isBST lo hi :=
  h.2.2.2.mono (by have := h.1; omega) le_rfl

/-- The edit `Tree.genEdit` returns undoes the one it made. -/
theorem Tree.genEdit.sound {lo hi : Int} (h : lo ≤ hi) {t : Tree Int}
    (ht : t.All fun y => lo ≤ y ∧ y ≤ hi) :
    IsSoundFor (Tree.genEdit lo hi h t)
      fun c => c.1.All (fun y => lo ≤ y ∧ y ≤ hi) ∧ c.2.apply c.1 = some t := by
  induction t with
  | leaf =>
    rw [IsSoundFor.iff_obs]
    unfold Tree.genEdit
    walk
    all_goals simp_all [Tree.All, Tree.Edit.apply]
  | node l x r ihl ihr =>
    rw [IsSoundFor.iff_obs]
    unfold Tree.genEdit
    walk [(ihl ht.2.1).obs, (ihr ht.2.2).obs]
    all_goals simp_all [Tree.All, Tree.Edit.apply]

/-- `Tree.genEdit` reaches every tree that is not a search tree with each edit that makes it one. No
such edit is an insertion, since a deletion never breaks a search tree (`Tree.isBST.deleteLeft`,
`Tree.isBST.deleteRight`), which is why `Tree.genEdit` makes no deletion. -/
theorem Tree.genEdit.complete {lo hi : Int} (h : lo ≤ hi) {t t' : Tree Int} {e : Tree.Edit Int}
    (hk : t'.All fun y => lo ≤ y ∧ y ≤ hi) (he : e.apply t' = some t) {lo' hi' : Int}
    (ht : t.isBST lo' hi') (ht' : ¬ t'.isBST lo' hi') :
    (t', e) ∈ SPMF.support (Tree.genEdit lo hi h t) := by
  induction e generalizing t t' lo' hi' with
  | relabel x =>
    cases t' with
    | leaf => simp [Tree.Edit.apply] at he
    | node l y r =>
      obtain rfl : node l x r = t := by simpa [Tree.Edit.apply] using he
      rw [Tree.genEdit, SPMF.mem_support_iff_may]; walk
      exact .inl ⟨y, hk.1, .inl rfl⟩
  | insertLeft y =>
    obtain rfl : node t' y leaf = t := by simpa [Tree.Edit.apply] using he
    exact absurd ht.deleteLeft ht'
  | insertRight y =>
    obtain rfl : node leaf y t' = t := by simpa [Tree.Edit.apply] using he
    exact absurd ht.deleteRight ht'
  | deleteLeft =>
    cases t' with
    | leaf => simp [Tree.Edit.apply] at he
    | node a y b =>
      cases b with
      | node _ _ _ => simp [Tree.Edit.apply] at he
      | leaf =>
        obtain rfl : a = t := by simpa [Tree.Edit.apply] using he
        cases a <;> (rw [Tree.genEdit, SPMF.mem_support_iff_may]; walk)
        · exact ⟨y, hk.1, .inl rfl⟩
        · exact .inl ⟨y, hk.1, .inr (.inl rfl)⟩
  | deleteRight =>
    cases t' with
    | leaf => simp [Tree.Edit.apply] at he
    | node a y b =>
      cases a with
      | node _ _ _ => simp [Tree.Edit.apply] at he
      | leaf =>
        obtain rfl : b = t := by simpa [Tree.Edit.apply] using he
        cases b <;> (rw [Tree.genEdit, SPMF.mem_support_iff_may]; walk)
        · exact ⟨y, hk.1, .inr rfl⟩
        · exact .inl ⟨y, hk.1, .inr (.inr rfl)⟩
  | left e ih =>
    cases t' with
    | leaf => simp [Tree.Edit.apply] at he
    | node l' x r =>
      obtain ⟨l, hl, rfl⟩ : ∃ l, e.apply l' = some l ∧ node l x r = t := by
        simpa [Tree.Edit.apply] using he
      obtain ⟨h1, h2, hbl, hbr⟩ := ht
      have := ih hk.2.1 hl hbl fun hl' => ht' ⟨h1, h2, hl', hbr⟩
      rw [Tree.genEdit, SPMF.mem_support_iff_may]; walk
      exact .inr (.inl ⟨by omega, _, this, rfl⟩)
  | right e ih =>
    cases t' with
    | leaf => simp [Tree.Edit.apply] at he
    | node l x r' =>
      obtain ⟨r, hr, rfl⟩ : ∃ r, e.apply r' = some r ∧ node l x r = t := by
        simpa [Tree.Edit.apply] using he
      obtain ⟨h1, h2, hbl, hbr⟩ := ht
      have := ih hk.2.2 hr hbr fun hr' => ht' ⟨h1, h2, hbl, hr'⟩
      rw [Tree.genEdit, SPMF.mem_support_iff_may]; walk
      exact .inr (.inr ⟨by omega, _, this, rfl⟩)

theorem Tree.genNearlyBST.sound_complete {lo hi : Int} (h : lo ≤ hi) :
    IsSoundAndComplete (Tree.genNearlyBST lo hi h) fun c => Tree.isNearlyBST lo hi c.1 c.2 :=
  genNearly.sound_complete (fun _ => Tree.isBSTb_iff) Tree.genBST.sound_complete
    (fun _ ht => Tree.genEdit.sound h ht.all)
    (fun _ _ _ ht hk ht' he => Tree.genEdit.complete h hk he ht ht')

/-! ## Termination -/

theorem Tree.genEdit.terminates {lo hi : Int} (h : lo ≤ hi) (t : Tree Int) :
    IsAlmostSurelyTerminating (Tree.genEdit lo hi h t) := by
  induction t with
  | leaf =>
    rw [IsAlmostSurelyTerminating.iff_obs, Tree.genEdit]
    walk
    norm_num [ENNReal.div_self]
  | node l x r ihl ihr =>
    rw [IsAlmostSurelyTerminating.iff_obs, Tree.genEdit]
    walk [ihl.obs, ihr.obs]
    norm_num [ENNReal.div_self]
    rw [ENNReal.div_self (by simp) (by finiteness)]

/-- A node inserted above its own key, and its deletion: the nearly search tree every interval
has. -/
theorem Tree.isNearlyBST_node_node {lo hi : Int} (h : lo ≤ hi) :
    (node (node leaf lo leaf) lo leaf).isNearlyBST lo hi .deleteLeft :=
  ⟨⟨⟨le_rfl, h⟩, ⟨⟨le_rfl, h⟩, trivial, trivial⟩, trivial⟩, fun ⟨_, _, ⟨_, _, _⟩, _⟩ => by omega,
    node leaf lo leaf, rfl, le_rfl, h, rfl, rfl⟩

theorem Tree.genNearlyBST.terminates {lo hi : Int} (h : lo ≤ hi) :
    IsAlmostSurelyTerminating (Tree.genNearlyBST lo hi h) :=
  have ⟨hk, hr⟩ := Tree.isNearlyBST_node_node h
  genNearly.terminates (fun _ => Tree.isBSTb_iff) Tree.genBST.sound_complete.complete
    (fun _ _ _ ht hk ht' he => Tree.genEdit.complete h hk he ht ht') Tree.genBST.terminates
    (Tree.genEdit.terminates h) hk hr

/-! ## Faithfulness -/

theorem Tree.genEdit.faithful {lo hi : Int} (h : lo ≤ hi) (t : Tree Int) :
    IsFaithful (Tree.genEdit lo hi h t) where
  terminates := Tree.genEdit.terminates h t
  below _ _ _ := by
    induction t with
    | leaf => unfold Tree.genEdit; walk
    | node l x r ihl ihr => unfold Tree.genEdit; walk
  approx := by
    induction t with
    | leaf => unfold Tree.genEdit; walk
    | node l x r ihl ihr => unfold Tree.genEdit; walk

theorem Tree.genNearlyBST.faithful {lo hi : Int} (h : lo ≤ hi) :
    IsFaithful (Tree.genNearlyBST lo hi h) := by
  faithful_fixpoint [Tree.genNearlyBST.terminates, Tree.genBST.faithful, Tree.genEdit.faithful]

/-! ## Cost -/

/-- An edit costs one choice per node above its position and two there. The whole generator
retries, so only its edits have a bound. -/
theorem Tree.genEdit.cost_bounded {lo hi : Int} (h : lo ≤ hi) (t : Tree Int) :
    IsCostBounded (Tree.genEdit lo hi h t) (fun c => c.1.size + 2) := by
  induction t with
  | leaf =>
    rw [IsCostBounded.iff_obs]
    unfold Tree.genEdit
    walk
    all_goals simp only [Tree.size]; omega
  | node l x r ihl ihr =>
    rw [IsCostBounded.iff_obs]
    unfold Tree.genEdit
    walk [ihl.obs, ihr.obs]
    all_goals simp only [Tree.size]; omega

end BST
