/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import BasaltExamples.SplayTree.Basic

open RandomChoice

/-!
# Splay Trees: Packed Subtrees

`Tree.genPacked s q lo hi` generates a search tree with exactly `s` nodes, all of them within depth
`q`, and keys in `[lo, hi]`. It is the building block the constructive special-tree generator hangs
off its access path: fixing the size exactly pins the total node count, while capping the depth
bounds what the subtree contributes after a splay.
-/

namespace SplayTree

/-- A tree of height `h` holds at most `2 ^ h - 1` nodes. -/
theorem Tree.size_lt_two_pow_height (t : Tree) : t.size + 1 ≤ 2 ^ t.height := by
  induction t with
  | leaf => simp [Tree.size, Tree.height]
  | node l x r ihl ihr =>
    have hl : (2 : Nat) ^ l.height ≤ 2 ^ max l.height r.height :=
      Nat.pow_le_pow_right (by omega) (le_max_left _ _)
    have hr : (2 : Nat) ^ r.height ≤ 2 ^ max l.height r.height :=
      Nat.pow_le_pow_right (by omega) (le_max_right _ _)
    simp only [Tree.size, Tree.height, pow_succ]
    omega

@[simp]
theorem Tree.size_eq_zero_iff {t : Tree} : t.size = 0 ↔ t = .leaf := by
  cases t <;> simp [Tree.size]

@[simp]
theorem Tree.height_eq_zero_iff {t : Tree} : t.height = 0 ↔ t = .leaf := by
  cases t <;> simp [Tree.height]

/-- A search tree with exactly `s` nodes, every node within depth `q`, and keys in `[lo, hi]`. -/
def Tree.isPacked (s q : Nat) (lo hi : Int) (t : Tree) : Prop :=
  t.size = s ∧ t.height ≤ q ∧ t.isBST lo hi

/-- Generates a search tree with exactly `s` nodes, all within depth `q`, and keys in `[lo, hi]`.
The left-subtree size is drawn from the window that keeps both children within depth `q - 1`, and
the pivot from the window that leaves each child enough key space; both draws are offsets from `0`,
so the generator needs no feasibility proof and simply produces junk when `s` does not fit. -/
def Tree.genPacked [Gen G] : (s q : Nat) → (lo hi : Int) → G Tree
  | 0, _, _, _ => pure .leaf
  | _ + 1, 0, _, _ => pure .leaf
  | s + 1, q + 1, lo, hi => do
    let a ← chooseNat 0 (min s (2 ^ q - 1) - (s - (2 ^ q - 1)))
    let d ← chooseNat 0 (hi - lo - s).toNat
    let al := (s - (2 ^ q - 1)) + a
    let x := lo + (al : Int) + (d : Int)
    let l ← Tree.genPacked al q lo (x - 1)
    let r ← Tree.genPacked (s - al) q (x + 1) hi
    pure (.node l x r)

theorem Tree.genPacked_mem_support (t : Tree) (s q : Nat) (lo hi : Int)
    (hcap : s + 1 ≤ 2 ^ q) (hw : (s : Int) ≤ hi - lo + 1) :
    t ∈ SPMF.support (Tree.genPacked s q lo hi) ↔ t.isPacked s q lo hi := by
  induction q generalizing s lo hi t with
  | zero =>
    have hs : s = 0 := by simpa using hcap
    subst hs
    rw [Tree.genPacked]
    simp only [SPMF.mem_support_pure_iff, Tree.isPacked]
    constructor
    · rintro rfl; exact ⟨rfl, by simp [Tree.height], trivial⟩
    · rintro ⟨h, -, -⟩; exact Tree.size_eq_zero_iff.mp h
  | succ q ih =>
    cases s with
    | zero =>
      rw [Tree.genPacked]
      simp only [SPMF.mem_support_pure_iff, Tree.isPacked]
      constructor
      · rintro rfl; exact ⟨rfl, by simp [Tree.height], trivial⟩
      · rintro ⟨h, -, -⟩; exact Tree.size_eq_zero_iff.mp h
    | succ s =>
      cases t with
      | leaf =>
        rw [Tree.genPacked]
        support_simp [Tree.isPacked, Tree.size]
        simp
      | node l x r =>
        rw [Tree.genPacked]
        have hp : 1 ≤ 2 ^ q := Nat.one_le_two_pow
        support_simp [Tree.isPacked, Tree.size, Tree.height, Tree.isBST, Tree.node.injEq]
        constructor
        · rintro ⟨a, ⟨-, ha⟩, d, ⟨-, hd⟩, l', hl', r', hr', rfl, rfl, rfl⟩
          obtain ⟨hls, hlh, hlb⟩ := (ih _ _ _ _ (by omega) (by omega)).mp hl'
          obtain ⟨hrs, hrh, hrb⟩ := (ih _ _ _ _ (by omega) (by omega)).mp hr'
          exact ⟨by omega, by omega, by omega, by omega, hlb, hrb⟩
        · rintro ⟨hsz, hht, hlo, hhi, hbl, hbr⟩
          have hL := Tree.size_lt_two_pow_height l
          have hR := Tree.size_lt_two_pow_height r
          have hLh : (2 : Nat) ^ l.height ≤ 2 ^ q := Nat.pow_le_pow_right (by omega) (by omega)
          have hRh : (2 : Nat) ^ r.height ≤ 2 ^ q := Nat.pow_le_pow_right (by omega) (by omega)
          have hbl' := Tree.size_le_of_isBST hbl
          have hbr' := Tree.size_le_of_isBST hbr
          refine ⟨l.size - (s - (2 ^ q - 1)), ⟨Nat.zero_le _, by omega⟩,
                  (x - lo - l.size).toNat, ⟨Nat.zero_le _, by omega⟩, ?_⟩
          rw [show s - (2 ^ q - 1) + (l.size - (s - (2 ^ q - 1))) = l.size from by omega,
              show (((x - lo - l.size).toNat : Nat) : Int) = x - lo - l.size from by omega,
              show lo + (l.size : Int) + (x - lo - l.size) = x from by ring]
          exact ⟨l, (ih l l.size lo (x - 1) (by omega) (by omega)).mpr ⟨rfl, by omega, hbl⟩,
                 r, (ih r (s - l.size) (x + 1) hi (by omega) (by omega)).mpr
                      ⟨by omega, by omega, hbr⟩, rfl, rfl, rfl⟩

theorem Tree.genPacked.sound_complete {s q : Nat} {lo hi : Int}
    (hcap : s + 1 ≤ 2 ^ q) (hw : (s : Int) ≤ hi - lo + 1) :
    IsSoundAndComplete (Tree.genPacked s q lo hi) (Tree.isPacked s q lo hi) :=
  fun t => Tree.genPacked_mem_support t s q lo hi hcap hw

theorem Tree.genPacked.terminates (s q : Nat) (lo hi : Int) :
    IsAlmostSurelyTerminating (Tree.genPacked s q lo hi) := by
  induction q generalizing s lo hi with
  | zero => cases s <;> (rw [Tree.genPacked]; exact SPMF.IsPMF_pure _)
  | succ q ih =>
    cases s with
    | zero => rw [Tree.genPacked]; exact SPMF.IsPMF_pure _
    | succ s =>
      rw [Tree.genPacked]
      refine SPMF.IsPMF_bind (SPMF.IsPMF_chooseNat _ _ _) fun _ => ?_
      refine SPMF.IsPMF_bind (SPMF.IsPMF_chooseNat _ _ _) fun _ => ?_
      refine SPMF.IsPMF_bind (ih _ _ _) fun _ => ?_
      exact SPMF.IsPMF_bind (ih _ _ _) fun _ => SPMF.IsPMF_pure _

theorem Tree.genPacked.cost_bounded (s q : Nat) (lo hi : Int) :
    IsCostBounded (Tree.genPacked s q lo hi) (fun t => 2 * t.size) := by
  unfold IsCostBounded
  induction q generalizing s lo hi with
  | zero =>
    cases s <;>
      · rw [Tree.genPacked, IsBounded_iff]
        rintro ⟨t, n⟩ hmem
        cost_support_simp at hmem
        obtain ⟨rfl, rfl⟩ := hmem
        simp [Tree.size]
  | succ q ih =>
    cases s with
    | zero =>
      rw [Tree.genPacked, IsBounded_iff]
      rintro ⟨t, n⟩ hmem
      cost_support_simp at hmem
      obtain ⟨rfl, rfl⟩ := hmem
      simp [Tree.size]
    | succ s =>
      rw [Tree.genPacked, IsBounded_iff]
      rintro ⟨t, n⟩ hmem
      cost_support_simp at hmem
      obtain ⟨a, na, m2, ⟨-, hna⟩, ⟨d, nd, m3, ⟨-, hnd⟩,
        ⟨l, nl, m4, hl, ⟨r, nr, m5, hr, ⟨rfl, hm5⟩, hm4⟩, hm3⟩, hm2⟩, hn⟩ := hmem
      have hL := ih _ _ _ (l, nl) hl
      have hR := ih _ _ _ (r, nr) hr
      simp only [Tree.size]
      simp only at hL hR ⊢
      omega

/-- No tree of `s` nodes is shallower than `⌈log₂ (s + 1)⌉`, so a packed tree drawn at that depth
cap has *exactly* that height. This is what makes the depth cap `Nat.clog 2 (s + 1)` the useful one:
it fixes the subtree's height while leaving its shape free. -/
theorem Tree.clog_size_le_height (t : Tree) : Nat.clog 2 (t.size + 1) ≤ t.height :=
  Nat.clog_le_of_le_pow (Tree.size_lt_two_pow_height t)

end SplayTree
