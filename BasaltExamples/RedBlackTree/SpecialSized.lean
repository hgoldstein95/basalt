/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt
import Basalt.Combinators
import BasaltExamples.RedBlackTree.Sized
import BasaltExamples.RedBlackTree.Special

open RandomChoice

/-!
# Generating Red-Black Trees That Rebalance, by Node Count

`genSpecialUpTo x N lo hi` generates the red-black trees of at most `N` keys into which inserting
`x` makes `balance` restructure — the paper's bound on special red-black trees. It is the union of
`genSpecialBlackSized`, the size-indexed form of `genSpecialBlack`, over the `(black height, size)`
pairs such a tree can have; the extra key a special tree needs over the all-black minimum for its
black height (`RBTree.minKeys_lt_size_of_searchEndsUnderRed`) is what makes that range exact.
-/

namespace RedBlackTree

namespace RBTree

/-- A subtree whose search for `x` ends beneath a red node holds one key more than the minimum for
its black height: the minimum is all black, and this one has a red node with a leaf child. -/
theorem minKeys_lt_size_of_searchEndsUnderRed {x : Int} {n : Nat} {t : RBTree}
    (hbh : t.hasBlackHeight n) (hs : t.searchEndsUnderRed x) : minKeys n < t.size := by
  induction t generalizing n with
  | leaf => exact absurd hs not_false
  | node c l y r ihl ihr =>
    cases c with
    | red =>
      obtain ⟨hl, hr⟩ := hbh
      have hml := minKeys_le_size hl
      have hmr := minKeys_le_size hr
      simp only [searchEndsUnderRed] at hs
      split at hs
      · rcases hs with ⟨-, rfl⟩ | hs
        · simp only [hasBlackHeight] at hl
          subst hl
          simp only [size, minKeys]
          omega
        · have := ihl hl hs
          simp only [size]
          omega
      · split at hs
        · rcases hs with ⟨-, rfl⟩ | hs
          · simp only [hasBlackHeight] at hr
            subst hr
            simp only [size, minKeys]
            omega
          · have := ihr hr hs
            simp only [size]
            omega
        · exact absurd hs not_false
    | black =>
      cases n with
      | zero => exact absurd hbh not_false
      | succ m =>
        obtain ⟨hl, hr⟩ := hbh
        have hml := minKeys_le_size hl
        have hmr := minKeys_le_size hr
        simp only [searchEndsUnderRed] at hs
        split at hs
        · rcases hs with ⟨hc, -⟩ | hs
          · exact absurd hc (by simp)
          · have := ihl hl hs
            simp only [size, minKeys]
            omega
        · split at hs
          · rcases hs with ⟨hc, -⟩ | hs
            · exact absurd hc (by simp)
            · have := ihr hr hs
              simp only [size, minKeys]
              omega
          · exact absurd hs not_false

/-- A tree ordered inside `[lo, hi]` that avoids a key `x` of that interval leaves that key's
value free, so it holds one fewer key than the interval has values. -/
theorem size_lt_of_isBST_of_not_contains {lo hi x : Int} {t : RBTree} (h : t.isBST lo hi)
    (hx : ¬ t.contains x) (h1 : lo ≤ x) (h2 : x ≤ hi) : t.size + 1 ≤ (hi - lo + 1).toNat := by
  induction t generalizing lo hi with
  | leaf => simp only [size]; omega
  | node c l y r ihl ihr =>
    obtain ⟨hylo, hyhi, hlbst, hrbst⟩ := h
    simp only [contains, not_or] at hx
    obtain ⟨hxy, hlx, hrx⟩ := hx
    have hlsz := size_le_of_isBST hlbst
    have hrsz := size_le_of_isBST hrbst
    rcases lt_trichotomy x y with hlt | heq | hgt
    · have := ihl hlbst hlx h1 (by omega)
      simp only [size]; omega
    · exact absurd heq hxy
    · have := ihr hrbst hrx (by omega) h2
      simp only [size]; omega

end RBTree

/-- The value a special child's interval must hold beyond its own keys when the child sits below a
pivot above `x`: the child avoids `x`, and `x` falls inside its interval exactly when `lo ≤ x`. -/
def gapAbove (x lo : Int) : Nat := if lo ≤ x then 1 else 0

/-- `gapAbove`'s mirror, for a special child sitting above a pivot below `x`. -/
def gapBelow (x hi : Int) : Nat := if x ≤ hi then 1 else 0

/-- The value a tree avoiding `x` must leave free in `[lo, hi]`. -/
def gapIn (x lo hi : Int) : Nat := if lo ≤ x ∧ x ≤ hi then 1 else 0

theorem isSpecialTree_size_bounds {x : Int} {n : Nat} (sl : Nat) (a b : Int) (u : RBTree) :
    (isSpecialTree x a b n u ∧ u.size = sl) →
      u.size = sl ∧ minKeys n + 1 ≤ sl ∧ sl ≤ maxKeysBlack n := by
  rintro ⟨⟨hrb, -, hsr⟩, rfl⟩
  exact ⟨rfl, RBTree.minKeys_lt_size_of_searchEndsUnderRed hrb.2.2.2 hsr,
    RBTree.size_le_maxKeysBlack hrb⟩

theorem isSpecialSubtree_size_bounds {x : Int} {n : Nat} (sl : Nat) (a b : Int) (u : RBTree) :
    (isSpecialSubtree x a b n u ∧ u.size = sl) →
      u.size = sl ∧ minKeys n + 1 ≤ sl ∧ sl ≤ maxKeysAny n := by
  rintro ⟨⟨hsub, -, hsr⟩, rfl⟩
  exact ⟨rfl, RBTree.minKeys_lt_size_of_searchEndsUnderRed hsub.2.2 hsr,
    RBTree.size_le_maxKeysAny hsub⟩

theorem isSpecialTree_width {x : Int} {n : Nat} {lo hi : Int} {t : RBTree}
    (h : isSpecialTree x lo hi n t) : t.size + gapIn x lo hi ≤ (hi - lo + 1).toNat := by
  have hle := RBTree.size_le_of_isBST h.1.2.1
  simp only [gapIn]
  split <;> rename_i hx
  · have := RBTree.size_lt_of_isBST_of_not_contains h.1.2.1 h.2.1 hx.1 hx.2
    omega
  · omega

theorem isSpecialTree_width_left {x lo : Int} {n : Nat} (sl : Nat) (y : Int) (u : RBTree)
    (hy : x + 1 ≤ y) (h : isSpecialTree x lo (y - 1) n u ∧ u.size = sl) :
    sl + gapAbove x lo ≤ (y - lo).toNat := by
  simp only [gapAbove]
  split <;> rename_i hx
  · have := RBTree.size_lt_of_isBST_of_not_contains h.1.1.2.1 h.1.2.1 hx (by omega)
    omega
  · have := RBTree.size_le_of_isBST h.1.1.2.1
    omega

theorem isSpecialTree_width_right {x hi : Int} {n : Nat} (sr : Nat) (y : Int) (u : RBTree)
    (hy : y ≤ x - 1) (h : isSpecialTree x (y + 1) hi n u ∧ u.size = sr) :
    sr + gapBelow x hi ≤ (hi - y).toNat := by
  simp only [gapBelow]
  split <;> rename_i hx
  · have := RBTree.size_lt_of_isBST_of_not_contains h.1.1.2.1 h.1.2.1 (by omega) hx
    omega
  · have := RBTree.size_le_of_isBST h.1.1.2.1
    omega

theorem isSpecialSubtree_width_left {x lo : Int} {n : Nat} (sl : Nat) (y : Int) (u : RBTree)
    (hy : x + 1 ≤ y) (h : isSpecialSubtree x lo (y - 1) n u ∧ u.size = sl) :
    sl + gapAbove x lo ≤ (y - lo).toNat := by
  simp only [gapAbove]
  split <;> rename_i hx
  · have := RBTree.size_lt_of_isBST_of_not_contains h.1.1.1 h.1.2.1 hx (by omega)
    omega
  · have := RBTree.size_le_of_isBST h.1.1.1
    omega

theorem isSpecialSubtree_width_right {x hi : Int} {n : Nat} (sr : Nat) (y : Int) (u : RBTree)
    (hy : y ≤ x - 1) (h : isSpecialSubtree x (y + 1) hi n u ∧ u.size = sr) :
    sr + gapBelow x hi ≤ (hi - y).toNat := by
  simp only [gapBelow]
  split <;> rename_i hx
  · have := RBTree.size_lt_of_isBST_of_not_contains h.1.1.1 h.1.2.1 (by omega) hx
    omega
  · have := RBTree.size_le_of_isBST h.1.1.1
    omega

/-! ## The generators -/

/-- A red root keyed above `x`, so `x`'s search descends into the left child, which `gs` makes
special; the right child is an ordinary black-rooted subtree. -/
def genRedAboveSized [Gen G] (x : Int) (n : Nat) (gs : Nat → Int → Int → G RBTree)
    (s : Nat) (lo hi : Int) : G RBTree :=
  genNodeSized .red (minKeys n + 1) (maxKeysBlack n) (minKeys n) (maxKeysBlack n)
    (gapAbove x lo) 0 (x + 1) hi gs (fun s' a b => genBlackSized n s' a b) s lo hi

/-- A red root keyed below `x`, the mirror of `genRedAboveSized`. -/
def genRedBelowSized [Gen G] (x : Int) (n : Nat) (gs : Nat → Int → Int → G RBTree)
    (s : Nat) (lo hi : Int) : G RBTree :=
  genNodeSized .red (minKeys n) (maxKeysBlack n) (minKeys n + 1) (maxKeysBlack n)
    0 (gapBelow x hi) lo (x - 1) (fun s' a b => genBlackSized n s' a b) gs s lo hi

/-- Wraps a black-rooted special generator `gs` of black height `n` into one that may also produce
a red root. At black height `0` the only special subtree is the red node the search runs off; above
it that node cannot occur, and a red root's child on `x`'s side carries the property instead. -/
def specialAnyOfSized [Gen G] (x : Int) (n : Nat) (gs : Nat → Int → Int → G RBTree)
    (s : Nat) (lo hi : Int) : G RBTree :=
  if n = 0 then
    pickOf2 (p := s = 1 ∧ max lo (x + 1) ≤ hi) (q := s = 1 ∧ lo ≤ min hi (x - 1))
      (fun h => genLeafAbove x lo hi h.2) (fun h => genLeafBelow x lo hi h.2)
  else
    pickOf3All
      (p := minKeys n + 1 ≤ s ∧ s ≤ maxKeysBlack n ∧ s + gapIn x lo hi ≤ (hi - lo + 1).toNat)
      (q := NodeRoom (minKeys n + 1) (maxKeysBlack n) (minKeys n) (maxKeysBlack n)
        (gapAbove x lo) 0 (x + 1) hi s lo hi)
      (r := NodeRoom (minKeys n) (maxKeysBlack n) (minKeys n + 1) (maxKeysBlack n)
        0 (gapBelow x hi) lo (x - 1) s lo hi)
      (fun _ => gs s lo hi)
      (fun _ => genRedAboveSized x n gs s lo hi)
      (fun _ => genRedBelowSized x n gs s lo hi)

/-- Generates the black-rooted red-black trees of black height `n` holding exactly `s` keys, with
keys in `[lo, hi]`, into which inserting `x` rebalances. A black-rooted tree of black height `0` is
a leaf, and no leaf is special. -/
def genSpecialBlackSized [Gen G] (x : Int) : (n s : Nat) → (lo hi : Int) → G RBTree
  | 0, _, _, _ => default
  | m + 1, s, lo, hi =>
      pickOf2
        (p := NodeRoom (minKeys m + 1) (maxKeysAny m) (minKeys m) (maxKeysAny m)
          (gapAbove x lo) 0 (x + 1) hi s lo hi)
        (q := NodeRoom (minKeys m) (maxKeysAny m) (minKeys m + 1) (maxKeysAny m)
          0 (gapBelow x hi) lo (x - 1) s lo hi)
        (fun _ => genNodeSized .black (minKeys m + 1) (maxKeysAny m) (minKeys m) (maxKeysAny m)
          (gapAbove x lo) 0 (x + 1) hi
          (fun s' a b => specialAnyOfSized x m
            (fun s'' a' b' => genSpecialBlackSized x m s'' a' b') s' a b)
          (fun s' a b => genAnySized m s' a b) s lo hi)
        (fun _ => genNodeSized .black (minKeys m) (maxKeysAny m) (minKeys m + 1) (maxKeysAny m)
          0 (gapBelow x hi) lo (x - 1)
          (fun s' a b => genAnySized m s' a b)
          (fun s' a b => specialAnyOfSized x m
            (fun s'' a' b' => genSpecialBlackSized x m s'' a' b') s' a b) s lo hi)


/-! ## Support -/

theorem specialAnyOfSized_mem_support {x : Int} {n : Nat} {gs : Nat → Int → Int → SPMF RBTree}
    (hgs : ∀ s a b u, u ∈ SPMF.support (gs s a b) ↔ isSpecialTree x a b n u ∧ u.size = s)
    (s : Nat) (lo hi : Int) (t : RBTree) :
    t ∈ SPMF.support (specialAnyOfSized x n gs s lo hi)
      ↔ isSpecialSubtree x lo hi n t ∧ t.size = s := by
  unfold specialAnyOfSized genRedAboveSized genRedBelowSized
  split <;> rename_i hn
  · subst hn
    rw [mem_support_pickOf2
      (A := s = 1 ∧ ∃ y, (max lo (x + 1) ≤ y ∧ y ≤ hi) ∧ t = .node .red .leaf y .leaf)
      (B := s = 1 ∧ ∃ y, (lo ≤ y ∧ y ≤ min hi (x - 1)) ∧ t = .node .red .leaf y .leaf)
      (fun h => by
        rw [genLeafAbove_mem_support]
        exact ⟨fun hh => ⟨h.1, hh⟩, fun hh => hh.2⟩)
      (fun h => by
        rw [genLeafBelow_mem_support]
        exact ⟨fun hh => ⟨h.1, hh⟩, fun hh => hh.2⟩)
      (fun h => ⟨h.1, by obtain ⟨-, y, hy, -⟩ := h; omega⟩)
      (fun h => ⟨h.1, by obtain ⟨-, y, hy, -⟩ := h; omega⟩)]
    constructor
    · rintro (⟨rfl, y, ⟨hy1, hy2⟩, rfl⟩ | ⟨rfl, y, ⟨hy1, hy2⟩, rfl⟩) <;>
        simp only [max_le_iff, le_min_iff] at hy1 hy2
      · refine ⟨⟨⟨⟨by omega, by omega, trivial, trivial⟩,
          ⟨fun _ => ⟨rfl, rfl⟩, trivial, trivial⟩, rfl, rfl⟩, ?_, ?_⟩, rfl⟩
        · simp only [RBTree.contains, not_or]
          exact ⟨by omega, not_false, not_false⟩
        · simp only [RBTree.searchEndsUnderRed, if_pos (show x < y by omega)]
          exact Or.inl ⟨trivial, trivial⟩
      · refine ⟨⟨⟨⟨by omega, by omega, trivial, trivial⟩,
          ⟨fun _ => ⟨rfl, rfl⟩, trivial, trivial⟩, rfl, rfl⟩, ?_, ?_⟩, rfl⟩
        · simp only [RBTree.contains, not_or]
          exact ⟨by omega, not_false, not_false⟩
        · simp only [RBTree.searchEndsUnderRed, if_neg (show ¬ x < y by omega),
            if_pos (show y < x by omega)]
          exact Or.inl ⟨trivial, trivial⟩
    · rintro ⟨⟨hsub, hx, hs⟩, hsz⟩
      rcases t with _ | ⟨c, a, y, b⟩
      · exact absurd hs not_false
      cases c
      case _ =>
        obtain ⟨⟨hlo, hhi, habst, hbbst⟩, ⟨hcc, hanrr, hbnrr⟩, habh, hbbh⟩ := hsub
        obtain ⟨hac, hbc⟩ := hcc rfl
        obtain rfl : a = .leaf := RBTree.isRB_zero_iff.mp ⟨hac, habst, hanrr, habh⟩
        obtain rfl : b = .leaf := RBTree.isRB_zero_iff.mp ⟨hbc, hbbst, hbnrr, hbbh⟩
        simp only [RBTree.contains, not_or] at hx
        simp only [RBTree.searchEndsUnderRed] at hs
        simp only [RBTree.size] at hsz
        rcases lt_trichotomy x y with hlt | heq | hgt
        · exact Or.inl ⟨by omega, y, ⟨by omega, by omega⟩, rfl⟩
        · exact absurd heq hx.1
        · exact Or.inr ⟨by omega, y, ⟨by omega, by omega⟩, rfl⟩
      case _ => exact absurd hsub.2.2 not_false
  · rw [mem_support_pickOf3All (fun _ => hgs s lo hi t)
      (fun _ => genNodeSized_mem_support
        (Pl := fun sl a b u => isSpecialTree x a b n u ∧ u.size = sl)
        (Pr := fun sr a b u => u.isRB a b n ∧ u.size = sr)
        (fun sl a b u => hgs sl a b u) (fun sr a b u => genBlackSized_mem_support n sr a b u)
        isSpecialTree_size_bounds isRB_size_bounds
        isSpecialTree_width_left isRB_width_right s t)
      (fun _ => genNodeSized_mem_support
        (Pl := fun sl a b u => u.isRB a b n ∧ u.size = sl)
        (Pr := fun sr a b u => isSpecialTree x a b n u ∧ u.size = sr)
        (fun sl a b u => genBlackSized_mem_support n sl a b u) (fun sr a b u => hgs sr a b u)
        isRB_size_bounds isSpecialTree_size_bounds
        isRB_width_left isSpecialTree_width_right s t)
      (fun h => by
        obtain ⟨-, h1, h2⟩ := isSpecialTree_size_bounds t.size lo hi t ⟨h.1, rfl⟩
        have h3 := isSpecialTree_width h.1
        exact ⟨by omega, by omega, by omega⟩)
      (nodeRoom_of_support isSpecialTree_size_bounds isRB_size_bounds
        isSpecialTree_width_left isRB_width_right)
      (nodeRoom_of_support isRB_size_bounds isSpecialTree_size_bounds
        isRB_width_left isSpecialTree_width_right)]
    constructor
    · rintro (⟨⟨⟨-, hsub⟩, hx, hs⟩, hsz⟩
        | ⟨y, a, b, hlo, hhi, hylo, -, ⟨⟨⟨hac, habst, hanrr, habh⟩, hax, has⟩, -⟩,
            ⟨⟨hbc, hbbst, hbnrr, hbbh⟩, -⟩, hsize, rfl⟩
        | ⟨y, a, b, hlo, hhi, -, hyhi, ⟨⟨hac, habst, hanrr, habh⟩, -⟩,
            ⟨⟨⟨hbc, hbbst, hbnrr, hbbh⟩, hbx, hbs⟩, -⟩, hsize, rfl⟩)
      · exact ⟨⟨hsub, hx, hs⟩, hsz⟩
      · refine ⟨⟨⟨⟨hlo, hhi, habst, hbbst⟩, ⟨fun _ => ⟨hac, hbc⟩, hanrr, hbnrr⟩, habh, hbbh⟩,
          ?_, ?_⟩, by simpa [RBTree.size] using hsize⟩
        · simp only [RBTree.contains, not_or]
          exact ⟨by omega, hax, fun hc => by have := RBTree.contains_bounds hbbst hc; omega⟩
        · simp only [RBTree.searchEndsUnderRed, if_pos (show x < y by omega)]
          exact Or.inr has
      · refine ⟨⟨⟨⟨hlo, hhi, habst, hbbst⟩, ⟨fun _ => ⟨hac, hbc⟩, hanrr, hbnrr⟩, habh, hbbh⟩,
          ?_, ?_⟩, by simpa [RBTree.size] using hsize⟩
        · simp only [RBTree.contains, not_or]
          exact ⟨by omega, fun hc => by have := RBTree.contains_bounds habst hc; omega, hbx⟩
        · simp only [RBTree.searchEndsUnderRed, if_neg (show ¬ x < y by omega),
            if_pos (show y < x by omega)]
          exact Or.inr hbs
    · rintro ⟨⟨hsub, hx, hs⟩, hsz⟩
      rcases t with _ | ⟨c, a, y, b⟩
      · exact absurd hs not_false
      cases c
      case _ =>
        obtain ⟨⟨hlo, hhi, habst, hbbst⟩, ⟨hcc, hanrr, hbnrr⟩, habh, hbbh⟩ := hsub
        obtain ⟨hac, hbc⟩ := hcc rfl
        simp only [RBTree.contains, not_or] at hx
        obtain ⟨hxy, hax, hbx⟩ := hx
        simp only [RBTree.searchEndsUnderRed] at hs
        simp only [RBTree.size] at hsz
        rcases lt_trichotomy x y with hlt | heq | hgt
        · rw [if_pos hlt] at hs
          rcases hs with ⟨-, rfl⟩ | has
          · exact absurd habh hn
          · exact Or.inr (Or.inl ⟨y, a, b, hlo, hhi, by omega, hhi,
              ⟨⟨⟨hac, habst, hanrr, habh⟩, hax, has⟩, rfl⟩,
              ⟨⟨hbc, hbbst, hbnrr, hbbh⟩, rfl⟩, hsz, rfl⟩)
        · exact absurd heq hxy
        · rw [if_neg (by omega), if_pos hgt] at hs
          rcases hs with ⟨-, rfl⟩ | hbs
          · exact absurd hbbh hn
          · exact Or.inr (Or.inr ⟨y, a, b, hlo, hhi, hlo, by omega,
              ⟨⟨hac, habst, hanrr, habh⟩, rfl⟩,
              ⟨⟨⟨hbc, hbbst, hbnrr, hbbh⟩, hbx, hbs⟩, rfl⟩, hsz, rfl⟩)
      case _ => exact Or.inl ⟨⟨⟨rfl, hsub⟩, hx, hs⟩, hsz⟩

theorem genSpecialBlackSized_mem_support (x : Int) (n s : Nat) (lo hi : Int) (t : RBTree) :
    t ∈ SPMF.support (genSpecialBlackSized x n s lo hi)
      ↔ isSpecialTree x lo hi n t ∧ t.size = s := by
  induction n generalizing s lo hi t with
  | zero =>
    rw [genSpecialBlackSized, mem_support_default]
    refine ⟨False.elim, ?_⟩
    rintro ⟨⟨hrb, -, hs⟩, -⟩
    rw [RBTree.isRB_zero_iff] at hrb
    subst hrb
    exact absurd hs not_false
  | succ m ih =>
    have hspec : ∀ s' a b u,
        u ∈ SPMF.support (specialAnyOfSized x m
          (fun s'' a' b' => genSpecialBlackSized x m s'' a' b') s' a b)
          ↔ isSpecialSubtree x a b m u ∧ u.size = s' :=
      fun s' a b u => specialAnyOfSized_mem_support (fun s'' a' b' u' => ih s'' a' b' u') s' a b u
    rw [genSpecialBlackSized, mem_support_pickOf2
      (fun _ => genNodeSized_mem_support
        (Pl := fun sl a b u => isSpecialSubtree x a b m u ∧ u.size = sl)
        (Pr := fun sr a b u => u.isRBSubtree a b m ∧ u.size = sr)
        hspec (fun sr a b u => genAnySized_mem_support m sr a b u)
        isSpecialSubtree_size_bounds isRBSubtree_size_bounds
        isSpecialSubtree_width_left isRBSubtree_width_right s t)
      (fun _ => genNodeSized_mem_support
        (Pl := fun sl a b u => u.isRBSubtree a b m ∧ u.size = sl)
        (Pr := fun sr a b u => isSpecialSubtree x a b m u ∧ u.size = sr)
        (fun sl a b u => genAnySized_mem_support m sl a b u) hspec
        isRBSubtree_size_bounds isSpecialSubtree_size_bounds
        isRBSubtree_width_left isSpecialSubtree_width_right s t)
      (nodeRoom_of_support isSpecialSubtree_size_bounds isRBSubtree_size_bounds
        isSpecialSubtree_width_left isRBSubtree_width_right)
      (nodeRoom_of_support isRBSubtree_size_bounds isSpecialSubtree_size_bounds
        isRBSubtree_width_left isSpecialSubtree_width_right)]
    constructor
    · rintro (⟨y, l, r, hlo, hhi, hylo, -, ⟨⟨hlsub, hlx, hls⟩, -⟩, ⟨hrsub, -⟩, hsize, rfl⟩
        | ⟨y, l, r, hlo, hhi, -, hyhi, ⟨hlsub, -⟩, ⟨⟨hrsub, hrx, hrs⟩, -⟩, hsize, rfl⟩)
      · refine ⟨⟨⟨rfl, ⟨hlo, hhi, hlsub.1, hrsub.1⟩,
          ⟨fun h => Color.noConfusion h, hlsub.2.1, hrsub.2.1⟩, hlsub.2.2, hrsub.2.2⟩,
          ?_, ?_⟩, by simpa [RBTree.size] using hsize⟩
        · simp only [RBTree.contains, not_or]
          exact ⟨by omega, hlx, fun hc => by have := RBTree.contains_bounds hrsub.1 hc; omega⟩
        · simp only [RBTree.searchEndsUnderRed, if_pos (show x < y by omega)]
          exact Or.inr hls
      · refine ⟨⟨⟨rfl, ⟨hlo, hhi, hlsub.1, hrsub.1⟩,
          ⟨fun h => Color.noConfusion h, hlsub.2.1, hrsub.2.1⟩, hlsub.2.2, hrsub.2.2⟩,
          ?_, ?_⟩, by simpa [RBTree.size] using hsize⟩
        · simp only [RBTree.contains, not_or]
          exact ⟨by omega, fun hc => by have := RBTree.contains_bounds hlsub.1 hc; omega, hrx⟩
        · simp only [RBTree.searchEndsUnderRed, if_neg (show ¬ x < y by omega),
            if_pos (show y < x by omega)]
          exact Or.inr hrs
    · rintro ⟨⟨hrb, hx, hs⟩, hsz⟩
      rcases t with _ | ⟨c, l, y, r⟩
      · exact absurd hs not_false
      cases c
      case _ => exact absurd hrb.1 (by simp [RBTree.rootColor])
      case _ =>
        obtain ⟨-, ⟨hlo, hhi, hlbst, hrbst⟩, ⟨-, hlnrr, hrnrr⟩, hlbh, hrbh⟩ := hrb
        simp only [RBTree.contains, not_or] at hx
        obtain ⟨hxy, hlx, hrx⟩ := hx
        simp only [RBTree.searchEndsUnderRed] at hs
        simp only [RBTree.size] at hsz
        rcases lt_trichotomy x y with hlt | heq | hgt
        · rw [if_pos hlt] at hs
          rcases hs with ⟨hcr, -⟩ | hls
          · exact absurd hcr (by simp)
          · exact Or.inl ⟨y, l, r, hlo, hhi, by omega, hhi,
              ⟨⟨⟨hlbst, hlnrr, hlbh⟩, hlx, hls⟩, rfl⟩, ⟨⟨hrbst, hrnrr, hrbh⟩, rfl⟩, hsz, rfl⟩
        · exact absurd heq hxy
        · rw [if_neg (by omega), if_pos hgt] at hs
          rcases hs with ⟨hcr, -⟩ | hrs
          · exact absurd hcr (by simp)
          · exact Or.inr ⟨y, l, r, hlo, hhi, hlo, by omega,
              ⟨⟨hlbst, hlnrr, hlbh⟩, rfl⟩, ⟨⟨⟨hrbst, hrnrr, hrbh⟩, hrx, hrs⟩, rfl⟩, hsz, rfl⟩


/-! ## At most `N` keys -/

/-- The `(black height, size)` pairs a black-rooted special red-black tree of at most `N` keys
drawn from `[lo, hi]` can have: one key more than the all-black minimum for its black height, and
no more than a black-rooted tree of that height holds. -/
def specialIndices (x : Int) (N : Nat) (lo hi : Int) : List (Nat × Nat) :=
  (indexPairs N).filter fun p =>
    decide (minKeys p.1 + 1 ≤ p.2 ∧ p.2 ≤ maxKeysBlack p.1 ∧
      p.2 + gapIn x lo hi ≤ (hi - lo + 1).toNat)

theorem mem_specialIndices {x : Int} {N n s : Nat} {lo hi : Int} :
    (n, s) ∈ specialIndices x N lo hi ↔
      (n ≤ N ∧ s ≤ N) ∧ minKeys n + 1 ≤ s ∧ s ≤ maxKeysBlack n ∧
        s + gapIn x lo hi ≤ (hi - lo + 1).toNat := by
  simp [specialIndices, List.mem_filter, mem_indexPairs]

theorem mem_specialIndices_of_isSpecialTree {x : Int} {N n : Nat} {lo hi : Int} {t : RBTree}
    (hsp : isSpecialTree x lo hi n t) (hsz : t.size ≤ N) :
    (n, t.size) ∈ specialIndices x N lo hi := by
  rw [mem_specialIndices]
  obtain ⟨-, h1, h2⟩ := isSpecialTree_size_bounds t.size lo hi t ⟨hsp, rfl⟩
  have h3 := isSpecialTree_width hsp
  have := RBTree.le_minKeys n
  exact ⟨⟨by omega, hsz⟩, h1, h2, h3⟩

/-- Generates the red-black trees of at most `N` keys, drawn from `[lo, hi]`, into which inserting
`x` rebalances — the paper's bound on special red-black trees — as the union of
`genSpecialBlackSized` over every `(black height, size)` pair such a tree can have. -/
def genSpecialUpTo [Gen G] (x : Int) (N : Nat) (lo hi : Int) : G RBTree :=
  if h : specialIndices x N lo hi ≠ [] then
    oneOf ((specialIndices x N lo hi).map fun p => fun (_ : Unit) =>
      genSpecialBlackSized x p.1 p.2 lo hi) (by simpa using h)
  else default

theorem genSpecialUpTo_mem_support (x : Int) (N : Nat) (lo hi : Int) (t : RBTree) :
    t ∈ SPMF.support (genSpecialUpTo x N lo hi)
      ↔ (∃ n, isSpecialTree x lo hi n t) ∧ t.size ≤ N := by
  unfold genSpecialUpTo
  split <;> rename_i hne
  · rw [SPMF.mem_support_oneOf_iff]
    simp only [List.mem_map]
    constructor
    · rintro ⟨gg, ⟨⟨n, s⟩, hmem, rfl⟩, hsupp⟩
      rw [genSpecialBlackSized_mem_support] at hsupp
      obtain ⟨hsp, rfl⟩ := hsupp
      exact ⟨⟨n, hsp⟩, (mem_specialIndices.mp hmem).1.2⟩
    · rintro ⟨⟨n, hsp⟩, hsz⟩
      exact ⟨_, ⟨(n, t.size), mem_specialIndices_of_isSpecialTree hsp hsz, rfl⟩,
        (genSpecialBlackSized_mem_support x n t.size lo hi t).mpr ⟨hsp, rfl⟩⟩
  · rw [mem_support_default]
    refine ⟨False.elim, ?_⟩
    rintro ⟨⟨n, hsp⟩, hsz⟩
    rw [not_not] at hne
    have := mem_specialIndices_of_isSpecialTree (N := N) hsp hsz
    rw [hne] at this
    exact absurd this (List.not_mem_nil)

theorem genSpecialUpTo.sound_complete :
    IsSoundAndComplete (genSpecialUpTo x N lo hi)
      (fun t => (∃ n, t.isRB lo hi n) ∧ ¬ t.contains x ∧ t.insertRebalances x ∧ t.size ≤ N) := by
  intro t
  rw [genSpecialUpTo_mem_support]
  constructor
  · rintro ⟨⟨n, hrb, hx, hs⟩, hsz⟩
    exact ⟨⟨n, hrb⟩, hx, (RBTree.insertRebalances_iff hrb.2.2.1 hrb.1 hx).mpr hs, hsz⟩
  · rintro ⟨⟨n, hrb⟩, hx, hir, hsz⟩
    exact ⟨⟨n, hrb, hx, (RBTree.insertRebalances_iff hrb.2.2.1 hrb.1 hx).mp hir⟩, hsz⟩

end RedBlackTree
