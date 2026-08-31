/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt
import Basalt.Combinators
import BasaltExamples.RedBlackTree.Basic

open RandomChoice

/-!
# Generating Red-Black Trees That Rebalance

`genSpecialBlack x n lo hi` generates the red-black trees into which inserting `x` — a key the tree
does not already hold — makes `balance` restructure at least once. The generator is constructive
rather than filtering: `insertRebalances_iff` shows the property holds exactly when `x`'s search
runs off the tree beneath a red node, and the recursion forces the search path to end that way.
-/

namespace RedBlackTree

namespace RBTree

/-- The root is red and has a red child: the violation Okasaki's `balance` repairs. -/
def redRedRoot : RBTree → Prop
  | node .red l _ r => l.rootColor = .red ∨ r.rootColor = .red
  | _ => False

/-- The search for `x` runs off the tree at a leaf whose parent is red. -/
def searchEndsUnderRed (x : Int) : RBTree → Prop
  | leaf => False
  | node c l y r =>
    if x < y then (c = .red ∧ l = .leaf) ∨ l.searchEndsUnderRed x
    else if y < x then (c = .red ∧ r = .leaf) ∨ r.searchEndsUnderRed x
    else False

/-! ## What `balance` does -/

theorem balance_red (a : RBTree) (z : Int) (b : RBTree) :
    balance .red a z b = node .red a z b := by
  unfold balance; split <;> simp_all

theorem isRotation_iff (c : Color) (l : RBTree) (y : Int) (r : RBTree) :
    isRotation c l y r ↔ c = .black ∧ (redRedRoot l ∨ redRedRoot r) := by
  unfold isRotation balance
  split <;> simp_all [redRedRoot, rootColor]
  grind

theorem not_redRedRoot_balance_black (a : RBTree) (z : Int) (b : RBTree) :
    ¬ redRedRoot (balance .black a z b) := by
  unfold balance
  split <;> simp_all [redRedRoot, rootColor]

theorem not_redRedRoot_of_noRedRed {t : RBTree} (h : t.noRedRed) : ¬ redRedRoot t := by
  rcases t with _ | ⟨c, l, y, r⟩
  · simp [redRedRoot]
  cases c
  · obtain ⟨hc, -, -⟩ := h
    obtain ⟨hl, hr⟩ := hc rfl
    simp [redRedRoot, hl, hr]
  · simp [redRedRoot]

theorem not_redRedRoot_ins {x : Int} {t : RBTree} (h : t.rootColor = .black) :
    ¬ redRedRoot (t.ins x) := by
  rcases t with _ | ⟨c, l, y, r⟩
  · simp [ins, redRedRoot, rootColor]
  cases c
  · simp [rootColor] at h
  · simp only [ins]
    split
    · exact not_redRedRoot_balance_black _ _ _
    · split
      · exact not_redRedRoot_balance_black _ _ _
      · simp [redRedRoot]

/-- A red root can only appear where the tree already had one, where the tree was empty, or where
`balance` has just rotated. -/
theorem rootColor_ins_red {x : Int} {t : RBTree} (h : (t.ins x).rootColor = .red) :
    t = .leaf ∨ t.rootColor = .red ∨ t.insertRebalances x := by
  rcases t with _ | ⟨c, l, y, r⟩
  · exact Or.inl rfl
  cases c
  · exact Or.inr (Or.inl rfl)
  refine Or.inr (Or.inr ?_)
  simp only [ins] at h
  simp only [insertRebalances]
  split at h <;> rename_i hc
  · rw [if_pos hc]
    refine Or.inr ?_
    by_contra hnr
    simp only [isRotation, not_not] at hnr
    rw [hnr, rootColor] at h
    exact Color.noConfusion h
  · rw [if_neg hc]
    split at h <;> rename_i hc2
    · rw [if_pos hc2]
      refine Or.inr ?_
      by_contra hnr
      simp only [isRotation, not_not] at hnr
      rw [hnr, rootColor] at h
      exact Color.noConfusion h
    · rw [rootColor] at h
      exact Color.noConfusion h

/-- The induction behind `insertRebalances_iff`: a subtree either rebalances on its own or hands
its parent a red-red violation, exactly when `x`'s search ends beneath a red node. -/
theorem rebalances_or_redRed_iff {x : Int} {t : RBTree} (hv : t.noRedRed) (hx : ¬ t.contains x) :
    (t.insertRebalances x ∨ redRedRoot (t.ins x)) ↔ t.searchEndsUnderRed x := by
  induction t with
  | leaf => simp [insertRebalances, ins, redRedRoot, rootColor, searchEndsUnderRed]
  | node c l y r ihl ihr =>
    obtain ⟨hcc, hlv, hrv⟩ := hv
    simp only [contains, not_or] at hx
    obtain ⟨hxy, hxl, hxr⟩ := hx
    have ihl := ihl hlv hxl
    have ihr := ihr hrv hxr
    simp only [insertRebalances, ins, searchEndsUnderRed]
    rcases lt_trichotomy x y with hlt | heq | hgt
    · simp only [if_pos hlt]
      cases c
      · obtain ⟨hlb, hrb⟩ := hcc rfl
        rw [balance_red]
        simp only [isRotation_iff, redRedRoot, hrb, or_false, reduceCtorEq, false_and, or_false,
          true_and]
        constructor
        · rintro (h | h)
          · exact Or.inr (ihl.mp (Or.inl h))
          · rcases rootColor_ins_red h with h | h | h
            · exact Or.inl h
            · rw [hlb] at h; exact absurd h (by simp)
            · exact Or.inr (ihl.mp (Or.inl h))
        · rintro (rfl | h)
          · exact Or.inr rfl
          · rcases ihl.mpr h with h | h
            · exact Or.inl h
            · exact absurd h (not_redRedRoot_ins hlb)
      · simp only [isRotation_iff, not_redRedRoot_of_noRedRed hrv, or_false, true_and,
          reduceCtorEq, false_and, false_or]
        rw [iff_of_eq (eq_false (not_redRedRoot_balance_black _ _ _)), or_false]
        exact ihl
    · exact absurd heq hxy
    · simp only [if_neg (by omega : ¬ x < y), if_pos hgt]
      cases c
      · obtain ⟨hlb, hrb⟩ := hcc rfl
        rw [balance_red]
        simp only [isRotation_iff, redRedRoot, hlb, false_or, reduceCtorEq, false_and, or_false,
          true_and]
        constructor
        · rintro (h | h)
          · exact Or.inr (ihr.mp (Or.inl h))
          · rcases rootColor_ins_red h with h | h | h
            · exact Or.inl h
            · rw [hrb] at h; exact absurd h (by simp)
            · exact Or.inr (ihr.mp (Or.inl h))
        · rintro (rfl | h)
          · exact Or.inr rfl
          · rcases ihr.mpr h with h | h
            · exact Or.inl h
            · exact absurd h (not_redRedRoot_ins hrb)
      · simp only [isRotation_iff, not_redRedRoot_of_noRedRed hlv, false_or, true_and,
          reduceCtorEq, false_and, false_or]
        rw [iff_of_eq (eq_false (not_redRedRoot_balance_black _ _ _)), or_false]
        exact ihr

/-- Inserting a key the tree does not hold rebalances a red-black tree exactly when the search for
that key runs off the tree beneath a red node. -/
theorem insertRebalances_iff {x : Int} {t : RBTree} (hv : t.noRedRed)
    (hb : t.rootColor = .black) (hx : ¬ t.contains x) :
    t.insertRebalances x ↔ t.searchEndsUnderRed x := by
  rw [← rebalances_or_redRed_iff hv hx]
  exact (or_iff_left (not_redRedRoot_ins hb)).symm

end RBTree

/-! ## Special trees -/

/-- A red-black subtree of `[lo, hi]` at black height `n` that avoids `x` and along which `x`'s
search runs off beneath a red node. -/
def isSpecialSubtree (x lo hi : Int) (n : Nat) (t : RBTree) : Prop :=
  t.isRBSubtree lo hi n ∧ ¬ t.contains x ∧ t.searchEndsUnderRed x

/-- An `isSpecialSubtree` whose root is black. -/
def isSpecialTree (x lo hi : Int) (n : Nat) (t : RBTree) : Prop :=
  t.isRB lo hi n ∧ ¬ t.contains x ∧ t.searchEndsUnderRed x

/-! ## The generators -/

/-- The node `x`'s search runs off, keyed above `x`. -/
def genLeafAbove [Gen G] (x lo hi : Int) (h : max lo (x + 1) ≤ hi) : G RBTree := do
  let y ← chooseInt (max lo (x + 1)) hi h
  return .node .red .leaf y .leaf

/-- The node `x`'s search runs off, keyed below `x`. -/
def genLeafBelow [Gen G] (x lo hi : Int) (h : lo ≤ min hi (x - 1)) : G RBTree := do
  let y ← chooseInt lo (min hi (x - 1)) h
  return .node .red .leaf y .leaf

/-- A red root keyed above `x`, so `x`'s search descends into the left child, which `gs` makes
special; the right child is an ordinary black-rooted subtree. -/
def genRedAbove [Gen G] (x : Int) (n : Nat) (gs : Int → Int → G RBTree) (lo hi : Int)
    (h : max (lo + minKeys n) (x + 1) ≤ hi - minKeys n) : G RBTree := do
  let y ← chooseInt (max (lo + minKeys n) (x + 1)) (hi - minKeys n) h
  let a ← gs lo (y - 1)
  let b ← genBlack n (y + 1) hi
  return .node .red a y b

/-- A red root keyed below `x`, the mirror of `genRedAbove`. -/
def genRedBelow [Gen G] (x : Int) (n : Nat) (gs : Int → Int → G RBTree) (lo hi : Int)
    (h : lo + minKeys n ≤ min (hi - minKeys n) (x - 1)) : G RBTree := do
  let y ← chooseInt (lo + minKeys n) (min (hi - minKeys n) (x - 1)) h
  let a ← genBlack n lo (y - 1)
  let b ← gs (y + 1) hi
  return .node .red a y b

/-- Wraps a black-rooted special generator `gs` of black height `n` into one that may also produce
a red root. At black height `0` the only special subtree is the node the search runs off; above it
that node cannot occur, and a red root's child on `x`'s side carries the property instead. -/
def specialAnyOf [Gen G] (x : Int) (n : Nat) (gs : Int → Int → G RBTree) (lo hi : Int) : G RBTree :=
  if n = 0 then
    pickOf2 (genLeafAbove x lo hi) (genLeafBelow x lo hi)
  else
    pickOf3 (gs lo hi) (genRedAbove x n gs lo hi) (genRedBelow x n gs lo hi)

/-- A black root keyed above `x`, so `x`'s search descends into the left child, which is generated
special; the right child is an ordinary subtree. -/
def genBlackAbove [Gen G] (x : Int) (m : Nat) (gs : Int → Int → G RBTree) (lo hi : Int)
    (h : max (lo + minKeys m) (x + 1) ≤ hi - minKeys m) : G RBTree := do
  let y ← chooseInt (max (lo + minKeys m) (x + 1)) (hi - minKeys m) h
  let l ← specialAnyOf x m gs lo (y - 1)
  let r ← genAny m (y + 1) hi
  return .node .black l y r

/-- A black root keyed below `x`, the mirror of `genBlackAbove`. -/
def genBlackBelow [Gen G] (x : Int) (m : Nat) (gs : Int → Int → G RBTree) (lo hi : Int)
    (h : lo + minKeys m ≤ min (hi - minKeys m) (x - 1)) : G RBTree := do
  let y ← chooseInt (lo + minKeys m) (min (hi - minKeys m) (x - 1)) h
  let l ← genAny m lo (y - 1)
  let r ← specialAnyOf x m gs (y + 1) hi
  return .node .black l y r

/-- Generates the black-rooted red-black trees of black height `n` with keys in `[lo, hi]` into
which inserting `x` rebalances. A black-rooted tree of black height `0` is a leaf, and no leaf is
special, so there is nothing to generate: `default` is the empty distribution at `SPMF` and a
generator error at a running interpretation. -/
def genSpecialBlack [Gen G] (x : Int) : Nat → Int → Int → G RBTree
  | 0, _, _ => default
  | m + 1, lo, hi =>
    pickOf2 (genBlackAbove x m (fun a b => genSpecialBlack x m a b) lo hi)
      (genBlackBelow x m (fun a b => genSpecialBlack x m a b) lo hi)

/-! ## Support -/

theorem genLeafAbove_mem_support (x lo hi : Int) (h : max lo (x + 1) ≤ hi) (t : RBTree) :
    t ∈ SPMF.support (genLeafAbove x lo hi h)
      ↔ ∃ y, (max lo (x + 1) ≤ y ∧ y ≤ hi) ∧ t = .node .red .leaf y .leaf := by
  unfold genLeafAbove
  support_simp

theorem genLeafBelow_mem_support (x lo hi : Int) (h : lo ≤ min hi (x - 1)) (t : RBTree) :
    t ∈ SPMF.support (genLeafBelow x lo hi h)
      ↔ ∃ y, (lo ≤ y ∧ y ≤ min hi (x - 1)) ∧ t = .node .red .leaf y .leaf := by
  unfold genLeafBelow
  support_simp

theorem genRedAbove_mem_support {x : Int} {n : Nat} {gs : Int → Int → SPMF RBTree}
    (hgs : ∀ lo hi t, t ∈ SPMF.support (gs lo hi) ↔ isSpecialTree x lo hi n t)
    (lo hi : Int) (h : max (lo + minKeys n) (x + 1) ≤ hi - minKeys n) (t : RBTree) :
    t ∈ SPMF.support (genRedAbove x n gs lo hi h)
      ↔ ∃ y, (max (lo + minKeys n) (x + 1) ≤ y ∧ y ≤ hi - minKeys n) ∧
          ∃ a, isSpecialTree x lo (y - 1) n a ∧
            ∃ b, RBTree.isRB (y + 1) hi n b ∧ t = .node .red a y b := by
  unfold genRedAbove
  support_simp [hgs, genBlack_mem_support]

theorem genRedBelow_mem_support {x : Int} {n : Nat} {gs : Int → Int → SPMF RBTree}
    (hgs : ∀ lo hi t, t ∈ SPMF.support (gs lo hi) ↔ isSpecialTree x lo hi n t)
    (lo hi : Int) (h : lo + minKeys n ≤ min (hi - minKeys n) (x - 1)) (t : RBTree) :
    t ∈ SPMF.support (genRedBelow x n gs lo hi h)
      ↔ ∃ y, (lo + minKeys n ≤ y ∧ y ≤ min (hi - minKeys n) (x - 1)) ∧
          ∃ a, RBTree.isRB lo (y - 1) n a ∧
            ∃ b, isSpecialTree x (y + 1) hi n b ∧ t = .node .red a y b := by
  unfold genRedBelow
  support_simp [hgs, genBlack_mem_support]

theorem specialAnyOf_mem_support {x : Int} {n : Nat} {gs : Int → Int → SPMF RBTree}
    (hgs : ∀ lo hi t, t ∈ SPMF.support (gs lo hi) ↔ isSpecialTree x lo hi n t)
    (lo hi : Int) (t : RBTree) :
    t ∈ SPMF.support (specialAnyOf x n gs lo hi) ↔ isSpecialSubtree x lo hi n t := by
  have h0 : 0 ≤ (minKeys n : Int) := Int.natCast_nonneg _
  unfold specialAnyOf
  split <;> rename_i hn
  · subst hn
    rw [mem_support_pickOf2 (fun h => genLeafAbove_mem_support x lo hi h t)
      (fun h => genLeafBelow_mem_support x lo hi h t)
      (fun ⟨_, hy, _⟩ => by omega) (fun ⟨_, hy, _⟩ => by omega)]
    constructor
    · rintro (⟨y, ⟨hy1, hy2⟩, rfl⟩ | ⟨y, ⟨hy1, hy2⟩, rfl⟩) <;>
        simp only [max_le_iff, le_min_iff] at hy1 hy2
      · refine ⟨⟨⟨by omega, by omega, trivial, trivial⟩,
          ⟨fun _ => ⟨rfl, rfl⟩, trivial, trivial⟩, rfl, rfl⟩, ?_, ?_⟩
        · simp only [RBTree.contains, not_or]
          exact ⟨by omega, not_false, not_false⟩
        · simp only [RBTree.searchEndsUnderRed, if_pos (show x < y by omega)]
          exact Or.inl ⟨trivial, trivial⟩
      · refine ⟨⟨⟨by omega, by omega, trivial, trivial⟩,
          ⟨fun _ => ⟨rfl, rfl⟩, trivial, trivial⟩, rfl, rfl⟩, ?_, ?_⟩
        · simp only [RBTree.contains, not_or]
          exact ⟨by omega, not_false, not_false⟩
        · simp only [RBTree.searchEndsUnderRed, if_neg (show ¬ x < y by omega),
            if_pos (show y < x by omega)]
          exact Or.inl ⟨trivial, trivial⟩
    · rintro ⟨hsub, hx, hs⟩
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
        rcases lt_trichotomy x y with hlt | heq | hgt
        · exact Or.inl ⟨y, ⟨by omega, by omega⟩, rfl⟩
        · exact absurd heq hx.1
        · exact Or.inr ⟨y, ⟨by omega, by omega⟩, rfl⟩
      case _ => exact absurd hsub.2.2 not_false
  · rw [mem_support_pickOf3 (hgs lo hi t) (fun h => genRedAbove_mem_support hgs lo hi h t)
      (fun h => genRedBelow_mem_support hgs lo hi h t)
      (fun ⟨_, hy, _⟩ => by omega) (fun ⟨_, hy, _⟩ => by omega)]
    constructor
    · rintro (⟨⟨-, hsub⟩, hx, hs⟩
        | ⟨y, ⟨hy1, hy2⟩, a, ⟨⟨hac, habst, hanrr, habh⟩, hax, has⟩, b,
            ⟨hbc, hbbst, hbnrr, hbbh⟩, rfl⟩
        | ⟨y, ⟨hy1, hy2⟩, a, ⟨hac, habst, hanrr, habh⟩, b,
            ⟨⟨hbc, hbbst, hbnrr, hbbh⟩, hbx, hbs⟩, rfl⟩)
      · exact ⟨hsub, hx, hs⟩
      · simp only [max_le_iff] at hy1
        refine ⟨⟨⟨by omega, by omega, habst, hbbst⟩, ⟨fun _ => ⟨hac, hbc⟩, hanrr, hbnrr⟩,
          habh, hbbh⟩, ?_, ?_⟩
        · simp only [RBTree.contains, not_or]
          exact ⟨by omega, hax, fun hc => by have := RBTree.contains_bounds hbbst hc; omega⟩
        · simp only [RBTree.searchEndsUnderRed, if_pos (show x < y by omega)]
          exact Or.inr has
      · simp only [le_min_iff] at hy2
        refine ⟨⟨⟨by omega, by omega, habst, hbbst⟩, ⟨fun _ => ⟨hac, hbc⟩, hanrr, hbnrr⟩,
          habh, hbbh⟩, ?_, ?_⟩
        · simp only [RBTree.contains, not_or]
          exact ⟨by omega, fun hc => by have := RBTree.contains_bounds habst hc; omega, hbx⟩
        · simp only [RBTree.searchEndsUnderRed, if_neg (show ¬ x < y by omega),
            if_pos (show y < x by omega)]
          exact Or.inr hbs
    · rintro ⟨hsub, hx, hs⟩
      rcases t with _ | ⟨c, a, y, b⟩
      · exact absurd hs not_false
      cases c
      case _ =>
        obtain ⟨⟨hlo, hhi, habst, hbbst⟩, ⟨hcc, hanrr, hbnrr⟩, habh, hbbh⟩ := hsub
        obtain ⟨hac, hbc⟩ := hcc rfl
        simp only [RBTree.contains, not_or] at hx
        obtain ⟨hxy, hax, hbx⟩ := hx
        simp only [RBTree.searchEndsUnderRed] at hs
        have hl := RBTree.minKeys_le_width habst habh
        have hr := RBTree.minKeys_le_width hbbst hbbh
        rcases lt_trichotomy x y with hlt | heq | hgt
        · rw [if_pos hlt] at hs
          rcases hs with ⟨-, rfl⟩ | has
          · exact absurd habh hn
          · exact Or.inr (Or.inl ⟨y, ⟨by omega, by omega⟩,
              a, ⟨⟨hac, habst, hanrr, habh⟩, hax, has⟩, b, ⟨hbc, hbbst, hbnrr, hbbh⟩, rfl⟩)
        · exact absurd heq hxy
        · rw [if_neg (by omega), if_pos hgt] at hs
          rcases hs with ⟨-, rfl⟩ | hbs
          · exact absurd hbbh hn
          · exact Or.inr (Or.inr ⟨y, ⟨by omega, by omega⟩,
              a, ⟨hac, habst, hanrr, habh⟩, b, ⟨⟨hbc, hbbst, hbnrr, hbbh⟩, hbx, hbs⟩, rfl⟩)
      case _ => exact Or.inl ⟨⟨rfl, hsub⟩, hx, hs⟩

theorem genBlackAbove_mem_support {x : Int} {m : Nat} {gs : Int → Int → SPMF RBTree}
    (hgs : ∀ lo hi t, t ∈ SPMF.support (gs lo hi) ↔ isSpecialTree x lo hi m t)
    (lo hi : Int) (h : max (lo + minKeys m) (x + 1) ≤ hi - minKeys m) (t : RBTree) :
    t ∈ SPMF.support (genBlackAbove x m gs lo hi h)
      ↔ ∃ y, (max (lo + minKeys m) (x + 1) ≤ y ∧ y ≤ hi - minKeys m) ∧
          ∃ l, isSpecialSubtree x lo (y - 1) m l ∧
            ∃ r, RBTree.isRBSubtree (y + 1) hi m r ∧ t = .node .black l y r := by
  unfold genBlackAbove
  support_simp [specialAnyOf_mem_support hgs, genAny_mem_support]

theorem genBlackBelow_mem_support {x : Int} {m : Nat} {gs : Int → Int → SPMF RBTree}
    (hgs : ∀ lo hi t, t ∈ SPMF.support (gs lo hi) ↔ isSpecialTree x lo hi m t)
    (lo hi : Int) (h : lo + minKeys m ≤ min (hi - minKeys m) (x - 1)) (t : RBTree) :
    t ∈ SPMF.support (genBlackBelow x m gs lo hi h)
      ↔ ∃ y, (lo + minKeys m ≤ y ∧ y ≤ min (hi - minKeys m) (x - 1)) ∧
          ∃ l, RBTree.isRBSubtree lo (y - 1) m l ∧
            ∃ r, isSpecialSubtree x (y + 1) hi m r ∧ t = .node .black l y r := by
  unfold genBlackBelow
  support_simp [specialAnyOf_mem_support hgs, genAny_mem_support]

theorem genSpecialBlack_mem_support (x : Int) (n : Nat) (lo hi : Int) (t : RBTree) :
    t ∈ SPMF.support (genSpecialBlack x n lo hi) ↔ isSpecialTree x lo hi n t := by
  induction n generalizing lo hi t with
  | zero =>
    rw [genSpecialBlack]
    refine ⟨fun h => absurd h not_mem_support_default, fun ht => ?_⟩
    obtain ⟨hrb, -, hs⟩ := ht
    rw [RBTree.isRB_zero_iff] at hrb
    subst hrb
    exact absurd hs not_false
  | succ m ih =>
    have h0 : 0 ≤ (minKeys m : Int) := Int.natCast_nonneg _
    have hgs : ∀ lo hi t, t ∈ SPMF.support ((fun a b => genSpecialBlack x m a b) lo hi)
        ↔ isSpecialTree x lo hi m t := fun lo hi t => ih lo hi t
    rw [genSpecialBlack, mem_support_pickOf2 (fun h => genBlackAbove_mem_support hgs lo hi h t)
      (fun h => genBlackBelow_mem_support hgs lo hi h t)
      (fun ⟨_, hy, _⟩ => by omega) (fun ⟨_, hy, _⟩ => by omega)]
    constructor
    · rintro (⟨y, ⟨hy1, hy2⟩, l, ⟨⟨hlbst, hlnrr, hlbh⟩, hlx, hls⟩, r,
          ⟨hrbst, hrnrr, hrbh⟩, rfl⟩
        | ⟨y, ⟨hy1, hy2⟩, l, ⟨hlbst, hlnrr, hlbh⟩, r,
          ⟨⟨hrbst, hrnrr, hrbh⟩, hrx, hrs⟩, rfl⟩)
      · simp only [max_le_iff] at hy1
        refine ⟨⟨rfl, ⟨by omega, by omega, hlbst, hrbst⟩,
          ⟨fun h => Color.noConfusion h, hlnrr, hrnrr⟩, hlbh, hrbh⟩, ?_, ?_⟩
        · simp only [RBTree.contains, not_or]
          exact ⟨by omega, hlx, fun hc => by have := RBTree.contains_bounds hrbst hc; omega⟩
        · simp only [RBTree.searchEndsUnderRed, if_pos (show x < y by omega)]
          exact Or.inr hls
      · simp only [le_min_iff] at hy2
        refine ⟨⟨rfl, ⟨by omega, by omega, hlbst, hrbst⟩,
          ⟨fun h => Color.noConfusion h, hlnrr, hrnrr⟩, hlbh, hrbh⟩, ?_, ?_⟩
        · simp only [RBTree.contains, not_or]
          exact ⟨by omega, fun hc => by have := RBTree.contains_bounds hlbst hc; omega, hrx⟩
        · simp only [RBTree.searchEndsUnderRed, if_neg (show ¬ x < y by omega),
            if_pos (show y < x by omega)]
          exact Or.inr hrs
    · rintro ⟨hrb, hx, hs⟩
      rcases t with _ | ⟨c, l, y, r⟩
      · exact absurd hs not_false
      cases c
      case _ => exact absurd hrb.1 (by simp [RBTree.rootColor])
      case _ =>
        obtain ⟨-, ⟨hlo, hhi, hlbst, hrbst⟩, ⟨-, hlnrr, hrnrr⟩, hlbh, hrbh⟩ := hrb
        simp only [RBTree.contains, not_or] at hx
        obtain ⟨hxy, hlx, hrx⟩ := hx
        simp only [RBTree.searchEndsUnderRed] at hs
        have hl := RBTree.minKeys_le_width hlbst hlbh
        have hr := RBTree.minKeys_le_width hrbst hrbh
        rcases lt_trichotomy x y with hlt | heq | hgt
        · rw [if_pos hlt] at hs
          rcases hs with ⟨hcr, -⟩ | hls
          · exact absurd hcr (by simp)
          · exact Or.inl ⟨y, ⟨by omega, by omega⟩, l,
              ⟨⟨hlbst, hlnrr, hlbh⟩, hlx, hls⟩, r, ⟨hrbst, hrnrr, hrbh⟩, rfl⟩
        · exact absurd heq hxy
        · rw [if_neg (by omega), if_pos hgt] at hs
          rcases hs with ⟨hcr, -⟩ | hrs
          · exact absurd hcr (by simp)
          · exact Or.inr ⟨y, ⟨by omega, by omega⟩, l, ⟨hlbst, hlnrr, hlbh⟩, r,
              ⟨⟨hrbst, hrnrr, hrbh⟩, hrx, hrs⟩, rfl⟩

theorem genSpecialBlack.sound_complete :
    IsSoundAndComplete (genSpecialBlack x n lo hi)
      (fun t => t.isRB lo hi n ∧ ¬ t.contains x ∧ t.insertRebalances x) := by
  intro t
  rw [genSpecialBlack_mem_support]
  constructor
  · rintro ⟨hrb, hx, hs⟩
    exact ⟨hrb, hx, (RBTree.insertRebalances_iff hrb.2.2.1 hrb.1 hx).mpr hs⟩
  · rintro ⟨hrb, hx, hr⟩
    exact ⟨hrb, hx, (RBTree.insertRebalances_iff hrb.2.2.1 hrb.1 hx).mp hr⟩

end RedBlackTree
