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
# Generating Red-Black Trees of a Given Size

`genBlackSized n s lo hi` generates the red-black trees of black height `n` that hold exactly `s`
keys, and `genBlackUpTo N lo hi` unions those over every `(n, s)` a tree of at most `N` keys can
have. Indexing by an exact size makes the interval arithmetic trivial — a node whose children take
`sl` and `sr` keys has its pivot in `[lo + sl, hi - sr]` — and turns "at most `N` nodes" into a
finite union rather than a filter.
-/

namespace RedBlackTree

/-- The most keys a black-rooted red-black subtree of black height `n` can hold, `4 ^ n - 1`,
written so that `omega` sees the recurrence. -/
def maxKeysBlack : Nat → Nat
  | 0 => 0
  | n + 1 => 4 * maxKeysBlack n + 3

/-- The most keys a red-black subtree of black height `n` can hold when its root may be red,
`2 * 4 ^ n - 1`: a red root over two black-rooted subtrees of black height `n`. -/
def maxKeysAny (n : Nat) : Nat := 2 * maxKeysBlack n + 1

namespace RBTree

/-- Black height is a coarser measure than size: `n ≤ 2 ^ n - 1`. -/
theorem le_minKeys (n : Nat) : n ≤ minKeys n := by
  induction n with
  | zero => simp [minKeys]
  | succ m ih => simp only [minKeys]; omega

theorem minKeys_le_maxKeysBlack (n : Nat) : minKeys n ≤ maxKeysBlack n := by
  induction n with
  | zero => simp [minKeys, maxKeysBlack]
  | succ m ih => simp only [minKeys, maxKeysBlack]; omega

theorem size_le_maxKeys {n : Nat} {t : RBTree} (hnrr : t.noRedRed) (hbh : t.hasBlackHeight n) :
    t.size ≤ maxKeysAny n ∧ (t.rootColor = .black → t.size ≤ maxKeysBlack n) := by
  induction t generalizing n with
  | leaf => subst hbh; simp [size, maxKeysAny, maxKeysBlack]
  | node c l y r ihl ihr =>
    obtain ⟨hcc, hlv, hrv⟩ := hnrr
    cases c with
    | red =>
      obtain ⟨hl, hr⟩ := hbh
      obtain ⟨hlb, hrb⟩ := hcc rfl
      have hl' := (ihl hlv hl).2 hlb
      have hr' := (ihr hrv hr).2 hrb
      refine ⟨?_, fun h => absurd h (by simp [rootColor])⟩
      simp only [size, maxKeysAny]
      omega
    | black =>
      cases n with
      | zero => exact absurd hbh not_false
      | succ m =>
        obtain ⟨hl, hr⟩ := hbh
        have hl' := (ihl hlv hl).1
        have hr' := (ihr hrv hr).1
        simp only [maxKeysAny] at hl' hr' ⊢
        simp only [size, maxKeysBlack]
        exact ⟨by omega, fun _ => by omega⟩

theorem size_le_maxKeysAny {n : Nat} {t : RBTree} (h : t.isRBSubtree lo hi n) :
    t.size ≤ maxKeysAny n := (size_le_maxKeys h.2.1 h.2.2).1

theorem size_le_maxKeysBlack {n : Nat} {t : RBTree} (h : t.isRB lo hi n) :
    t.size ≤ maxKeysBlack n := (size_le_maxKeys h.2.2.1 h.2.2.2).2 h.1

end RBTree

/-! ## One node -/

/-- The least size the left child of a size-`s` node can take: its own minimum `al`, what the right
child's maximum `br` leaves it, and what the pivot's lower bound `plo` and the right child's
reserve `dr` force it to hold. -/
def splitLo (al br dr : Nat) (plo hi : Int) (s : Nat) : Nat :=
  max (max al (s - 1 - br)) (plo - hi + ((s - 1 : Nat) : Int) + dr).toNat

/-- The greatest size the left child of a size-`s` node can take: its own maximum `bl`, what the
right child's minimum `ar` leaves it, and what the pivot's upper bound `phi` and the left child's
reserve `dl` allow below it. -/
def splitHi (bl ar dl : Nat) (lo phi : Int) (s : Nat) : Nat :=
  min (min bl (s - 1 - ar)) (phi - lo - dl).toNat

/-- `[lo, hi]` has room for a node of size `s` whose pivot lies in `[plo, phi]` and whose children
take sizes in `[al, bl]` and `[ar, br]`. `dl` and `dr` are values each child's interval must hold
*beyond* its own keys — one, for a child that must avoid a key inside its interval. -/
def NodeRoom (al bl ar br dl dr : Nat) (plo phi : Int) (s : Nat) (lo hi : Int) : Prop :=
  1 ≤ s ∧ plo ≤ phi ∧ lo + dl ≤ phi ∧ (s : Int) - 1 + dl + dr ≤ hi - lo ∧
    splitLo al br dr plo hi s ≤ splitHi bl ar dl lo phi s

instance : Decidable (NodeRoom al bl ar br dl dr plo phi s lo hi) := by
  unfold NodeRoom; infer_instance

/-- One node of a size-indexed generator: the `s - 1` keys below the pivot are split between a left
child of size `sl ∈ [al, bl]` and a right child of size `s - 1 - sl ∈ [ar, br]`, and the pivot is
drawn from `[plo, phi]` and from the room that split leaves it. Both draws range over exactly the
values that yield a tree, so no branch is wasted. -/
def genNodeSized [Gen G] (c : Color) (al bl ar br dl dr : Nat) (plo phi : Int)
    (gl gr : Nat → Int → Int → G RBTree) (s : Nat) (lo hi : Int) : G RBTree :=
  if h : NodeRoom al bl ar br dl dr plo phi s lo hi then do
    let sl ← chooseNat (splitLo al br dr plo hi s) (splitHi bl ar dl lo phi s) h.2.2.2.2
    if hy : max (lo + sl + dl) plo ≤ min (hi - ((s - 1 - sl : Nat) : Int) - dr) phi then do
      let y ← chooseInt (max (lo + sl + dl) plo)
        (min (hi - ((s - 1 - sl : Nat) : Int) - dr) phi) hy
      let l ← gl sl lo (y - 1)
      let r ← gr (s - 1 - sl) (y + 1) hi
      return .node c l y r
    else default
  else default

/-- The children of a node fix the room it needs: their sizes, the room their intervals must leave
and the pivot between them determine every conjunct of `NodeRoom`. This is what lets a branch that
builds such a node be guarded by `NodeRoom` without the guard ever excluding a tree. -/
theorem split_bounds {al bl ar br dl dr : Nat} {plo phi : Int}
    {Pl Pr : Nat → Int → Int → RBTree → Prop} {s : Nat} {lo hi : Int}
    (hl : ∀ sl a b u, Pl sl a b u → u.size = sl ∧ al ≤ sl ∧ sl ≤ bl)
    (hr : ∀ sr a b u, Pr sr a b u → u.size = sr ∧ ar ≤ sr ∧ sr ≤ br)
    (hwl : ∀ sl y u, plo ≤ y → Pl sl lo (y - 1) u → sl + dl ≤ (y - lo).toNat)
    (hwr : ∀ sr y u, y ≤ phi → Pr sr (y + 1) hi u → sr + dr ≤ (hi - y).toNat)
    {y : Int} {l r : RBTree} (hPl : Pl l.size lo (y - 1) l) (hPr : Pr r.size (y + 1) hi r)
    (hsize : l.size + r.size + 1 = s) (hylo : plo ≤ y) (hyhi : y ≤ phi)
    (hlo : lo ≤ y) (hhi : y ≤ hi) :
    (splitLo al br dr plo hi s ≤ l.size ∧ l.size ≤ splitHi bl ar dl lo phi s) ∧
      r.size = s - 1 - l.size ∧ NodeRoom al bl ar br dl dr plo phi s lo hi := by
  obtain ⟨-, hal, hbl⟩ := hl _ _ _ _ hPl
  obtain ⟨-, har, hbr⟩ := hr _ _ _ _ hPr
  have hwl' := hwl _ _ _ hylo hPl
  have hwr' := hwr _ _ _ hyhi hPr
  have hA : splitLo al br dr plo hi s ≤ l.size := by simp only [splitLo]; omega
  have hB : l.size ≤ splitHi bl ar dl lo phi s := by simp only [splitHi]; omega
  exact ⟨⟨hA, hB⟩, by omega, by omega, by omega, by omega, by omega, hA.trans hB⟩

/-- `NodeRoom` read off a node this generator could have produced. -/
theorem nodeRoom_of_support {al bl ar br dl dr : Nat} {plo phi : Int}
    {Pl Pr : Nat → Int → Int → RBTree → Prop} {s : Nat} {lo hi : Int} {c : Color} {t : RBTree}
    (hl : ∀ sl a b u, Pl sl a b u → u.size = sl ∧ al ≤ sl ∧ sl ≤ bl)
    (hr : ∀ sr a b u, Pr sr a b u → u.size = sr ∧ ar ≤ sr ∧ sr ≤ br)
    (hwl : ∀ sl y u, plo ≤ y → Pl sl lo (y - 1) u → sl + dl ≤ (y - lo).toNat)
    (hwr : ∀ sr y u, y ≤ phi → Pr sr (y + 1) hi u → sr + dr ≤ (hi - y).toNat)
    (h : ∃ y l r, lo ≤ y ∧ y ≤ hi ∧ plo ≤ y ∧ y ≤ phi ∧
          Pl l.size lo (y - 1) l ∧ Pr r.size (y + 1) hi r ∧
          l.size + r.size + 1 = s ∧ t = .node c l y r) :
    NodeRoom al bl ar br dl dr plo phi s lo hi := by
  obtain ⟨y, l, r, hlo, hhi, hylo, hyhi, hPl, hPr, hsize, -⟩ := h
  exact (split_bounds hl hr hwl hwr hPl hPr hsize hylo hyhi hlo hhi).2.2

/-- The support of one node: the size split and the pivot's room are recovered from the children,
so neither the child size bounds nor `NodeRoom` appear on the right. -/
theorem genNodeSized_mem_support {c : Color} {al bl ar br dl dr : Nat} {plo phi : Int}
    {gl gr : Nat → Int → Int → SPMF RBTree} {Pl Pr : Nat → Int → Int → RBTree → Prop}
    (hgl : ∀ sl a b u, u ∈ SPMF.support (gl sl a b) ↔ Pl sl a b u)
    (hgr : ∀ sr a b u, u ∈ SPMF.support (gr sr a b) ↔ Pr sr a b u)
    (hl : ∀ sl a b u, Pl sl a b u → u.size = sl ∧ al ≤ sl ∧ sl ≤ bl)
    (hr : ∀ sr a b u, Pr sr a b u → u.size = sr ∧ ar ≤ sr ∧ sr ≤ br)
    (hwl : ∀ sl y u, plo ≤ y → Pl sl lo (y - 1) u → sl + dl ≤ (y - lo).toNat)
    (hwr : ∀ sr y u, y ≤ phi → Pr sr (y + 1) hi u → sr + dr ≤ (hi - y).toNat)
    (s : Nat) (t : RBTree) :
    t ∈ SPMF.support (genNodeSized c al bl ar br dl dr plo phi gl gr s lo hi)
      ↔ ∃ y l r, lo ≤ y ∧ y ≤ hi ∧ plo ≤ y ∧ y ≤ phi ∧
          Pl l.size lo (y - 1) l ∧ Pr r.size (y + 1) hi r ∧
          l.size + r.size + 1 = s ∧ t = .node c l y r := by
  unfold genNodeSized
  split <;> rename_i hroom
  · support_simp [hgl, hgr, mem_support_default, exists_false, or_false]
    constructor
    · rintro ⟨sl, ⟨hs1, hs2⟩, hy, y, ⟨hy1, hy2⟩, l, hPl, r, hPr, rfl⟩
      obtain ⟨rfl, hal, hbl⟩ := hl _ _ _ _ hPl
      obtain ⟨hrs, har, hbr⟩ := hr _ _ _ _ hPr
      simp only [splitHi, le_min_iff] at hs2
      simp only [le_min_iff] at hy2
      simp only [max_le_iff] at hy1
      have hpos : 1 ≤ s := hroom.1
      exact ⟨y, l, r, by omega, by omega, hy1.2, hy2.2, hPl, by rw [hrs]; exact hPr,
        by omega, rfl⟩
    · rintro ⟨y, l, r, hlo, hhi, hylo, hyhi, hPl, hPr, hsize, rfl⟩
      obtain ⟨⟨h1, h2⟩, hrs, -⟩ := split_bounds hl hr hwl hwr hPl hPr hsize hylo hyhi hlo hhi
      have hwl' := hwl _ _ _ hylo hPl
      have hwr' := hwr _ _ _ hyhi hPr
      refine ⟨l.size, ⟨h1, h2⟩, ?_, y, ⟨by omega, ?_⟩, l, hPl, r, ?_, rfl⟩
      · rw [← hrs]; omega
      · rw [← hrs]; omega
      · rw [← hrs]; exact hPr
  · rw [mem_support_default]
    exact ⟨False.elim, fun h => absurd (nodeRoom_of_support hl hr hwl hwr h) hroom⟩

/-! ## The generators -/

/-- Wraps a black-rooted size-indexed generator `g` of black height `n` into one that may also
produce a red root, whose two children `g` supplies at sizes summing to `s - 1`. A red root needs
one more key than a black one at either end of the size range, so which branches can produce
anything is decided before the choice, not inside it. -/
def anyOfSized [Gen G] (n : Nat) (g : Nat → Int → Int → G RBTree) (s : Nat) (lo hi : Int) :
    G RBTree :=
  pickOf2 (p := minKeys n ≤ s ∧ s ≤ maxKeysBlack n ∧ s ≤ (hi - lo + 1).toNat)
    (q := 2 * minKeys n + 1 ≤ s ∧ s ≤ maxKeysAny n ∧ s ≤ (hi - lo + 1).toNat)
    (fun _ => g s lo hi)
    (fun _ => genNodeSized .red (minKeys n) (maxKeysBlack n) (minKeys n) (maxKeysBlack n) 0 0
      lo hi g g s lo hi)

/-- Generates the black-rooted red-black trees of black height `n` that hold exactly `s` keys, from
`[lo, hi]`. -/
def genBlackSized [Gen G] : (n s : Nat) → (lo hi : Int) → G RBTree
  | 0, s, _, _ => if s = 0 then pure .leaf else default
  | m + 1, s, lo, hi =>
      genNodeSized .black (minKeys m) (maxKeysAny m) (minKeys m) (maxKeysAny m) 0 0 lo hi
        (fun s' a b => anyOfSized m (fun s'' a' b' => genBlackSized m s'' a' b') s' a b)
        (fun s' a b => anyOfSized m (fun s'' a' b' => genBlackSized m s'' a' b') s' a b)
        s lo hi

/-- Generates the red-black trees of black height `n` that hold exactly `s` keys, red root
allowed. -/
def genAnySized [Gen G] (n s : Nat) (lo hi : Int) : G RBTree :=
  anyOfSized n (fun s' a b => genBlackSized n s' a b) s lo hi

/-! ## Support -/

theorem isRB_size_bounds {n : Nat} (sl : Nat) (a b : Int) (u : RBTree) :
    (u.isRB a b n ∧ u.size = sl) → u.size = sl ∧ minKeys n ≤ sl ∧ sl ≤ maxKeysBlack n := by
  rintro ⟨hrb, rfl⟩
  exact ⟨rfl, RBTree.minKeys_le_size hrb.2.2.2, RBTree.size_le_maxKeysBlack hrb⟩

theorem isRBSubtree_size_bounds {n : Nat} (sl : Nat) (a b : Int) (u : RBTree) :
    (u.isRBSubtree a b n ∧ u.size = sl) → u.size = sl ∧ minKeys n ≤ sl ∧ sl ≤ maxKeysAny n := by
  rintro ⟨hsub, rfl⟩
  exact ⟨rfl, RBTree.minKeys_le_size hsub.2.2, RBTree.size_le_maxKeysAny hsub⟩

/-- A child that may use its whole interval reserves nothing beyond its own keys. -/
theorem isRB_width_left {n : Nat} {lo plo : Int} (sl : Nat) (y : Int) (u : RBTree) (_hy : plo ≤ y)
    (h : u.isRB lo (y - 1) n ∧ u.size = sl) : sl + 0 ≤ (y - lo).toNat := by
  have := RBTree.size_le_of_isBST h.1.2.1
  omega

theorem isRB_width_right {n : Nat} {hi phi : Int} (sr : Nat) (y : Int) (u : RBTree) (_hy : y ≤ phi)
    (h : u.isRB (y + 1) hi n ∧ u.size = sr) : sr + 0 ≤ (hi - y).toNat := by
  have := RBTree.size_le_of_isBST h.1.2.1
  omega

theorem isRBSubtree_width_left {n : Nat} {lo plo : Int} (sl : Nat) (y : Int) (u : RBTree)
    (_hy : plo ≤ y) (h : u.isRBSubtree lo (y - 1) n ∧ u.size = sl) : sl + 0 ≤ (y - lo).toNat := by
  have := RBTree.size_le_of_isBST h.1.1
  omega

theorem isRBSubtree_width_right {n : Nat} {hi phi : Int} (sr : Nat) (y : Int) (u : RBTree)
    (_hy : y ≤ phi) (h : u.isRBSubtree (y + 1) hi n ∧ u.size = sr) : sr + 0 ≤ (hi - y).toNat := by
  have := RBTree.size_le_of_isBST h.1.1
  omega

theorem anyOfSized_mem_support {n : Nat} {g : Nat → Int → Int → SPMF RBTree}
    (hg : ∀ s lo hi t, t ∈ SPMF.support (g s lo hi) ↔ t.isRB lo hi n ∧ t.size = s)
    (s : Nat) (lo hi : Int) (t : RBTree) :
    t ∈ SPMF.support (anyOfSized n g s lo hi) ↔ t.isRBSubtree lo hi n ∧ t.size = s := by
  unfold anyOfSized
  rw [mem_support_pickOf2 (fun _ => hg s lo hi t)
    (fun _ => genNodeSized_mem_support (Pl := fun sl a b u => u.isRB a b n ∧ u.size = sl)
      (Pr := fun sr a b u => u.isRB a b n ∧ u.size = sr)
      (fun sl a b u => hg sl a b u) (fun sr a b u => hg sr a b u)
      isRB_size_bounds isRB_size_bounds isRB_width_left isRB_width_right s t)
    (by
      rintro ⟨hrb, rfl⟩
      exact ⟨RBTree.minKeys_le_size hrb.2.2.2, RBTree.size_le_maxKeysBlack hrb,
        RBTree.size_le_of_isBST hrb.2.1⟩)
    (by
      rintro ⟨y, l, r, hlo, hhi, -, -, ⟨hlrb, -⟩, ⟨hrrb, -⟩, hsize, -⟩
      have hl1 := isRB_size_bounds l.size lo (y - 1) l ⟨hlrb, rfl⟩
      have hr1 := isRB_size_bounds r.size (y + 1) hi r ⟨hrrb, rfl⟩
      have hl2 := RBTree.size_le_of_isBST hlrb.2.1
      have hr2 := RBTree.size_le_of_isBST hrrb.2.1
      simp only [maxKeysAny]
      omega)]
  constructor
  · rintro (⟨hrb, hsz⟩ | ⟨y, l, r, hlo, hhi, -, -, ⟨hlrb, -⟩, ⟨hrrb, -⟩, hsize, rfl⟩)
    · exact ⟨hrb.2, hsz⟩
    · obtain ⟨hlc, hlbst, hlnrr, hlbh⟩ := hlrb
      obtain ⟨hrc, hrbst, hrnrr, hrbh⟩ := hrrb
      exact ⟨⟨⟨hlo, hhi, hlbst, hrbst⟩, ⟨fun _ => ⟨hlc, hrc⟩, hlnrr, hrnrr⟩, hlbh, hrbh⟩,
        by simpa [RBTree.size] using hsize⟩
  · rintro ⟨hsub, hsz⟩
    rcases t with _ | ⟨c, l, y, r⟩
    · exact Or.inl ⟨⟨rfl, hsub⟩, hsz⟩
    cases c
    case _ =>
      obtain ⟨⟨hlo, hhi, hlbst, hrbst⟩, ⟨hcc, hlnrr, hrnrr⟩, hlbh, hrbh⟩ := hsub
      obtain ⟨hlc, hrc⟩ := hcc rfl
      exact Or.inr ⟨y, l, r, hlo, hhi, hlo, hhi, ⟨⟨hlc, hlbst, hlnrr, hlbh⟩, rfl⟩,
        ⟨⟨hrc, hrbst, hrnrr, hrbh⟩, rfl⟩, by simpa [RBTree.size] using hsz, rfl⟩
    case _ => exact Or.inl ⟨⟨rfl, hsub⟩, hsz⟩

theorem genBlackSized_mem_support (n s : Nat) (lo hi : Int) (t : RBTree) :
    t ∈ SPMF.support (genBlackSized n s lo hi) ↔ t.isRB lo hi n ∧ t.size = s := by
  induction n generalizing s lo hi t with
  | zero =>
    rw [genBlackSized]
    split <;> rename_i hs
    · subst hs
      support_simp [RBTree.isRB_zero_iff]
      constructor
      · rintro rfl; exact ⟨rfl, rfl⟩
      · rintro ⟨rfl, -⟩; rfl
    · rw [mem_support_default]
      refine ⟨False.elim, ?_⟩
      rintro ⟨hrb, hsz⟩
      rw [RBTree.isRB_zero_iff] at hrb
      subst hrb
      exact absurd hsz.symm hs
  | succ m ih =>
    have hany : ∀ s' a b u,
        u ∈ SPMF.support (anyOfSized m (fun s'' a' b' => genBlackSized m s'' a' b') s' a b)
          ↔ u.isRBSubtree a b m ∧ u.size = s' :=
      fun s' a b u => anyOfSized_mem_support (fun s'' a' b' u' => ih s'' a' b' u') s' a b u
    rw [genBlackSized,
      genNodeSized_mem_support (Pl := fun sl a b u => u.isRBSubtree a b m ∧ u.size = sl)
        (Pr := fun sr a b u => u.isRBSubtree a b m ∧ u.size = sr) hany hany
        isRBSubtree_size_bounds isRBSubtree_size_bounds
        isRBSubtree_width_left isRBSubtree_width_right s t]
    constructor
    · rintro ⟨y, l, r, hlo, hhi, -, -, ⟨hlsub, -⟩, ⟨hrsub, -⟩, hsize, rfl⟩
      exact ⟨⟨rfl, ⟨hlo, hhi, hlsub.1, hrsub.1⟩,
        ⟨fun h => Color.noConfusion h, hlsub.2.1, hrsub.2.1⟩, hlsub.2.2, hrsub.2.2⟩,
        by simpa [RBTree.size] using hsize⟩
    · rintro ⟨hrb, hsz⟩
      rcases t with _ | ⟨c, l, y, r⟩
      · exact absurd hrb.2.2.2 (by simp [RBTree.hasBlackHeight])
      cases c
      case _ => exact absurd hrb.1 (by simp [RBTree.rootColor])
      case _ =>
        obtain ⟨-, ⟨hlo, hhi, hlbst, hrbst⟩, ⟨-, hlnrr, hrnrr⟩, hlbh, hrbh⟩ := hrb
        exact ⟨y, l, r, hlo, hhi, hlo, hhi, ⟨⟨hlbst, hlnrr, hlbh⟩, rfl⟩,
          ⟨⟨hrbst, hrnrr, hrbh⟩, rfl⟩, by simpa [RBTree.size] using hsz, rfl⟩

theorem genAnySized_mem_support (n s : Nat) (lo hi : Int) (t : RBTree) :
    t ∈ SPMF.support (genAnySized n s lo hi) ↔ t.isRBSubtree lo hi n ∧ t.size = s :=
  anyOfSized_mem_support (fun s' a b u => genBlackSized_mem_support n s' a b u) s lo hi t

theorem genBlackSized.sound_complete :
    IsSoundAndComplete (genBlackSized n s lo hi) (fun t => t.isRB lo hi n ∧ t.size = s) :=
  genBlackSized_mem_support n s lo hi

theorem genAnySized.sound_complete :
    IsSoundAndComplete (genAnySized n s lo hi) (fun t => t.isRBSubtree lo hi n ∧ t.size = s) :=
  genAnySized_mem_support n s lo hi

/-! ## At most `N` keys -/

/-- Every `(black height, size)` pair within `N`. Black height never exceeds size
(`RBTree.le_minKeys`), so `N` bounds both coordinates. -/
def indexPairs (N : Nat) : List (Nat × Nat) :=
  (List.range (N + 1)).flatMap fun s => (List.range (N + 1)).map fun n => (n, s)

theorem mem_indexPairs {N n s : Nat} : (n, s) ∈ indexPairs N ↔ n ≤ N ∧ s ≤ N := by
  simp only [indexPairs, List.mem_flatMap, List.mem_map, List.mem_range, Prod.mk.injEq]
  constructor
  · rintro ⟨s', hs', n', hn', rfl, rfl⟩; omega
  · rintro ⟨hn, hs⟩; exact ⟨s, by omega, n, by omega, rfl, rfl⟩

/-- The `(black height, size)` pairs a black-rooted red-black tree of at most `N` keys drawn from
`[lo, hi]` can have. -/
def blackIndices (N : Nat) (lo hi : Int) : List (Nat × Nat) :=
  (indexPairs N).filter fun p =>
    decide (minKeys p.1 ≤ p.2 ∧ p.2 ≤ maxKeysBlack p.1 ∧ p.2 ≤ (hi - lo + 1).toNat)

theorem mem_blackIndices {N n s : Nat} {lo hi : Int} :
    (n, s) ∈ blackIndices N lo hi ↔
      (n ≤ N ∧ s ≤ N) ∧ minKeys n ≤ s ∧ s ≤ maxKeysBlack n ∧ s ≤ (hi - lo + 1).toNat := by
  simp [blackIndices, List.mem_filter, mem_indexPairs]

theorem mem_blackIndices_of_isRB {N n : Nat} {lo hi : Int} {t : RBTree} (hrb : t.isRB lo hi n)
    (hsz : t.size ≤ N) : (n, t.size) ∈ blackIndices N lo hi := by
  rw [mem_blackIndices]
  have h1 := RBTree.le_minKeys n
  have h2 := RBTree.minKeys_le_size hrb.2.2.2
  exact ⟨⟨by omega, hsz⟩, h2, RBTree.size_le_maxKeysBlack hrb, RBTree.size_le_of_isBST hrb.2.1⟩

/-- Generates the red-black trees with keys in `[lo, hi]` that hold at most `N` keys — the paper's
bound on red-black trees — as the union of `genBlackSized` over every `(black height, size)` pair
such a tree can have. Black height and size together pin a tree down, so the union is disjoint.

**"Every branch can produce something" is believed but not proved, which is why there is no
`terminates` here.** `mem_blackIndices` is a necessary condition on a tree's `(black height, size)`;
that it is also sufficient — that some black-rooted tree of black height `n` holds exactly `s` keys
in `[lo, hi]` whenever `minKeys n ≤ s ≤ maxKeysBlack n` and `s` fits the interval — is the missing
lemma, and `IsAlmostSurelyTerminating` needs it twice over: once for the branches of this union, and
once inside `genNodeSized`, to know that every size split `sl ∈ [splitLo, splitHi]` and every pivot
in the drawn window leaves *both* children realizable. Unlike the B-tree guards, which are known to
admit empty branches (`BTree.sizeIndices`), no counterexample is known here; `BasaltTest/IO.lean`
records the sweep that looked. -/
def genBlackUpTo [Gen G] (N : Nat) (lo hi : Int) : G RBTree :=
  if h : blackIndices N lo hi ≠ [] then
    oneOf ((blackIndices N lo hi).map fun p => fun (_ : Unit) => genBlackSized p.1 p.2 lo hi)
      (by simpa using h)
  else default

theorem genBlackUpTo_mem_support (N : Nat) (lo hi : Int) (t : RBTree) :
    t ∈ SPMF.support (genBlackUpTo N lo hi) ↔ (∃ n, t.isRB lo hi n) ∧ t.size ≤ N := by
  unfold genBlackUpTo
  split <;> rename_i hne
  · rw [SPMF.mem_support_oneOf_iff]
    simp only [List.mem_map]
    constructor
    · rintro ⟨gg, ⟨⟨n, s⟩, hmem, rfl⟩, hsupp⟩
      rw [genBlackSized_mem_support] at hsupp
      obtain ⟨hrb, rfl⟩ := hsupp
      exact ⟨⟨n, hrb⟩, (mem_blackIndices.mp hmem).1.2⟩
    · rintro ⟨⟨n, hrb⟩, hsz⟩
      exact ⟨_, ⟨(n, t.size), mem_blackIndices_of_isRB hrb hsz, rfl⟩,
        (genBlackSized_mem_support n t.size lo hi t).mpr ⟨hrb, rfl⟩⟩
  · rw [mem_support_default]
    refine ⟨False.elim, ?_⟩
    rintro ⟨⟨n, hrb⟩, hsz⟩
    rw [not_not] at hne
    have := mem_blackIndices_of_isRB (N := N) hrb hsz
    rw [hne] at this
    exact absurd this (List.not_mem_nil)

theorem genBlackUpTo.sound_complete :
    IsSoundAndComplete (genBlackUpTo N lo hi) (fun t => (∃ n, t.isRB lo hi n) ∧ t.size ≤ N) :=
  genBlackUpTo_mem_support N lo hi

end RedBlackTree
