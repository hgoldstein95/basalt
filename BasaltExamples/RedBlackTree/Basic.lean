/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt
import Basalt.Combinators
import BasaltExamples.RedBlackTree.Def

open RandomChoice

/-!
# Generating Red-Black Trees

`genBlack n lo hi` generates the red-black trees of black height `n` with keys in `[lo, hi]`, and
`genAny n lo hi` the same trees with the black-root requirement dropped. Both recurse structurally
on the black height and draw each pivot from the keys that leave room for a subtree of black height
`n` on either side, so their support is exactly the trees the bounds admit. The `pickOf` family
here chooses among branches whose side conditions the bounds admit, so a choice never commits to a
branch with nothing to produce.
-/

namespace RedBlackTree

/-- The fewest keys a red-black subtree of black height `n` can hold, `2 ^ n - 1`, written so that
`omega` sees the recurrence. -/
def minKeys : Nat → Nat
  | 0 => 0
  | n + 1 => 2 * minKeys n + 1

namespace RBTree

/-- The number of keys in the tree. -/
def size : RBTree → Nat
  | leaf => 0
  | node _ l _ r => l.size + r.size + 1

theorem minKeys_le_size {n : Nat} {t : RBTree} (h : t.hasBlackHeight n) : minKeys n ≤ t.size := by
  induction t generalizing n with
  | leaf => subst h; simp [minKeys, size]
  | node c l y r ihl ihr =>
    cases c with
    | red =>
      obtain ⟨hl, hr⟩ := h
      have := ihl hl
      have := ihr hr
      have : minKeys n ≤ 2 * minKeys n := by omega
      simp only [size]
      omega
    | black =>
      cases n with
      | zero => exact absurd h not_false
      | succ m =>
        obtain ⟨hl, hr⟩ := h
        have := ihl hl
        have := ihr hr
        simp only [size, minKeys]
        omega

theorem size_le_of_isBST {lo hi : Int} {t : RBTree} (h : t.isBST lo hi) :
    t.size ≤ (hi - lo + 1).toNat := by
  induction t generalizing lo hi with
  | leaf => simp [size]
  | node c l y r ihl ihr =>
    obtain ⟨h1, h2, hl, hr⟩ := h
    have := ihl hl
    have := ihr hr
    simp only [size]
    omega

/-- The room a subtree of black height `n` needs inside `[lo, hi]`. -/
theorem minKeys_le_width {lo hi : Int} {n : Nat} {t : RBTree} (hbst : t.isBST lo hi)
    (hbh : t.hasBlackHeight n) : minKeys n ≤ (hi - lo + 1).toNat :=
  le_trans (minKeys_le_size hbh) (size_le_of_isBST hbst)

end RBTree

/-! ## The generators -/

/-- Wraps a black-rooted generator `g` of black height `n` into one that may also produce a red
root, whose two children `g` supplies. The red root needs room for `2 ^ (n + 1) - 1` keys; where
there is none, no red-rooted tree of that height exists and the black-rooted ones are all of them. -/
def anyOf [Gen G] (n : Nat) (g : Int → Int → G RBTree) (lo hi : Int) : G RBTree :=
  if h : (minKeys (n + 1) : Int) ≤ hi - lo + 1 then
    pick
      (fun () => g lo hi)
      (fun () => do
        let y ← chooseInt (lo + minKeys n) (hi - minKeys n) (by simp only [minKeys] at h; omega)
        let a ← g lo (y - 1)
        let b ← g (y + 1) hi
        return .node .red a y b)
  else
    g lo hi

/-- Generates the black-rooted red-black trees of black height `n` with keys in `[lo, hi]`. When
`[lo, hi]` is too narrow to hold such a tree there is nothing to generate: `default` is the empty
distribution at `SPMF` and a generator error at a running interpretation. -/
def genBlack [Gen G] : Nat → Int → Int → G RBTree
  | 0, _, _ => pure .leaf
  | m + 1, lo, hi =>
    if h : (minKeys (m + 1) : Int) ≤ hi - lo + 1 then do
      let y ← chooseInt (lo + minKeys m) (hi - minKeys m) (by simp only [minKeys] at h; omega)
      let l ← anyOf m (fun a b => genBlack m a b) lo (y - 1)
      let r ← anyOf m (fun a b => genBlack m a b) (y + 1) hi
      return .node .black l y r
    else
      default

/-- Generates the red-black trees of black height `n` with keys in `[lo, hi]`, red root allowed. -/
def genAny [Gen G] (n : Nat) (lo hi : Int) : G RBTree := anyOf n (genBlack n) lo hi

/-! ## Support -/

theorem mem_support_default {α : Type u} {a : α} :
    a ∈ SPMF.support (default : SPMF α) ↔ False :=
  iff_false_intro (fun h => h rfl)

theorem not_mem_support_default {α : Type u} {a : α} : a ∉ SPMF.support (default : SPMF α) :=
  mem_support_default.mp

theorem anyOf_mem_support {n : Nat} {g : Int → Int → SPMF RBTree}
    (hg : ∀ lo hi t, t ∈ SPMF.support (g lo hi) ↔ t.isRB lo hi n) (lo hi : Int) (t : RBTree) :
    t ∈ SPMF.support (anyOf n g lo hi) ↔ t.isRBSubtree lo hi n := by
  have h0 : 0 ≤ (minKeys n : Int) := Int.natCast_nonneg _
  unfold anyOf
  split <;> rename_i hfeas
  · support_simp [hg, RBTree.isRB, RBTree.isRBSubtree]
    constructor
    · rintro (⟨-, ht⟩ | ⟨y, ⟨hy1, hy2⟩, a, ⟨hac, habst, hanrr, habh⟩, b,
        ⟨hbc, hbbst, hbnrr, hbbh⟩, rfl⟩)
      · exact ht
      · exact ⟨⟨by omega, by omega, habst, hbbst⟩, ⟨fun _ => ⟨hac, hbc⟩, hanrr, hbnrr⟩,
          habh, hbbh⟩
    · intro ht
      rcases t with _ | ⟨c, a, y, b⟩
      · exact Or.inl ⟨rfl, ht⟩
      cases c
      case _ =>
        obtain ⟨⟨hlo, hhi, habst, hbbst⟩, ⟨hchild, hanrr, hbnrr⟩, habh, hbbh⟩ := ht
        obtain ⟨hac, hbc⟩ := hchild rfl
        have ha := RBTree.minKeys_le_width habst habh
        have hb := RBTree.minKeys_le_width hbbst hbbh
        exact Or.inr ⟨y, ⟨by omega, by omega⟩, a, ⟨hac, habst, hanrr, habh⟩, b,
          ⟨hbc, hbbst, hbnrr, hbbh⟩, rfl⟩
      case _ => exact Or.inl ⟨rfl, ht⟩
  · rw [hg]
    simp only [RBTree.isRB, RBTree.isRBSubtree, minKeys] at hfeas ⊢
    refine ⟨fun h => h.2, fun ht => ⟨?_, ht⟩⟩
    rcases t with _ | ⟨c, a, y, b⟩
    · rfl
    cases c
    case _ =>
      obtain ⟨hbst, -, habh, hbbh⟩ := ht
      have ha := RBTree.minKeys_le_size habh
      have hb := RBTree.minKeys_le_size hbbh
      have hs := RBTree.size_le_of_isBST hbst
      simp only [RBTree.size] at hs
      omega
    case _ => rfl

theorem genBlack_mem_support (n : Nat) (lo hi : Int) (t : RBTree) :
    t ∈ SPMF.support (genBlack n lo hi) ↔ t.isRB lo hi n := by
  induction n generalizing lo hi t with
  | zero =>
    rw [genBlack]
    support_simp [RBTree.isRB, RBTree.isRBSubtree]
    rcases t with _ | ⟨c, l, y, r⟩
    · simp [RBTree.rootColor, RBTree.isBST, RBTree.noRedRed, RBTree.hasBlackHeight]
    cases c
    case _ => simp [RBTree.rootColor]
    case _ => simp [RBTree.rootColor, RBTree.hasBlackHeight]
  | succ m ih =>
    have h0 : 0 ≤ (minKeys m : Int) := Int.natCast_nonneg _
    have hany : ∀ lo hi t, t ∈ SPMF.support (anyOf m (fun a b => genBlack m a b) lo hi)
        ↔ t.isRBSubtree lo hi m := fun lo hi t => anyOf_mem_support (fun _ _ _ => ih _ _ _) lo hi t
    rw [genBlack]
    split <;> rename_i hfeas
    · support_simp [hany, RBTree.isRB, RBTree.isRBSubtree]
      constructor
      · rintro ⟨y, ⟨hy1, hy2⟩, l, ⟨hlbst, hlnrr, hlbh⟩, r, ⟨hrbst, hrnrr, hrbh⟩, rfl⟩
        exact ⟨rfl, ⟨by omega, by omega, hlbst, hrbst⟩, ⟨by simp, hlnrr, hrnrr⟩, hlbh, hrbh⟩
      · intro ht
        rcases t with _ | ⟨c, l, y, r⟩
        · exact absurd ht.2.2.2 (by simp [RBTree.hasBlackHeight])
        cases c
        case _ => exact absurd ht.1 (by simp [RBTree.rootColor])
        case _ =>
          obtain ⟨-, ⟨hlo, hhi, hlbst, hrbst⟩, ⟨-, hlnrr, hrnrr⟩, hlbh, hrbh⟩ := ht
          have hl := RBTree.minKeys_le_width hlbst hlbh
          have hr := RBTree.minKeys_le_width hrbst hrbh
          exact ⟨y, ⟨by omega, by omega⟩, l, ⟨hlbst, hlnrr, hlbh⟩, r, ⟨hrbst, hrnrr, hrbh⟩, rfl⟩
    · simp only [RBTree.isRB, RBTree.isRBSubtree, minKeys] at hfeas ⊢
      refine ⟨fun h => absurd h not_mem_support_default, fun ht => ?_⟩
      exfalso
      rcases t with _ | ⟨c, l, y, r⟩
      · exact absurd ht.2.2.2 (by simp [RBTree.hasBlackHeight])
      cases c
      case _ => exact absurd ht.1 (by simp [RBTree.rootColor])
      case _ =>
        obtain ⟨-, hbst, -, hlbh, hrbh⟩ := ht
        have hl := RBTree.minKeys_le_size hlbh
        have hr := RBTree.minKeys_le_size hrbh
        have hs := RBTree.size_le_of_isBST hbst
        simp only [RBTree.size] at hs
        omega

theorem RBTree.isRB_zero_iff {lo hi : Int} {t : RBTree} : t.isRB lo hi 0 ↔ t = .leaf := by
  rcases t with _ | ⟨c, l, y, r⟩
  · simp [RBTree.isRB, RBTree.isRBSubtree, RBTree.rootColor, RBTree.isBST, RBTree.noRedRed,
      RBTree.hasBlackHeight]
  cases c
  · simp [RBTree.isRB, RBTree.rootColor]
  · simp [RBTree.isRB, RBTree.isRBSubtree, RBTree.rootColor, RBTree.hasBlackHeight]

/-- Every key of an ordered tree lies within its bounds. -/
theorem RBTree.contains_bounds {lo hi x : Int} {t : RBTree} (hbst : t.isBST lo hi)
    (hc : t.contains x) : lo ≤ x ∧ x ≤ hi := by
  induction t generalizing lo hi with
  | leaf => exact absurd hc not_false
  | node c l y r ihl ihr =>
    obtain ⟨h1, h2, hl, hr⟩ := hbst
    rcases hc with rfl | hc | hc
    · exact ⟨h1, h2⟩
    · have := ihl hl hc; omega
    · have := ihr hr hc; omega

theorem genAny_mem_support (n : Nat) (lo hi : Int) (t : RBTree) :
    t ∈ SPMF.support (genAny n lo hi) ↔ t.isRBSubtree lo hi n :=
  anyOf_mem_support (fun _ _ _ => genBlack_mem_support n _ _ _) lo hi t

theorem genBlack.sound_complete :
    IsSoundAndComplete (genBlack n lo hi) (RBTree.isRB lo hi n) :=
  genBlack_mem_support n lo hi

theorem genAny.sound_complete :
    IsSoundAndComplete (genAny n lo hi) (RBTree.isRBSubtree lo hi n) :=
  genAny_mem_support n lo hi

/-! ## Choosing among the branches that can produce something -/

/-- Chooses between two branches, each guarded by a side condition, and takes whichever the bounds
admit. Testing the condition *inside* a branch instead would let the choice commit to a branch with
nothing to produce, and that loss compounds at every level of a recursion. -/
def pickOf2 [Gen G] {p q : Prop} [Decidable p] [Decidable q] (a : p → G α) (b : q → G α) : G α :=
  if hp : p then
    if hq : q then pick (fun () => a hp) (fun () => b hq) else a hp
  else if hq : q then b hq else default

/-- `pickOf2` with an unguarded third branch, which is also the fallback. -/
def pickOf3 [Gen G] {p q : Prop} [Decidable p] [Decidable q]
    (c : G α) (a : p → G α) (b : q → G α) : G α :=
  if hp : p then
    if hq : q then pick (fun () => c) (fun () => pick (fun () => a hp) (fun () => b hq))
    else pick (fun () => c) (fun () => a hp)
  else if hq : q then pick (fun () => c) (fun () => b hq)
  else c

theorem mem_support_pickOf2 {p q A B : Prop} [Decidable p] [Decidable q]
    {a : p → SPMF α} {b : q → SPMF α} {t : α}
    (ha : ∀ h, t ∈ SPMF.support (a h) ↔ A) (hb : ∀ h, t ∈ SPMF.support (b h) ↔ B)
    (hap : A → p) (hbq : B → q) :
    t ∈ SPMF.support (pickOf2 a b) ↔ A ∨ B := by
  unfold pickOf2
  split_ifs with hp hq hq
  · rw [SPMF.mem_support_pick_iff, ha, hb]
  · rw [ha]
    exact ⟨Or.inl, fun h => h.resolve_right fun hB => hq (hbq hB)⟩
  · rw [hb]
    exact ⟨Or.inr, fun h => h.resolve_left fun hA => hp (hap hA)⟩
  · rw [mem_support_default]
    exact ⟨False.elim, fun h => h.elim (fun hA => hp (hap hA)) fun hB => hq (hbq hB)⟩

theorem mem_support_pickOf3 {p q A B C : Prop} [Decidable p] [Decidable q]
    {c : SPMF α} {a : p → SPMF α} {b : q → SPMF α} {t : α}
    (hc : t ∈ SPMF.support c ↔ C)
    (ha : ∀ h, t ∈ SPMF.support (a h) ↔ A) (hb : ∀ h, t ∈ SPMF.support (b h) ↔ B)
    (hap : A → p) (hbq : B → q) :
    t ∈ SPMF.support (pickOf3 c a b) ↔ C ∨ A ∨ B := by
  unfold pickOf3
  split_ifs with hp hq hq
  · rw [SPMF.mem_support_pick_iff, SPMF.mem_support_pick_iff, hc, ha, hb]
  · rw [SPMF.mem_support_pick_iff, hc, ha]
    exact ⟨fun h => h.imp id Or.inl,
      fun h => h.imp id fun h => h.resolve_right fun hB => hq (hbq hB)⟩
  · rw [SPMF.mem_support_pick_iff, hc, hb]
    exact ⟨fun h => h.imp id Or.inr,
      fun h => h.imp id fun h => h.resolve_left fun hA => hp (hap hA)⟩
  · rw [hc]
    exact ⟨Or.inl, fun h => h.resolve_right fun h =>
      h.elim (fun hA => hp (hap hA)) fun hB => hq (hbq hB)⟩


/-- Three branches, each guarded by a side condition. `pickOf3` is the variant whose first branch
is always available; use this one where every branch can be empty. -/
def pickOf3All [Gen G] {p q r : Prop} [Decidable p] [Decidable q] [Decidable r]
    (a : p → G α) (b : q → G α) (c : r → G α) : G α :=
  pickOf2 a (fun (_ : q ∨ r) => pickOf2 b c)

theorem mem_support_pickOf3All {p q r A B C : Prop} [Decidable p] [Decidable q] [Decidable r]
    {a : p → SPMF α} {b : q → SPMF α} {c : r → SPMF α} {t : α}
    (ha : ∀ h, t ∈ SPMF.support (a h) ↔ A) (hb : ∀ h, t ∈ SPMF.support (b h) ↔ B)
    (hc : ∀ h, t ∈ SPMF.support (c h) ↔ C)
    (hap : A → p) (hbq : B → q) (hcr : C → r) :
    t ∈ SPMF.support (pickOf3All a b c) ↔ A ∨ B ∨ C :=
  mem_support_pickOf2 ha (fun _ => mem_support_pickOf2 hb hc hbq hcr) hap fun h => h.imp hbq hcr

end RedBlackTree
