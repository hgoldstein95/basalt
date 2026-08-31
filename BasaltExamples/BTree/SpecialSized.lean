/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt
import Basalt.Combinators
import BasaltExamples.BTree.Sized
import BasaltExamples.BTree.Special

open RandomChoice

/-!
# Generating Splitting B-Trees of a Given Node Count

`genSplittingSized t h s x lo hi` generates the B-trees of order `t` and height `h` with exactly `s`
nodes that inserting `x` splits, and `genSplittingUpTo t N x lo hi` unions those over every
`(height, node count)` pair such a tree of at most `N` nodes can have. The subtree on `x`'s path
claims `t + 1` values beyond its node count's own reserve — `t` because its leaf is full, one for
`x` itself — and that surcharge is the only way the path shows up in the interval arithmetic.
-/

namespace BTree

/-! ## What a splitting subtree claims -/

/-- The surcharge a subtree on `x`'s path adds to the reserve its node count already forces: `t`
for the full leaf at the end of the path, one for `x`, which is in the interval but is no key. -/
def xExtra (t : Nat) : Nat := t + 1

/-- `ForestFor`'s version of `Forest.sum_le`: the child on `x`'s path claims the surcharge, every
other child claims only its own reserve. -/
theorem ForestFor.sum_le {P : Int → Int → Tree → Prop} {Q : Tree → Prop} {f : Tree → Nat}
    {e : Nat} {x : Int}
    (hP : ∀ a b c, P a b c → a + (f c : Int) ≤ b + 1)
    (hQ : ∀ a b c, P a b c → Q c → a ≤ x → x ≤ b → a + ((f c + e : Nat) : Int) ≤ b + 1) :
    ∀ (ks : List Int) (cs : List Tree) (lo hi : Int), x ∉ ks → lo ≤ x → x ≤ hi →
      ForestFor P Q x lo hi ks cs →
      lo + ((ks.length + (cs.map f).sum + e : Nat) : Int) ≤ hi + 1 := by
  intro ks
  induction ks with
  | nil =>
    intro cs lo hi _ hlo hhi hf
    match cs with
    | [c] => have := hQ lo hi c hf.1 hf.2 hlo hhi; simpa using this
    | [] => exact absurd hf not_false
    | _ :: _ :: _ => exact absurd hf not_false
  | cons k ks ih =>
    intro cs lo hi hx hlo hhi hf
    simp only [List.mem_cons, not_or] at hx
    match cs with
    | [] => exact absurd hf not_false
    | c :: cs' =>
      unfold ForestFor at hf
      split at hf
      · rename_i hlt
        obtain ⟨⟨hc, hq⟩, hrest⟩ := hf
        have h1 := hQ lo (k - 1) c hc hq hlo (by omega)
        have h2 := Forest.sum_le hP ks cs' (k + 1) hi hrest
        simp only [List.map_cons, List.sum_cons, List.length_cons]
        push_cast at h1 h2 ⊢
        omega
      · rename_i hnlt
        obtain ⟨hc, hrest⟩ := hf
        have hkx : k < x := by have : x ≠ k := hx.1; omega
        have h1 := hP lo (k - 1) c hc
        have h2 := ih cs' (k + 1) hi hx.2 (by omega) hhi hrest
        simp only [List.map_cons, List.sum_cons, List.length_cons]
        push_cast at h1 h2 ⊢
        omega

/-- A splitting subtree of `s` nodes claims `(t - 1) * (s - 1) + kmin` values for its keys and
`t + 1` more for its full leaf and for `x`. -/
theorem Tree.IsBTreeAt.xwidth (ht : 1 ≤ t) {x : Int} :
    ∀ (h kmin : Nat) (lo hi : Int) (tr : Tree), kmin ≤ t - 1 →
      Tree.IsBTreeAt t kmin h lo hi tr → Tree.SplitsOn t x h tr → lo ≤ x → x ≤ hi →
      lo + (((t - 1) * (tr.size - 1) + kmin + xExtra t : Nat) : Int) ≤ hi + 1 := by
  intro h
  induction h with
  | zero =>
    rintro kmin lo hi ⟨ks, cs⟩ hkm ⟨rfl, hmin, hmax, hg⟩ ⟨hx, hlen⟩ hlo hhi
    have hroom := (GappedFor.of_gapped_one hlo hhi hx hg).room
    unfold RoomFor at hroom
    rw [hlen] at hroom
    have hsz : Tree.size ⟨ks, ([] : List Tree)⟩ - 1 = 0 := by rw [Tree.size_mk]; simp
    rw [hsz]
    unfold xExtra
    push_cast at hroom ⊢
    omega
  | succ h ih =>
    rintro kmin lo hi ⟨ks, cs⟩ hkm ⟨hmin, hmax, hg, hforest⟩ ⟨hx, c, hc, hsp⟩ hlo hhi
    have hff : ForestFor (fun a b c => Tree.IsBTreeAt t (t - 1) h a b c)
        (fun c => Tree.SplitsOn t x h c) x lo hi ks cs :=
      (forestFor_iff ks cs lo hi).mpr ⟨hforest, c, hc, hsp⟩
    have hP : ∀ a b c, Tree.IsBTreeAt t (t - 1) h a b c →
        a + (((t - 1) * c.size : Nat) : Int) ≤ b + 1 := by
      intro a b c hc'
      have h1 := Tree.IsBTreeAt.width (t := t) h (t - 1) a b c hc'
      rwa [mul_pred_add _ _ (Tree.one_le_size c)] at h1
    have hQ : ∀ a b c, Tree.IsBTreeAt t (t - 1) h a b c → Tree.SplitsOn t x h c →
        a ≤ x → x ≤ b → a + ((((t - 1) * c.size : Nat) + xExtra t : Nat) : Int) ≤ b + 1 := by
      intro a b c hc' hq ha hb
      have h1 := ih (t - 1) a b c le_rfl hc' hq ha hb
      rwa [mul_pred_add _ _ (Tree.one_le_size c)] at h1
    have hsum := ForestFor.sum_le hP hQ ks cs lo hi hx hlo hhi hff
    have hsz : Tree.size ⟨ks, cs⟩ - 1 = (cs.map Tree.size).sum := by rw [Tree.size_mk]; omega
    rw [hsz, sum_map_mul] at *
    have hk : (kmin : Int) ≤ (ks.length : Int) := by exact_mod_cast hmin
    push_cast at hsum ⊢
    omega

/-- The leaf half of the reserve, for a subtree on `x`'s path: `t` values per leaf less one, plus
the surcharge. The full leaf at the end of the path pays for the `t`, and `x` for the one. -/
theorem Tree.IsBTreeAt.xleaves_width (ht : 1 ≤ t) {x : Int} :
    ∀ (h kmin : Nat) (lo hi : Int) (tr : Tree),
      Tree.IsBTreeAt t kmin h lo hi tr → Tree.SplitsOn t x h tr → lo ≤ x → x ≤ hi →
      lo + ((t * tr.leaves - 1 + xExtra t : Nat) : Int) ≤ hi + 1 := by
  intro h
  induction h with
  | zero =>
    rintro kmin lo hi ⟨ks, cs⟩ ⟨rfl, hmin, hmax, hg⟩ ⟨hx, hlen⟩ hlo hhi
    have hroom := (GappedFor.of_gapped_one hlo hhi hx hg).room
    unfold RoomFor at hroom
    rw [hlen] at hroom
    have hlv : Tree.leaves (⟨ks, ([] : List Tree)⟩ : Tree) = 1 := by simp [Tree.leaves]
    rw [hlv]
    unfold xExtra
    push_cast at hroom ⊢
    omega
  | succ h ih =>
    rintro kmin lo hi ⟨ks, cs⟩ ⟨hmin, hmax, hgap, hf⟩ ⟨hx, c, hc, hsp⟩ hlo hhi
    have hff : ForestFor (fun a b c => Tree.IsBTreeAt t (t - 1) h a b c)
        (fun c => Tree.SplitsOn t x h c) x lo hi ks cs :=
      (forestFor_iff ks cs lo hi).mpr ⟨hf, c, hc, hsp⟩
    have hP : ∀ a b c, Tree.IsBTreeAt t (t - 1) h a b c →
        a + ((t * c.leaves - 1 : Nat) : Int) ≤ b + 1 :=
      fun a b c hc' => Tree.IsBTreeAt.leaves_width ht h (t - 1) a b c (Or.inl le_rfl) hc'
    have hQ : ∀ a b c, Tree.IsBTreeAt t (t - 1) h a b c → Tree.SplitsOn t x h c →
        a ≤ x → x ≤ b → a + (((t * c.leaves - 1 : Nat) + xExtra t : Nat) : Int) ≤ b + 1 :=
      fun a b c hc' hq ha hb => ih (t - 1) a b c hc' hq ha hb
    have hsum := ForestFor.sum_le hP hQ ks cs lo hi hx hlo hhi hff
    have hlen := Forest.length_eq ks cs lo hi hf
    have hne : cs ≠ [] := by intro hnil; rw [hnil] at hlen; simp at hlen
    have hid := sum_map_leaves_pred t ht cs
    have hkey : t * (cs.map Tree.leaves).sum - 1
        = ks.length + (cs.map fun c => t * c.leaves - 1).sum := by omega
    rw [Tree.leaves_of_ne ks cs hne, hkey]
    push_cast at hsum ⊢
    omega

/-- The reserve a subtree on `x`'s path claims: its node count's own reserve plus the surcharge. -/
theorem Tree.IsBTreeAt.xresv_width (ht : 1 ≤ t) {x : Int} (h : Nat) : ∀ (lo hi : Int) (c : Tree),
    Tree.IsBTreeAt t (t - 1) h lo hi c → Tree.SplitsOn t x h c → lo ≤ x → x ≤ hi →
    lo + (((resv t h c.size : Nat) + xExtra t : Nat) : Int) ≤ hi + 1 := by
  intro lo hi c hc hq hlo hhi
  have h1 := Tree.IsBTreeAt.xwidth (t := t) ht h (t - 1) lo hi c le_rfl hc hq hlo hhi
  rw [mul_pred_add _ _ (Tree.one_le_size c)] at h1
  have h2 := Tree.IsBTreeAt.xleaves_width ht h (t - 1) lo hi c hc hq hlo hhi
  have h3 := Tree.IsBTreeAt.size_le_leaves ht h (t - 1) lo hi c hc
  have h4 : t * (c.size - innerSize t h) - 1 ≤ t * c.leaves - 1 := by
    have hle : c.size - innerSize t h ≤ c.leaves := by omega
    have := Nat.mul_le_mul_left t hle
    omega
  have h5 : ((t * (c.size - innerSize t h) - 1 + xExtra t : Nat) : Int)
      ≤ ((t * c.leaves - 1 + xExtra t : Nat) : Int) := by exact_mod_cast Nat.add_le_add_right h4 _
  simp only [resv]
  rcases Nat.le_total ((t - 1) * c.size) (t * (c.size - innerSize t h) - 1) with hle | hle
  · rw [max_eq_right hle]; omega
  · rw [max_eq_left hle]; omega

/-! ## Keys with a reserve per slot, and a surcharge on `x`'s slot -/

/-- `GappedForL e x rs lo hi ks`: `GappedL` with `e` values demanded on top of its own reserve by
the slot `x` falls into, and with `x` itself no key of `ks`. -/
def GappedForL (e : Nat) (x : Int) : List Nat → Int → Int → List Int → Prop
  | [r], lo, hi, [] => lo + ((r + e : Nat) : Int) ≤ hi + 1 ∧ lo ≤ x ∧ x ≤ hi
  | r :: r' :: rs, lo, hi, k :: ks =>
      if x < k then lo + ((r + e : Nat) : Int) ≤ k ∧ lo ≤ x ∧ GappedL (r' :: rs) (k + 1) hi ks
      else lo + (r : Int) ≤ k ∧ k < x ∧ GappedForL e x (r' :: rs) (k + 1) hi ks
  | _, _, _, _ => False

theorem GappedForL.length (e : Nat) (x : Int) : ∀ (rs : List Nat) (lo hi : Int) (ks : List Int),
    GappedForL e x rs lo hi ks → ks.length + 1 = rs.length := by
  intro rs
  induction rs with
  | nil => intro lo hi ks h; exact absurd h (by cases ks <;> exact not_false)
  | cons r rs ih =>
    match rs with
    | [] =>
      intro lo hi ks h
      match ks with
      | [] => rfl
      | _ :: _ => exact absurd h not_false
    | r' :: rs' =>
      intro lo hi ks h
      match ks with
      | [] => exact absurd h not_false
      | k :: ks' =>
        unfold GappedForL at h
        have : ks'.length + 1 = (r' :: rs').length := by
          split at h
          · have := GappedL.length _ _ _ _ h.2.2
            simpa using this
          · exact ih (k + 1) hi ks' h.2.2
        simp only [List.length_cons] at *
        omega

theorem GappedForL.gapped (e : Nat) (x : Int) : ∀ (rs : List Nat) (lo hi : Int) (ks : List Int),
    GappedForL e x rs lo hi ks → Gapped 0 lo hi ks := by
  intro rs
  induction rs with
  | nil => intro lo hi ks h; exact absurd h (by cases ks <;> exact not_false)
  | cons r rs ih =>
    match rs with
    | [] =>
      intro lo hi ks h
      match ks with
      | [] => simp only [Gapped]; simp only [GappedForL] at h; omega
      | _ :: _ => exact absurd h not_false
    | r' :: rs' =>
      intro lo hi ks h
      match ks with
      | [] => exact absurd h not_false
      | k :: ks' =>
        unfold GappedForL at h
        split at h
        · exact ⟨by simp; omega, GappedL.gapped _ _ _ _ h.2.2⟩
        · exact ⟨by simp; omega, ih (k + 1) hi ks' h.2.2⟩

theorem GappedForL.notMem (e : Nat) (x : Int) : ∀ (rs : List Nat) (lo hi : Int) (ks : List Int),
    GappedForL e x rs lo hi ks → x ∉ ks := by
  intro rs
  induction rs with
  | nil => intro lo hi ks h; exact absurd h (by cases ks <;> exact not_false)
  | cons r rs ih =>
    match rs with
    | [] =>
      intro lo hi ks h
      match ks with
      | [] => simp
      | _ :: _ => exact absurd h not_false
    | r' :: rs' =>
      intro lo hi ks h
      match ks with
      | [] => exact absurd h not_false
      | k :: ks' =>
        unfold GappedForL at h
        simp only [List.mem_cons, not_or]
        split at h
        · rename_i hlt
          refine ⟨by omega, fun hmem => ?_⟩
          have := (GappedL.gapped _ _ _ _ h.2.2).le_of_mem x hmem
          omega
        · exact ⟨by omega, ih (k + 1) hi ks' h.2.2⟩

theorem GappedForL.need (e : Nat) (x : Int) : ∀ (rs : List Nat) (lo hi : Int) (ks : List Int),
    GappedForL e x rs lo hi ks → lo + ((needL rs + e : Nat) : Int) ≤ hi + 1 := by
  intro rs
  induction rs with
  | nil => intro lo hi ks h; exact absurd h (by cases ks <;> exact not_false)
  | cons r rs ih =>
    match rs with
    | [] =>
      intro lo hi ks h
      match ks with
      | [] => simp only [GappedForL] at h; simpa [needL] using h.1
      | _ :: _ => exact absurd h not_false
    | r' :: rs' =>
      intro lo hi ks h
      match ks with
      | [] => exact absurd h not_false
      | k :: ks' =>
        unfold GappedForL at h
        simp only [needL]
        split at h
        · obtain ⟨hk, -, htl⟩ := h
          have := GappedL.need _ _ _ _ htl
          push_cast at hk this ⊢
          omega
        · obtain ⟨hk, -, htl⟩ := h
          have := ih (k + 1) hi ks' htl
          push_cast at hk this ⊢
          omega

/-- The keys of a node on `x`'s path spread far enough apart: each child's own reserve, and the
surcharge for the one that must hold `x`. -/
theorem GappedForL.of_forestFor {P : Int → Int → Tree → Prop} {Q : Tree → Prop} {f : Tree → Nat}
    {e : Nat} {x : Int}
    (hP : ∀ a b c, P a b c → a + (f c : Int) ≤ b + 1)
    (hQ : ∀ a b c, P a b c → Q c → a ≤ x → x ≤ b → a + ((f c + e : Nat) : Int) ≤ b + 1) :
    ∀ (ks : List Int) (cs : List Tree) (lo hi : Int), x ∉ ks → lo ≤ x → x ≤ hi →
      ForestFor P Q x lo hi ks cs → GappedForL e x (cs.map f) lo hi ks := by
  intro ks
  induction ks with
  | nil =>
    intro cs lo hi _ hlo hhi hf
    match cs with
    | [c] =>
      have := hQ lo hi c hf.1 hf.2 hlo hhi
      simp only [List.map_cons, List.map_nil, GappedForL]
      exact ⟨this, hlo, hhi⟩
    | [] => exact absurd hf not_false
    | _ :: _ :: _ => exact absurd hf not_false
  | cons k ks ih =>
    intro cs lo hi hx hlo hhi hf
    simp only [List.mem_cons, not_or] at hx
    match cs with
    | [] => exact absurd hf not_false
    | c :: cs' =>
      unfold ForestFor at hf
      have hne : cs' ≠ [] := by
        split at hf
        · intro hnil; subst hnil; exact absurd hf.2 (by cases ks <;> exact not_false)
        · intro hnil; subst hnil; exact absurd hf.2 (by cases ks <;> exact not_false)
      match cs', hne with
      | c' :: cs'', _ =>
        simp only [List.map_cons, GappedForL]
        split at hf
        · rename_i hlt
          obtain ⟨⟨hc, hq⟩, hrest⟩ := hf
          rw [if_pos hlt]
          refine ⟨by have := hQ lo (k - 1) c hc hq hlo (by omega); omega, hlo, ?_⟩
          have := GappedL.of_forest hP ks (c' :: cs'') (k + 1) hi hrest
          simpa using this
        · rename_i hnlt
          obtain ⟨hc, hrest⟩ := hf
          have hkx : k < x := by have : x ≠ k := hx.1; omega
          rw [if_neg (by omega)]
          refine ⟨by have := hP lo (k - 1) c hc; omega, hkx, ?_⟩
          have := ih (c' :: cs'') (k + 1) hi hx.2 (by omega) hhi hrest
          simpa using this

/-- A first key above `x`: the slot below it is fixed, and the rest is ordinary. -/
def genAboveXL [Gen G] (rs : List Nat) (a a' hi : Int) (h : a ≤ a') : G (List Int) := do
  let k ← chooseInt a a' h
  let ks ← genGappedL rs (k + 1) hi
  return k :: ks

/-- A first key below `x`: the surcharge moves along to the slots that remain. -/
def genBelowXL [Gen G] (rec : Int → G (List Int)) (b b' : Int) (h : b ≤ b') : G (List Int) := do
  let k ← chooseInt b b' h
  let ks ← rec (k + 1)
  return k :: ks

/-- Generates keys spaced by a reserve list, missing `x`, and leaving the slot `x` falls into `e`
values beyond its reserve. The first key either lands above `x` — fixing that slot and leaving the
rest ordinary — or below it, and the surcharge moves along. -/
def genGappedForL [Gen G] (e : Nat) (x : Int) : List Nat → Int → Int → G (List Int)
  | [], _, _ => default
  | [r], lo, hi =>
      if lo + ((r + e : Nat) : Int) ≤ hi + 1 ∧ lo ≤ x ∧ x ≤ hi then pure [] else default
  | r :: r' :: rs, lo, hi =>
      if hA : lo ≤ x ∧ max (lo + ((r + e : Nat) : Int)) (x + 1)
          ≤ hi - (needL (r' :: rs) : Nat) then
        if hB : lo + (r : Int) ≤ min (x - 1) (hi - ((needL (r' :: rs) + e : Nat) : Int)) then
          pick (fun () => genAboveXL (r' :: rs) _ _ hi hA.2)
            (fun () => genBelowXL (fun a => genGappedForL e x (r' :: rs) a hi) _ _ hB)
        else genAboveXL (r' :: rs) _ _ hi hA.2
      else if hB : lo + (r : Int) ≤ min (x - 1) (hi - ((needL (r' :: rs) + e : Nat) : Int)) then
        genBelowXL (fun a => genGappedForL e x (r' :: rs) a hi) _ _ hB
      else default

theorem genGappedForL_mem_support (e : Nat) (x : Int) :
    ∀ (rs : List Nat) (lo hi : Int) (ks : List Int),
      ks ∈ SPMF.support (genGappedForL e x rs lo hi : SPMF (List Int))
        ↔ GappedForL e x rs lo hi ks := by
  intro rs
  induction rs with
  | nil =>
    intro lo hi ks
    rw [genGappedForL, mem_support_default]
    exact ⟨False.elim, fun h => absurd h (by cases ks <;> exact not_false)⟩
  | cons r rs ih =>
    match rs with
    | [] =>
      intro lo hi ks
      rw [genGappedForL]
      split <;> rename_i hd
      · support_simp
        constructor
        · rintro rfl; exact hd
        · intro h
          match ks with
          | [] => rfl
          | _ :: _ => exact absurd h not_false
      · rw [mem_support_default]
        refine ⟨False.elim, fun h => ?_⟩
        match ks with
        | [] => exact hd h
        | _ :: _ => exact absurd h not_false
    | r' :: rs' =>
      intro lo hi ks
      have hAiff : ∀ (hA : lo ≤ x ∧ max (lo + ((r + e : Nat) : Int)) (x + 1)
            ≤ hi - (needL (r' :: rs') : Nat)),
          (ks ∈ SPMF.support (genAboveXL (r' :: rs')
              (max (lo + ((r + e : Nat) : Int)) (x + 1))
              (hi - (needL (r' :: rs') : Nat)) hi hA.2 : SPMF (List Int))
            ↔ ∃ k ks', ks = k :: ks' ∧ x < k ∧ lo ≤ x ∧ lo + ((r + e : Nat) : Int) ≤ k ∧
                GappedL (r' :: rs') (k + 1) hi ks') := by
        intro hA
        simp only [genAboveXL]
        support_simp [genGappedL_mem_support]
        constructor
        · rintro ⟨k, ⟨hk1, hk2⟩, ks', hmem, rfl⟩
          simp only [max_le_iff] at hk1
          exact ⟨k, ks', rfl, by omega, hA.1, hk1.1, hmem⟩
        · rintro ⟨k, ks', rfl, hxk, hlox, hrk, hgl⟩
          have hneed := GappedL.need _ _ _ _ hgl
          exact ⟨k, ⟨by simp only [max_le_iff]; omega, by omega⟩, ks', hgl, rfl⟩
      have hBiff : ∀ (hB : lo + (r : Int)
            ≤ min (x - 1) (hi - ((needL (r' :: rs') + e : Nat) : Int))),
          (ks ∈ SPMF.support (genBelowXL
              (fun a => (genGappedForL e x (r' :: rs') a hi : SPMF (List Int))) (lo + (r : Int))
              (min (x - 1) (hi - ((needL (r' :: rs') + e : Nat) : Int))) hB)
            ↔ ∃ k ks', ks = k :: ks' ∧ k < x ∧ lo + (r : Int) ≤ k ∧
                GappedForL e x (r' :: rs') (k + 1) hi ks') := by
        intro hB
        simp only [genBelowXL]
        support_simp [ih]
        constructor
        · rintro ⟨k, ⟨hk1, hk2⟩, ks', hmem, rfl⟩
          simp only [le_min_iff] at hk2
          exact ⟨k, ks', rfl, by omega, hk1, hmem⟩
        · rintro ⟨k, ks', rfl, hxk, hrk, hgl⟩
          have hneed := GappedForL.need _ _ _ _ _ _ hgl
          push_cast at hneed
          exact ⟨k, ⟨hrk, by simp only [le_min_iff]; push_cast; omega⟩, ks', hgl, rfl⟩
      have htarget : GappedForL e x (r :: r' :: rs') lo hi ks ↔
          ((∃ k ks', ks = k :: ks' ∧ x < k ∧ lo ≤ x ∧ lo + ((r + e : Nat) : Int) ≤ k ∧
              GappedL (r' :: rs') (k + 1) hi ks') ∨
           (∃ k ks', ks = k :: ks' ∧ k < x ∧ lo + (r : Int) ≤ k ∧
              GappedForL e x (r' :: rs') (k + 1) hi ks')) := by
        constructor
        · intro h
          match ks with
          | [] => exact absurd h not_false
          | k :: ks' =>
            unfold GappedForL at h
            split at h
            · exact Or.inl ⟨k, ks', rfl, by assumption, h.2.1, h.1, h.2.2⟩
            · exact Or.inr ⟨k, ks', rfl, h.2.1, h.1, h.2.2⟩
        · rintro (⟨k, ks', rfl, hxk, hlox, hrk, hgl⟩ | ⟨k, ks', rfl, hxk, hrk, hgl⟩)
          · unfold GappedForL; rw [if_pos hxk]; exact ⟨hrk, hlox, hgl⟩
          · unfold GappedForL; rw [if_neg (by omega)]; exact ⟨hrk, hxk, hgl⟩
      rw [genGappedForL]
      split_ifs with hA hB hB
      · support_simp
        rw [hAiff hA, hBiff hB, htarget]
      · rw [hAiff hA, htarget]
        refine ⟨Or.inl, ?_⟩
        rintro (h | ⟨k, ks', rfl, hxk, hrk, hgl⟩)
        · exact h
        · exact absurd (by
            have hneed := GappedForL.need _ _ _ _ _ _ hgl
            push_cast at hneed
            simp only [le_min_iff]
            omega) hB
      · rw [hBiff hB, htarget]
        refine ⟨Or.inr, ?_⟩
        rintro (⟨k, ks', rfl, hxk, hlox, hrk, hgl⟩ | h)
        · exact absurd (by
            have hneed := GappedL.need _ _ _ _ hgl
            refine ⟨hlox, ?_⟩
            simp only [max_le_iff]
            omega) hA
        · exact h
      · rw [mem_support_default, htarget]
        refine ⟨False.elim, ?_⟩
        rintro (⟨k, ks', rfl, hxk, hlox, hrk, hgl⟩ | ⟨k, ks', rfl, hxk, hrk, hgl⟩)
        · exact absurd (by
            have hneed := GappedL.need _ _ _ _ hgl
            refine ⟨hlox, ?_⟩
            simp only [max_le_iff]
            omega) hA
        · exact absurd (by
            have hneed := GappedForL.need _ _ _ _ _ _ hgl
            push_cast at hneed
            simp only [le_min_iff]
            omega) hB

/-! ## Nodes on `x`'s path -/

/-- `ForestFor` at a cons, as a rewrite: `unfold` leaves a `Decidable.rec` that `split` cannot
see, so the `ite` has to be produced by an equation. -/
theorem forestFor_cons {P : Int → Int → Tree → Prop} {Q : Tree → Prop} {x k : Int}
    (ks : List Int) (c : Tree) (cs : List Tree) (lo hi : Int) :
    ForestFor P Q x lo hi (k :: ks) (c :: cs) ↔
      (if x < k then (P lo (k - 1) c ∧ Q c) ∧ Forest P (k + 1) hi ks cs
       else P lo (k - 1) c ∧ ForestFor P Q x (k + 1) hi ks cs) := by
  rw [ForestFor]

/-- Generates the children of a node on `x`'s path: the one whose interval contains `x` continues
the path, the others are ordinary subtrees, each at the node count `ss` assigns it. -/
def genChildrenForSized [Gen G] (gen genx : Nat → Int → Int → G Tree) (x : Int) :
    List Nat → Int → Int → List Int → G (List Tree)
  | [s], lo, hi, [] => do
      let c ← genx s lo hi
      return [c]
  | s :: s' :: ss, lo, hi, k :: ks =>
      if x < k then do
        let c ← genx s lo (k - 1)
        let cs ← genChildrenSized gen (s' :: ss) (k + 1) hi ks
        return c :: cs
      else do
        let c ← gen s lo (k - 1)
        let cs ← genChildrenForSized gen genx x (s' :: ss) (k + 1) hi ks
        return c :: cs
  | _, _, _, _ => default

theorem genChildrenForSized_mem_support {gen genx : Nat → Int → Int → SPMF Tree}
    {P : Int → Int → Tree → Prop} {Q : Tree → Prop} {x : Int}
    (hgen : ∀ s a b u, u ∈ SPMF.support (gen s a b) ↔ P a b u ∧ u.size = s)
    (hgenx : ∀ s a b u, a ≤ x → x ≤ b →
      (u ∈ SPMF.support (genx s a b) ↔ (P a b u ∧ Q u) ∧ u.size = s)) :
    ∀ (ss : List Nat) (ks : List Int) (lo hi : Int) (cs : List Tree),
      lo ≤ x → x ≤ hi → x ∉ ks →
      (cs ∈ SPMF.support (genChildrenForSized gen genx x ss lo hi ks)
        ↔ ForestFor P Q x lo hi ks cs ∧ cs.map Tree.size = ss) := by
  intro ss
  induction ss with
  | nil =>
    intro ks lo hi cs _ _ _
    rw [genChildrenForSized, mem_support_default]
    · refine ⟨False.elim, ?_⟩
      rintro ⟨hf, hm⟩
      have : cs = [] := List.map_eq_nil_iff.mp hm
      subst this
      exact absurd hf (by cases ks <;> exact not_false)
    all_goals simp
  | cons s ss ih =>
    match ss with
    | [] =>
      intro ks lo hi cs hlo hhi hx
      match ks with
      | [] =>
        have hgx : ∀ u, u ∈ SPMF.support (genx s lo hi) ↔ (P lo hi u ∧ Q u) ∧ u.size = s :=
          fun u => hgenx s lo hi u hlo hhi
        rw [genChildrenForSized]
        support_simp [hgx]
        constructor
        · rintro ⟨c, ⟨hP, hsz⟩, rfl⟩
          exact ⟨hP, by simp [hsz]⟩
        · rintro ⟨hf, hm⟩
          match cs with
          | [c] => exact ⟨c, ⟨hf, by simpa using hm⟩, rfl⟩
          | [] => simp at hm
          | _ :: _ :: _ => simp at hm
      | k :: ks' =>
        rw [genChildrenForSized, mem_support_default]
        · refine ⟨False.elim, ?_⟩
          rintro ⟨hf, hm⟩
          match cs with
          | [] => simp at hm
          | [c] =>
            rw [forestFor_cons] at hf
            split at hf
            · exact absurd hf.2 (by cases ks' <;> exact not_false)
            · exact absurd hf.2 (by cases ks' <;> exact not_false)
          | _ :: _ :: _ => simp at hm
        all_goals simp
    | s' :: ss' =>
      intro ks lo hi cs hlo hhi hx
      match ks with
      | [] =>
        rw [genChildrenForSized, mem_support_default]
        · refine ⟨False.elim, ?_⟩
          rintro ⟨hf, hm⟩
          match cs with
          | [c] => simp at hm
          | [] => exact absurd hf not_false
          | _ :: _ :: _ => exact absurd hf not_false
        all_goals simp
      | k :: ks' =>
        simp only [List.mem_cons, not_or] at hx
        rw [genChildrenForSized]
        by_cases hlt : x < k
        · rw [if_pos hlt]
          have hgx : ∀ u, u ∈ SPMF.support (genx s lo (k - 1))
              ↔ (P lo (k - 1) u ∧ Q u) ∧ u.size = s :=
            fun u => hgenx s lo (k - 1) u hlo (by omega)
          support_simp [hgx, genChildrenSized_mem_support hgen]
          constructor
          · rintro ⟨c, ⟨hP, hsz⟩, cs₀, ⟨hf, hm⟩, rfl⟩
            exact ⟨(forestFor_cons ks' c cs₀ lo hi).mpr (by rw [if_pos hlt]; exact ⟨hP, hf⟩),
              by simp [hsz, hm]⟩
          · rintro ⟨hf, hm⟩
            match cs with
            | [] => simp at hm
            | c :: cs₀ =>
              rw [forestFor_cons, if_pos hlt] at hf
              simp only [List.map_cons, List.cons.injEq] at hm
              exact ⟨c, ⟨hf.1, hm.1⟩, cs₀, ⟨hf.2, hm.2⟩, rfl⟩
        · rw [if_neg hlt]
          have hkx : k < x := by have : x ≠ k := hx.1; omega
          have hrec : ∀ u,
              u ∈ SPMF.support (genChildrenForSized gen genx x (s' :: ss') (k + 1) hi ks')
                ↔ ForestFor P Q x (k + 1) hi ks' u ∧ u.map Tree.size = s' :: ss' :=
            fun u => ih ks' (k + 1) hi u (by omega) hhi hx.2
          support_simp [hgen, hrec]
          constructor
          · rintro ⟨c, ⟨hP, hsz⟩, cs₀, ⟨hf, hm⟩, rfl⟩
            exact ⟨(forestFor_cons ks' c cs₀ lo hi).mpr (by rw [if_neg hlt]; exact ⟨hP, hf⟩),
              by simp [hsz, hm]⟩
          · rintro ⟨hf, hm⟩
            match cs with
            | [] => simp at hm
            | c :: cs₀ =>
              rw [forestFor_cons, if_neg hlt] at hf
              simp only [List.map_cons, List.cons.injEq] at hm
              exact ⟨c, ⟨hf.1, hm.1⟩, cs₀, ⟨hf.2, hm.2⟩, rfl⟩

/-- Generates the full leaf at the end of `x`'s path: `2t - 1` keys that miss `x`. -/
def genFullLeaf [Gen G] (t kmin : Nat) (x lo hi : Int) : G Tree :=
  if kmin ≤ 2 * t - 1 ∧ lo ≤ x ∧ x ≤ hi ∧ RoomFor 0 1 (2 * t - 1) lo hi then do
    let ks ← genGappedFor 0 1 x (2 * t - 1) lo hi
    return ⟨ks, []⟩
  else default

theorem genFullLeaf_mem_support (t kmin : Nat) (x lo hi : Int) (hlo : lo ≤ x) (hhi : x ≤ hi)
    (ks : List Int) (cs : List Tree) :
    (⟨ks, cs⟩ : Tree) ∈ SPMF.support (genFullLeaf t kmin x lo hi : SPMF Tree)
      ↔ Tree.IsBTreeAt t kmin 0 lo hi ⟨ks, cs⟩ ∧ Tree.SplitsOn t x 0 ⟨ks, cs⟩ := by
  unfold genFullLeaf
  split <;> rename_i hg
  · support_simp [genGappedFor_mem_support 0 1 (by omega) x (2 * t - 1) lo hi _ hlo hhi hg.2.2.2,
      Tree.mk.injEq]
    constructor
    · rintro ⟨ks', ⟨hlen, hgf⟩, rfl, rfl⟩
      exact ⟨⟨rfl, by omega, by omega, hgf.gapped (by omega)⟩, hgf.notMem, hlen⟩
    · rintro ⟨⟨rfl, hmin, hmax, hgap⟩, hx, hlen⟩
      exact ⟨ks, ⟨hlen, GappedFor.of_gapped_one hlo hhi hx hgap⟩, rfl, rfl⟩
  · rw [mem_support_default]
    refine ⟨False.elim, ?_⟩
    rintro ⟨⟨rfl, hmin, hmax, hgap⟩, hx, hlen⟩
    refine hg ⟨by omega, hlo, hhi, ?_⟩
    have := (GappedFor.of_gapped_one hlo hhi hx hgap).room
    rwa [hlen] at this

/-! ## What the order has to be

The paper does not state its B-tree arity, and the model here fixes it by the usual minimum-degree
convention: a node holds between `t - 1` and `2 * t - 1` keys. That choice is checkable against the
paper's own data, and it does not match. -/

/-- **A splitting tree needs `2 * t` distinct values in its interval.** The leaf the search reaches
is full, so it holds `2 * t - 1` keys, and `x` falls inside that leaf's interval without being one
of them. -/
theorem Tree.SplitsOn.width_ge (ht : 1 ≤ t) {x : Int} {h : Nat} {lo hi : Int} {tr : Tree}
    (hv : Tree.IsBTree t h lo hi tr) (hsp : Tree.SplitsOn t x h tr) (hlo : lo ≤ x) (hhi : x ≤ hi) :
    lo + ((2 * t : Nat) : Int) ≤ hi + 1 := by
  have hw := Tree.IsBTreeAt.xleaves_width ht h (min 1 h) lo hi tr hv hsp hlo hhi
  have hl : 1 ≤ tr.leaves := Tree.one_le_leaves tr
  have hmul : t * 1 ≤ t * tr.leaves := Nat.mul_le_mul_left t hl
  have : ((2 * t : Nat) : Int) ≤ ((t * tr.leaves - 1 + xExtra t : Nat) : Int) := by
    have : 2 * t ≤ t * tr.leaves - 1 + xExtra t := by unfold xExtra; omega
    exact_mod_cast this
  omega

/-- **The paper's small special B-tree bound describes an empty set at every order `t ≥ 2`, but the
paper reports exactly one structure there — so the paper's nodes are not minimum-degree nodes.**

Dewey, Nichols and Hardekopf run special B-trees at bounds `2, 2` (at most two nodes, element
values `0`–`2`) and explain Korat's speed there by there being "only one satisfying structure in the
space" (§VI-B). Under the minimum-degree convention a full leaf holds `2 * t - 1 ≥ 3` keys and `x`
must differ from all of them, so four distinct values are needed and only three exist:
`Tree.SplitsOn.width_ge` rules the whole bound out. A node holding at most **two** keys — a 2-3
tree, `⌈m/2⌉`-to-`m` children with `m = 3` — does admit exactly one such structure once `x` is
fixed, which is the reading the paper's count supports.

Basalt's `t` cannot express that: `2 * t - 1` is odd for every `t`, so the maximum key count is
never `2`. Matching the paper exactly needs the arity as an independent `(minKeys, maxKeys)` pair
with `2 * minKeys ≤ maxKeys`, which is a change to `Tree.IsBTreeAt` and everything indexed by it —
deliberately not made here. Every other bound in the paper's tables is even in its element budget
and is unaffected. -/
theorem no_splitting_at_paper_small_bound (ht : 2 ≤ t) {x : Int} (hlo : 0 ≤ x) (hhi : x ≤ 2) :
    ¬ ∃ (h : Nat) (tr : Tree), Tree.IsBTree t h 0 2 tr ∧ Tree.SplitsOn t x h tr := by
  rintro ⟨h, tr, hv, hsp⟩
  have hw := Tree.SplitsOn.width_ge (by omega) hv hsp hlo hhi
  have : (4 : Int) ≤ ((2 * t : Nat) : Int) := by exact_mod_cast Nat.mul_le_mul_left 2 ht
  omega

/-- The arities a height-`h + 1` node on `x`'s path can have: `arities`, with the surcharge for the
child that must hold `x` added to the room the keys need. -/
def xArities (t kmin h s : Nat) (lo hi : Int) : List Nat :=
  (List.range (2 * t + 1)).filter fun k =>
    decide (kmin + 1 ≤ k ∧ k * minSize t h ≤ s - 1 ∧ s - 1 ≤ k * maxSize t h ∧
      lo + ((k - 1 + (t - 1) * (s - 1) + xExtra t : Nat) : Int) ≤ hi + 1)

theorem mem_xArities {t kmin h s k : Nat} {lo hi : Int} :
    k ∈ xArities t kmin h s lo hi ↔
      k ≤ 2 * t ∧ kmin + 1 ≤ k ∧ k * minSize t h ≤ s - 1 ∧ s - 1 ≤ k * maxSize t h ∧
        lo + ((k - 1 + (t - 1) * (s - 1) + xExtra t : Nat) : Int) ≤ hi + 1 := by
  simp only [xArities, List.mem_filter, List.mem_range, decide_eq_true_eq]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by omega, h2.1, h2.2.1, h2.2.2.1, h2.2.2.2⟩
  · rintro ⟨h1, h2, h3, h4, h5⟩; exact ⟨by omega, h2, h3, h4, h5⟩

/-- The reserve every ordinary child claims, read off its own validity. -/
theorem child_width (h : Nat) : ∀ a b c, Tree.IsBTreeAt t (t - 1) h a b c →
    a + (((t - 1) * c.size : Nat) : Int) ≤ b + 1 := by
  intro a b c hc
  have h1 := Tree.IsBTreeAt.width (t := t) h (t - 1) a b c hc
  rwa [mul_pred_add _ _ (Tree.one_le_size c)] at h1

/-- The reserve the child on `x`'s path claims. -/
theorem xchild_width (ht : 1 ≤ t) {x : Int} (h : Nat) : ∀ a b c,
    Tree.IsBTreeAt t (t - 1) h a b c → Tree.SplitsOn t x h c → a ≤ x → x ≤ b →
    a + ((((t - 1) * c.size : Nat) + xExtra t : Nat) : Int) ≤ b + 1 := by
  intro a b c hc hq ha hb
  have h1 := Tree.IsBTreeAt.xwidth (t := t) ht h (t - 1) a b c le_rfl hc hq ha hb
  rwa [mul_pred_add _ _ (Tree.one_le_size c)] at h1

/-- A valid splitting tree's own arity is one the guard admits. -/
theorem mem_xArities_of_splitting (ht : 1 ≤ t) {x : Int} {h kmin s : Nat} {lo hi : Int}
    {ks : List Int} {cs : List Tree} (hv : Tree.IsBTreeAt t kmin (h + 1) lo hi ⟨ks, cs⟩)
    (hsp : Tree.SplitsOn t x (h + 1) ⟨ks, cs⟩) (hlo : lo ≤ x) (hhi : x ≤ hi)
    (hsize : Tree.size ⟨ks, cs⟩ = s) : ks.length + 1 ∈ xArities t kmin h s lo hi := by
  obtain ⟨hmin, hmax, hgap, hf⟩ := hv
  obtain ⟨hx, c, hc, hcsp⟩ := hsp
  obtain ⟨hslo, hshi⟩ := Forest.sum_range (child_size_range ht) ks cs lo hi hf
  have hsum : (cs.map Tree.size).sum = s - 1 := by rw [Tree.size_mk] at hsize; omega
  have hff : ForestFor (fun a b c => Tree.IsBTreeAt t (t - 1) h a b c)
      (fun c => Tree.SplitsOn t x h c) x lo hi ks cs :=
    (forestFor_iff ks cs lo hi).mpr ⟨hf, c, hc, hcsp⟩
  have hwidth := ForestFor.sum_le (child_width h) (xchild_width ht h) ks cs lo hi hx hlo hhi hff
  rw [sum_map_mul, hsum] at hwidth
  rw [mem_xArities]
  refine ⟨by omega, by omega, by rw [← hsum]; omega, by rw [← hsum]; omega, ?_⟩
  push_cast at hwidth ⊢
  omega

/-- Generates the B-trees of order `t` and height `h` with exactly `s` nodes that `x` splits, whose
root holds at least `kmin` keys. -/
def genFullSized [Gen G] (t kmin : Nat) (x : Int) : (h s : Nat) → (lo hi : Int) → G Tree
  | 0, s, lo, hi => if s = 1 then genFullLeaf t kmin x lo hi else default
  | h + 1, s, lo, hi =>
      if hne : xArities t kmin h s lo hi ≠ [] then do
        let k ← elements (xArities t kmin h s lo hi) hne
        let ss ← genSizes (minSize t h) (maxSize t h) k (s - 1)
        let ks ← genGappedForL (xExtra t) x (ss.map fun sc => resv t h sc) lo hi
        let cs ← genChildrenForSized (fun s' a b => genNodeSized t (t - 1) h s' a b)
          (fun s' a b => genFullSized t (t - 1) x h s' a b) x ss lo hi ks
        return ⟨ks, cs⟩
      else default

theorem genFullSized_mem_support (ht : 1 ≤ t) {x : Int} :
    ∀ (h kmin s : Nat) (lo hi : Int) (tr : Tree), lo ≤ x → x ≤ hi →
      (tr ∈ SPMF.support (genFullSized t kmin x h s lo hi : SPMF Tree)
        ↔ (Tree.IsBTreeAt t kmin h lo hi tr ∧ Tree.SplitsOn t x h tr) ∧ tr.size = s) := by
  intro h
  induction h with
  | zero =>
    rintro kmin s lo hi ⟨ks, cs⟩ hlo hhi
    rw [genFullSized]
    have hsz : Tree.IsBTreeAt t kmin 0 lo hi ⟨ks, cs⟩ → Tree.size ⟨ks, cs⟩ = 1 := by
      rintro ⟨rfl, -, -, -⟩; simp [Tree.size_mk]
    split <;> rename_i hs
    · subst hs
      rw [genFullLeaf_mem_support t kmin x lo hi hlo hhi]
      exact ⟨fun hv => ⟨hv, hsz hv.1⟩, fun hv => hv.1⟩
    · rw [mem_support_default]
      exact ⟨False.elim, fun hv => hs (by rw [← hv.2, hsz hv.1.1])⟩
  | succ h ih =>
    rintro kmin s lo hi ⟨ks, cs⟩ hlo hhi
    rw [genFullSized]
    have hchild : ∀ s' a b u,
        u ∈ SPMF.support (genNodeSized t (t - 1) h s' a b : SPMF Tree)
          ↔ Tree.IsBTreeAt t (t - 1) h a b u ∧ u.size = s' :=
      fun s' a b u => genNodeSized_mem_support ht h (t - 1) s' a b u
    have hchildx : ∀ s' a b u, a ≤ x → x ≤ b →
        (u ∈ SPMF.support (genFullSized t (t - 1) x h s' a b : SPMF Tree)
          ↔ (Tree.IsBTreeAt t (t - 1) h a b u ∧ Tree.SplitsOn t x h u) ∧ u.size = s') :=
      fun s' a b u ha hb => ih (t - 1) s' a b u ha hb
    split <;> rename_i hne
    · support_simp [genSizes_mem_support, genGappedForL_mem_support, Tree.mk.injEq]
      constructor
      · rintro ⟨k, hkm, ss, ⟨hlen, hmem, hsum⟩, ks', hks', cs', hcs', rfl, rfl⟩
        rw [genChildrenForSized_mem_support hchild hchildx ss ks lo hi cs hlo hhi
          (GappedForL.notMem _ _ _ _ _ _ hks')] at hcs'
        obtain ⟨hff, hm⟩ := hcs'
        rw [mem_xArities] at hkm
        have hlenks : ks.length + 1 = ss.length := by
          have := GappedForL.length _ _ _ _ _ _ hks'
          simpa using this
        have hmin1 := one_le_minSize t h
        have hkpos : 1 ≤ k := by omega
        have hs1 : 1 ≤ s - 1 :=
          le_trans (le_trans hmin1 (Nat.le_mul_of_pos_left _ hkpos)) hkm.2.2.1
        obtain ⟨hforest, c, hc, hq⟩ := (forestFor_iff ks cs lo hi).mp hff
        refine ⟨⟨⟨by omega, by omega, GappedForL.gapped _ _ _ _ _ _ hks', hforest⟩,
          GappedForL.notMem _ _ _ _ _ _ hks', c, hc, hq⟩, ?_⟩
        rw [Tree.size_mk, hm, hsum]
        omega
      · rintro ⟨⟨hv, hsp⟩, hsize⟩
        obtain ⟨hmin, hmax, hgap, hf⟩ := hv
        obtain ⟨hx, c, hc, hcsp⟩ := hsp
        obtain ⟨hslo, hshi⟩ := Forest.sum_range (child_size_range ht) ks cs lo hi hf
        have hlencs := Forest.length_eq ks cs lo hi hf
        have hsum : (cs.map Tree.size).sum = s - 1 := by rw [Tree.size_mk] at hsize; omega
        have hff : ForestFor (fun a b c => Tree.IsBTreeAt t (t - 1) h a b c)
            (fun c => Tree.SplitsOn t x h c) x lo hi ks cs :=
          (forestFor_iff ks cs lo hi).mpr ⟨hf, c, hc, hcsp⟩
        have hgfl : GappedForL (xExtra t) x ((cs.map Tree.size).map fun sc => resv t h sc)
            lo hi ks := by
          have := GappedForL.of_forestFor (f := fun c => resv t h c.size)
            (Tree.IsBTreeAt.resv_width ht h) (Tree.IsBTreeAt.xresv_width ht h)
            ks cs lo hi hx hlo hhi hff
          simpa [List.map_map, Function.comp_def] using this
        refine ⟨ks.length + 1,
          mem_xArities_of_splitting ht ⟨hmin, hmax, hgap, hf⟩ ⟨hx, c, hc, hcsp⟩ hlo hhi hsize,
          cs.map Tree.size, ⟨by simp [hlencs], ?_, hsum⟩, ks, hgfl, cs, ?_, rfl, rfl⟩
        · intro y hy
          obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hy
          obtain ⟨a, b, hP⟩ := Forest.exists_of_mem ks cs lo hi hf c' hc'
          exact child_size_range ht a b c' hP
        · rw [genChildrenForSized_mem_support hchild hchildx _ ks lo hi cs hlo hhi hx]
          exact ⟨hff, rfl⟩
    · rw [mem_support_default]
      refine ⟨False.elim, ?_⟩
      rintro ⟨⟨hv, hsp⟩, hsize⟩
      rw [not_not] at hne
      have := mem_xArities_of_splitting ht hv hsp hlo hhi hsize
      rw [hne] at this
      exact absurd this List.not_mem_nil

/-! ## The generators -/

/-- Generates the B-trees of order `t` with keys in `[lo, hi]`, every leaf at depth `h`, exactly
`s` nodes, and a full leaf on `x`'s search path — the trees inserting `x` splits. -/
def genSplittingSized [Gen G] (t h s : Nat) (x lo hi : Int) : G Tree :=
  genFullSized t (min 1 h) x h s lo hi

theorem genSplittingSized_mem_support (ht : 1 ≤ t) (h s : Nat) (x lo hi : Int) (hlo : lo ≤ x)
    (hhi : x ≤ hi) (tr : Tree) :
    tr ∈ SPMF.support (genSplittingSized t h s x lo hi : SPMF Tree)
      ↔ (Tree.IsBTree t h lo hi tr ∧ Tree.SplitsOn t x h tr) ∧ tr.size = s :=
  genFullSized_mem_support ht h (min 1 h) s lo hi tr hlo hhi

theorem genSplittingSized.sound_complete (ht : 1 ≤ t) (hlo : lo ≤ x) (hhi : x ≤ hi) :
    IsSoundAndComplete (genSplittingSized t h s x lo hi : SPMF Tree)
      (fun tr => (Tree.IsBTree t h lo hi tr ∧ Tree.SplitsOn t x h tr) ∧ tr.size = s) :=
  genSplittingSized_mem_support ht h s x lo hi hlo hhi

/-! ## At most `N` nodes -/

/-- The `(height, node count)` pairs a splitting B-tree of at most `N` nodes with keys in `[lo, hi]`
can have: `sizeIndices` with the surcharge for the full leaf and for `x`.

It inherits `sizeIndices`' gap — the conjuncts are necessary, not sufficient — with its own
witnesses: `(3, 17)` and `(3, 18)` are both in `xSizeIndices 2 20 0 20` and both generate nothing.
See `sizeIndices` for why, and `BasaltTest/IO.lean` for the pin. -/
def xSizeIndices (t N : Nat) (lo hi : Int) : List (Nat × Nat) :=
  ((List.range (N + 1)).flatMap fun h => (List.range (N + 1)).map fun s => (h, s)).filter
    fun p => decide (rootMinSize t (min 1 p.1) p.1 ≤ p.2 ∧ p.2 ≤ maxSize t p.1 ∧
      lo + (((t - 1) * (p.2 - 1) + min 1 p.1 + xExtra t : Nat) : Int) ≤ hi + 1 ∧
      lo + ((t * (p.2 - innerSize t p.1) - 1 + xExtra t : Nat) : Int) ≤ hi + 1)

theorem mem_xSizeIndices {t N h s : Nat} {lo hi : Int} :
    (h, s) ∈ xSizeIndices t N lo hi ↔
      (h ≤ N ∧ s ≤ N) ∧ rootMinSize t (min 1 h) h ≤ s ∧ s ≤ maxSize t h ∧
        lo + (((t - 1) * (s - 1) + min 1 h + xExtra t : Nat) : Int) ≤ hi + 1 ∧
        lo + ((t * (s - innerSize t h) - 1 + xExtra t : Nat) : Int) ≤ hi + 1 := by
  simp only [xSizeIndices, List.mem_filter, List.mem_flatMap, List.mem_map, List.mem_range,
    Prod.mk.injEq, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨h', hh', s', hs', rfl, rfl⟩, hp⟩
    exact ⟨⟨by omega, by omega⟩, hp.1, hp.2.1, hp.2.2.1, hp.2.2.2⟩
  · rintro ⟨⟨hh, hs⟩, hp⟩
    exact ⟨⟨h, by omega, s, by omega, rfl, rfl⟩, hp⟩

theorem mem_xSizeIndices_of_splitting (ht : 2 ≤ t) {N h : Nat} {x lo hi : Int} {tr : Tree}
    (hv : Tree.IsBTree t h lo hi tr) (hsp : Tree.SplitsOn t x h tr) (hlo : lo ≤ x) (hhi : x ≤ hi)
    (hsz : tr.size ≤ N) : (h, tr.size) ∈ xSizeIndices t N lo hi := by
  have hrange := Tree.IsBTreeAt.size_range (by omega) h (min 1 h) lo hi tr hv
  have hwidth := Tree.IsBTreeAt.xwidth (t := t) (by omega) h (min 1 h) lo hi tr
    (by omega) hv hsp hlo hhi
  have hlt := lt_rootMinSize (t := t) (by omega) h
  have hleaf := Tree.IsBTreeAt.xleaves_width (t := t) (by omega) h (min 1 h) lo hi tr hv hsp hlo hhi
  have hsl := Tree.IsBTreeAt.size_le_leaves (t := t) (by omega) h (min 1 h) lo hi tr hv
  have h4 : t * (tr.size - innerSize t h) - 1 + xExtra t ≤ t * tr.leaves - 1 + xExtra t := by
    have hle : tr.size - innerSize t h ≤ tr.leaves := by omega
    have := Nat.mul_le_mul_left t hle
    omega
  have h5 : ((t * (tr.size - innerSize t h) - 1 + xExtra t : Nat) : Int)
      ≤ ((t * tr.leaves - 1 + xExtra t : Nat) : Int) := by exact_mod_cast h4
  rw [mem_xSizeIndices]
  exact ⟨⟨by omega, hsz⟩, hrange.1, hrange.2, hwidth, by omega⟩

/-- Generates the B-trees of order `t` with keys in `[lo, hi]` that hold at most `N` nodes and that
inserting `x` splits — the paper's bound on special B-trees — as the union of `genSplittingSized`
over every `(height, node count)` pair such a tree can have. -/
def genSplittingUpTo [Gen G] (t N : Nat) (x lo hi : Int) : G Tree :=
  if hne : xSizeIndices t N lo hi ≠ [] then
    oneOf ((xSizeIndices t N lo hi).map fun p =>
      fun (_ : Unit) => genSplittingSized t p.1 p.2 x lo hi) (by simpa using hne)
  else default

theorem genSplittingUpTo_mem_support (ht : 2 ≤ t) (N : Nat) (x lo hi : Int) (hlo : lo ≤ x)
    (hhi : x ≤ hi) (tr : Tree) :
    tr ∈ SPMF.support (genSplittingUpTo t N x lo hi : SPMF Tree)
      ↔ (∃ h, Tree.IsBTree t h lo hi tr ∧ Tree.SplitsOn t x h tr) ∧ tr.size ≤ N := by
  unfold genSplittingUpTo
  split <;> rename_i hne
  · rw [SPMF.mem_support_oneOf_iff]
    simp only [List.mem_map]
    constructor
    · rintro ⟨g, ⟨⟨h, s⟩, hmem, rfl⟩, hsupp⟩
      rw [genSplittingSized_mem_support (by omega) _ _ _ _ _ hlo hhi] at hsupp
      obtain ⟨⟨hv, hsp⟩, rfl⟩ := hsupp
      exact ⟨⟨h, hv, hsp⟩, (mem_xSizeIndices.mp hmem).1.2⟩
    · rintro ⟨⟨h, hv, hsp⟩, hsz⟩
      exact ⟨_, ⟨(h, tr.size), mem_xSizeIndices_of_splitting ht hv hsp hlo hhi hsz, rfl⟩,
        (genSplittingSized_mem_support (by omega) h tr.size x lo hi hlo hhi tr).mpr
          ⟨⟨hv, hsp⟩, rfl⟩⟩
  · rw [mem_support_default]
    refine ⟨False.elim, ?_⟩
    rintro ⟨⟨h, hv, hsp⟩, hsz⟩
    rw [not_not] at hne
    have := mem_xSizeIndices_of_splitting (N := N) ht hv hsp hlo hhi hsz
    rw [hne] at this
    exact absurd this List.not_mem_nil

theorem genSplittingUpTo.sound_complete (ht : 2 ≤ t) (hlo : lo ≤ x) (hhi : x ≤ hi) :
    IsSoundAndComplete (genSplittingUpTo t N x lo hi : SPMF Tree)
      (fun tr => (∃ h, Tree.IsBTree t h lo hi tr ∧ Tree.SplitsOn t x h tr) ∧ tr.size ≤ N) :=
  genSplittingUpTo_mem_support ht N x lo hi hlo hhi

end BTree
