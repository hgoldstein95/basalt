/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import BasaltExamples.BTree.Basic

open RandomChoice

/-!
# B-Trees That Split on a Given Key

`genSplitting t h x lo hi` generates the B-trees that `x` splits: valid trees of order `t` in
which the search for `x` reaches a full leaf, so that a **bottom-up** insertion of `x` (`insertAt`)
overflows that leaf and splits it. The search path is generated node by node, with `x`'s key
interval kept wide enough for the full leaf below it; every other subtree is an ordinary
`genNode` draw. A tree that `x` splits never holds `x` itself (`Tree.SplitsOn.not_hasKey`).
-/

namespace BTree

/-! ## Room along `x`'s path -/

/-- `[lo, hi]` has room for `m` keys spaced `g` apart, with a gap of `N` at the end that holds `x`
and `g` at every other end. -/
def RoomFor (g N m : Nat) (lo hi : Int) : Prop := lo + (m * (g + 1) + N : Nat) ≤ hi + 1

instance : Decidable (RoomFor g N m lo hi) := by unfold RoomFor; infer_instance

/-- `GappedFor g N x lo hi ks`: gapped keys that miss `x`, with `N` values in the interval `x` falls
into and `g` in every other. -/
def GappedFor (g N : Nat) (x : Int) : Int → Int → List Int → Prop
  | lo, hi, [] => lo + N ≤ hi + 1 ∧ lo ≤ x ∧ x ≤ hi
  | lo, hi, k :: ks =>
      if x < k then lo + N ≤ k ∧ lo ≤ x ∧ Gapped g (k + 1) hi ks
      else lo + g ≤ k ∧ k < x ∧ GappedFor g N x (k + 1) hi ks

/-- The interval a height-`h` subtree on `x`'s path claims: an ordinary subtree's, plus `x` itself
and the keys that fill its leaf. -/
def xgapAt (t : Nat) : Nat → Nat
  | 0 => 1
  | h + 1 => gap t (h + 1) + t + 1

/-- The keys a height-`h` subtree needs room for when its root holds `kmin` of them, its leaf on
`x`'s path is full, and it misses `x`. -/
def xNeed (t kmin : Nat) : Nat → Nat
  | 0 => 2 * t
  | h + 1 => kmin * (gap t (h + 1) + 1) + xgapAt t (h + 1)

/-- `[lo, hi]` has room for a height-`h` subtree that `x` splits. -/
def XFits (t kmin h : Nat) (lo hi : Int) : Prop := lo + (xNeed t kmin h : Nat) ≤ hi + 1

theorem xNeed_nonroot (ht : 1 ≤ t) (h : Nat) : xNeed t (t - 1) h = xgapAt t (h + 1) := by
  cases h with
  | zero => simp only [xNeed, xgapAt, gap]; omega
  | succ h => simp only [xNeed, xgapAt, gap]; ring

theorem RoomFor.mono (hle : m' ≤ m) (h : RoomFor g N m lo hi) : RoomFor g N m' lo hi := by
  unfold RoomFor at *
  have := Nat.mul_le_mul_right (g + 1) hle
  omega

/-! ## `GappedFor` -/

theorem GappedFor.room (h : GappedFor g N x lo hi ks) : RoomFor g N ks.length lo hi := by
  induction ks generalizing lo with
  | nil => simpa [RoomFor] using h.1
  | cons k ks ih =>
    unfold GappedFor at h
    unfold RoomFor at *
    have hexp : ((ks.length + 1) * (g + 1) + N : Nat)
        = (ks.length * (g + 1) + N : Nat) + (g + 1) := by ring
    simp only [List.length_cons, hexp]
    split at h
    · obtain ⟨hk, -, htl⟩ := h
      have := htl.room
      unfold Room at this
      push_cast at this ⊢
      omega
    · obtain ⟨hk, -, htl⟩ := h
      have := ih htl
      push_cast at this ⊢
      omega

theorem GappedFor.gapped (hgN : g ≤ N) (h : GappedFor g N x lo hi ks) : Gapped g lo hi ks := by
  induction ks generalizing lo with
  | nil => simp only [Gapped]; have := h.1; omega
  | cons k ks ih =>
    unfold GappedFor at h
    split at h
    · obtain ⟨hk, -, htl⟩ := h
      exact ⟨by omega, htl⟩
    · obtain ⟨hk, -, htl⟩ := h
      exact ⟨hk, ih htl⟩

theorem GappedFor.notMem (h : GappedFor g N x lo hi ks) : x ∉ ks := by
  induction ks generalizing lo with
  | nil => simp
  | cons k ks ih =>
    unfold GappedFor at h
    split at h
    · obtain ⟨-, -, htl⟩ := h
      simp only [List.mem_cons, not_or]
      refine ⟨by omega, fun hx => ?_⟩
      have := htl.le_of_mem x hx
      omega
    · obtain ⟨-, hk, htl⟩ := h
      simp only [List.mem_cons, not_or]
      exact ⟨by omega, ih htl⟩

/-- With no room to demand beyond `x` itself, missing `x` is all `GappedFor` adds. -/
theorem GappedFor.of_gapped_one (hlo : lo ≤ x) (hhi : x ≤ hi) (hx : x ∉ ks)
    (h : Gapped 0 lo hi ks) : GappedFor 0 1 x lo hi ks := by
  induction ks generalizing lo with
  | nil => exact ⟨by simp only [Gapped] at h; omega, hlo, hhi⟩
  | cons k ks ih =>
    obtain ⟨hk, htl⟩ := h
    simp only [List.mem_cons, not_or] at hx
    unfold GappedFor
    split
    · exact ⟨by omega, hlo, htl⟩
    · exact ⟨by omega, by omega, ih (by omega) hx.2 htl⟩

/-! ## The subtree `x` descends into -/

/-- Like `Forest`, but the child whose interval contains `x` also satisfies `Q`. -/
def ForestFor (P : Int → Int → Tree → Prop) (Q : Tree → Prop) (x : Int) :
    Int → Int → List Int → List Tree → Prop
  | lo, hi, [], [c] => P lo hi c ∧ Q c
  | lo, hi, k :: ks, c :: cs =>
      if x < k then (P lo (k - 1) c ∧ Q c) ∧ Forest P (k + 1) hi ks cs
      else P lo (k - 1) c ∧ ForestFor P Q x (k + 1) hi ks cs
  | _, _, _, _ => False

theorem forestFor_iff {P : Int → Int → Tree → Prop} {Q : Tree → Prop} {x : Int} :
    ∀ (ks : List Int) (cs : List Tree) (lo hi : Int),
      ForestFor P Q x lo hi ks cs ↔
        Forest P lo hi ks cs ∧ ∃ c, childFor x ks cs = some c ∧ Q c := by
  intro ks
  induction ks with
  | nil =>
    intro cs lo hi
    match cs with
    | [] => simp [ForestFor, Forest]
    | [c] => simp [ForestFor, Forest, childFor]
    | _ :: _ :: _ => simp [ForestFor, Forest, childFor]
  | cons k ks ih =>
    intro cs lo hi
    match cs with
    | [] => simp [ForestFor, Forest]
    | c :: cs =>
      simp only [ForestFor, Forest, childFor]
      split
      · simp only [and_assoc]
        constructor
        · rintro ⟨hc, hq, hf⟩
          exact ⟨hc, hf, c, rfl, hq⟩
        · rintro ⟨hc, hf, c', hc', hq⟩
          cases hc'
          exact ⟨hc, hq, hf⟩
      · rw [and_congr_right_iff.mpr (fun _ => ih cs (k + 1) hi), and_assoc]

/-- The keys of a node on `x`'s path spread far enough apart: `g` for each ordinary child, `N` for
the child that must hold `x`. -/
theorem GappedFor.of_forestFor {P : Int → Int → Tree → Prop} {Q : Tree → Prop} {g N : Nat}
    {x : Int}
    (hP : ∀ a b c, P a b c → a + (g : Int) ≤ b + 1)
    (hQ : ∀ a b c, P a b c → Q c → a ≤ x → x ≤ b → a + (N : Int) ≤ b + 1) :
    ∀ (ks : List Int) (cs : List Tree) (lo hi : Int), x ∉ ks → lo ≤ x → x ≤ hi →
      ForestFor P Q x lo hi ks cs → GappedFor g N x lo hi ks := by
  intro ks
  induction ks with
  | nil =>
    intro cs lo hi _ hlo hhi hf
    match cs with
    | [c] => exact ⟨hQ lo hi c hf.1 hf.2 hlo hhi, hlo, hhi⟩
    | [] => exact absurd hf not_false
    | _ :: _ :: _ => exact absurd hf not_false
  | cons k ks ih =>
    intro cs lo hi hx hlo hhi hf
    simp only [List.mem_cons, not_or] at hx
    match cs with
    | [] => exact absurd hf not_false
    | c :: cs =>
      unfold ForestFor at hf
      unfold GappedFor
      split at hf
      · rename_i hlt
        obtain ⟨⟨hc, hq⟩, hrest⟩ := hf
        rw [if_pos hlt]
        exact ⟨by have := hQ lo (k - 1) c hc hq hlo (by omega); omega, hlo,
          Gapped.of_forest hP hrest⟩
      · rename_i hnlt
        obtain ⟨hc, hrest⟩ := hf
        have hkx : k < x := by
          have : x ≠ k := hx.1
          omega
        rw [if_neg (by omega)]
        exact ⟨by have := hP lo (k - 1) c hc; omega, hkx,
          ih cs (k + 1) hi hx.2 (by omega) hhi hrest⟩

/-- A subtree that `x` splits needs room for `x` and for the keys that fill its leaf. -/
theorem Tree.IsBTreeAt.xfits {t : Nat} {x : Int} (ht : 1 ≤ t) :
    ∀ (h kmin : Nat) (lo hi : Int) (tr : Tree),
      Tree.IsBTreeAt t kmin h lo hi tr → Tree.SplitsOn t x h tr → lo ≤ x → x ≤ hi →
      XFits t kmin h lo hi := by
  intro h
  induction h with
  | zero =>
    rintro kmin lo hi ⟨ks, cs⟩ ⟨-, hmin, -, hg⟩ ⟨hx, hlen⟩ hlo hhi
    have := (GappedFor.of_gapped_one hlo hhi hx hg).room
    unfold RoomFor at this
    unfold XFits xNeed
    rw [hlen] at this
    push_cast at this ⊢
    omega
  | succ h ih =>
    rintro kmin lo hi ⟨ks, cs⟩ ⟨hmin, -, -, hforest⟩ ⟨hx, c, hc, hsplit⟩ hlo hhi
    have hff : ForestFor (fun a b c => Tree.IsBTreeAt t (t - 1) h a b c)
        (fun c => Tree.SplitsOn t x h c) x lo hi ks cs :=
      (forestFor_iff ks cs lo hi).mpr ⟨hforest, c, hc, hsplit⟩
    have hgf : GappedFor (gap t (h + 1)) (xgapAt t (h + 1)) x lo hi ks := by
      refine GappedFor.of_forestFor ?_ ?_ ks cs lo hi hx hlo hhi hff
      · intro a b c hc
        have := Tree.IsBTreeAt.fits h (t - 1) a b c hc
        unfold Fits Room at this
        rw [gap]
        push_cast at this ⊢
        omega
      · intro a b c hc hq ha hb
        have := ih (t - 1) a b c hc hq ha hb
        unfold XFits at this
        rw [xNeed_nonroot ht] at this
        exact this
    have := (hgf.room).mono hmin
    unfold RoomFor at this
    unfold XFits xNeed
    push_cast at this ⊢
    omega

/-! ## Generating the keys of a node on `x`'s path -/

/-- A first key above `x`, then ordinary gapped keys. -/
def genAboveX [Gen G] (g m : Nat) (a a' hi : Int) (h : a ≤ a') : G (List Int) := do
  let k ← chooseInt a a' h
  let ks ← genGapped g m (k + 1) hi
  return k :: ks

/-- A first key below `x`, then keys that still have to leave room for `x`. -/
def genBelowX [Gen G] (rec : Int → G (List Int)) (b b' : Int) (h : b ≤ b') : G (List Int) := do
  let k ← chooseInt b b' h
  let ks ← rec (k + 1)
  return k :: ks

/-- Generates `m` keys spaced `g` apart inside `[lo, hi]` that miss `x` and leave `N` values in the
interval `x` falls into. The first key either lands above `x`, fixing that interval and leaving the
rest ordinary, or below it, and the demand for `N` moves along. -/
def genGappedFor [Gen G] (g N : Nat) (x : Int) : Nat → Int → Int → G (List Int)
  | 0, _, _ => pure []
  | m + 1, lo, hi =>
    if hA : max (lo + (N : Int)) (x + 1) ≤ hi - ((m * (g + 1) + g : Nat) : Int) then
      if hB : lo + (g : Int) ≤ min (x - 1) (hi - ((m * (g + 1) + N : Nat) : Int)) then
        pick (fun () => genAboveX g m _ _ hi hA)
          (fun () => genBelowX (fun a => genGappedFor g N x m a hi) _ _ hB)
      else genAboveX g m _ _ hi hA
    else if hB : lo + (g : Int) ≤ min (x - 1) (hi - ((m * (g + 1) + N : Nat) : Int)) then
      genBelowX (fun a => genGappedFor g N x m a hi) _ _ hB
    else pure []

theorem genGappedFor_mem_support (g N : Nat) (hgN : g < N) (x : Int) :
    ∀ (m : Nat) (lo hi : Int) (ks : List Int), lo ≤ x → x ≤ hi → RoomFor g N m lo hi →
      (ks ∈ SPMF.support (genGappedFor g N x m lo hi : SPMF (List Int))
        ↔ ks.length = m ∧ GappedFor g N x lo hi ks) := by
  intro m
  induction m with
  | zero =>
    intro lo hi ks hlo hhi hroom
    rw [genGappedFor]
    support_simp
    unfold RoomFor at hroom
    push_cast at hroom
    constructor
    · rintro rfl
      exact ⟨rfl, by omega, hlo, hhi⟩
    · rintro ⟨hlen, -⟩
      exact List.length_eq_zero_iff.mp hlen
  | succ m ih =>
    intro lo hi ks hlo hhi hroom
    have hroom' : lo + ((m * (g + 1) + g : Nat) : Int) + N ≤ hi := by
      unfold RoomFor at hroom
      have hexp : ((m + 1) * (g + 1) + N : Nat) = (m * (g + 1) + g : Nat) + 1 + N := by ring
      rw [hexp] at hroom
      omega
    -- The two branches, and the two shapes of key list they produce.
    have hAiff : ∀ (hA : max (lo + (N : Int)) (x + 1) ≤ hi - ((m * (g + 1) + g : Nat) : Int)),
        (ks ∈ SPMF.support
            (genAboveX g m (max (lo + (N : Int)) (x + 1))
              (hi - ((m * (g + 1) + g : Nat) : Int)) hi hA : SPMF (List Int))
          ↔ ∃ k ks', ks = k :: ks' ∧ x < k ∧ lo + (N : Int) ≤ k ∧ ks'.length = m ∧
              Gapped g (k + 1) hi ks') := by
      intro hA
      simp only [genAboveX]
      support_simp
      constructor
      · rintro ⟨k, ⟨hk1, hk2⟩, ks', hmem, rfl⟩
        have hr : Room g m (k + 1) hi := by
          unfold Room
          push_cast at hk2 ⊢
          omega
        obtain ⟨hlen, hg⟩ := (genGapped_mem_support g m (k + 1) hi ks' hr).mp hmem
        exact ⟨k, ks', rfl, by omega, by omega, hlen, hg⟩
      · rintro ⟨k, ks', rfl, hxk, hNk, hlen, hg⟩
        have hr : Room g m (k + 1) hi := by
          have := hg.room
          rw [hlen] at this
          exact this
        refine ⟨k, ⟨by omega, ?_⟩, ks', ?_, rfl⟩
        · unfold Room at hr
          push_cast at hr ⊢
          omega
        · exact (genGapped_mem_support g m (k + 1) hi ks' hr).mpr ⟨hlen, hg⟩
    have hBiff : ∀ (hB : lo + (g : Int) ≤ min (x - 1) (hi - ((m * (g + 1) + N : Nat) : Int))),
        (ks ∈ SPMF.support
            (genBelowX (fun a => (genGappedFor g N x m a hi : SPMF (List Int))) (lo + (g : Int))
              (min (x - 1) (hi - ((m * (g + 1) + N : Nat) : Int))) hB)
          ↔ ∃ k ks', ks = k :: ks' ∧ k < x ∧ lo + (g : Int) ≤ k ∧ ks'.length = m ∧
              GappedFor g N x (k + 1) hi ks') := by
      intro hB
      simp only [genBelowX]
      support_simp
      constructor
      · rintro ⟨k, ⟨hk1, hk2⟩, ks', hmem, rfl⟩
        have hr : RoomFor g N m (k + 1) hi := by
          unfold RoomFor
          push_cast at hk2 ⊢
          omega
        obtain ⟨hlen, hg⟩ :=
          (ih (k + 1) hi ks' (by push_cast at hk2; omega) hhi hr).mp hmem
        exact ⟨k, ks', rfl, by push_cast at hk2; omega, hk1, hlen, hg⟩
      · rintro ⟨k, ks', rfl, hxk, hgk, hlen, hg⟩
        have hr : RoomFor g N m (k + 1) hi := by
          have := hg.room
          rw [hlen] at this
          exact this
        refine ⟨k, ⟨hgk, ?_⟩, ks', ?_, rfl⟩
        · unfold RoomFor at hr
          push_cast at hr ⊢
          omega
        · exact (ih (k + 1) hi ks' (by omega) hhi hr).mpr ⟨hlen, hg⟩
    have htarget : (ks.length = m + 1 ∧ GappedFor g N x lo hi ks) ↔
        ((∃ k ks', ks = k :: ks' ∧ x < k ∧ lo + (N : Int) ≤ k ∧ ks'.length = m ∧
            Gapped g (k + 1) hi ks') ∨
         (∃ k ks', ks = k :: ks' ∧ k < x ∧ lo + (g : Int) ≤ k ∧ ks'.length = m ∧
            GappedFor g N x (k + 1) hi ks')) := by
      constructor
      · rintro ⟨hlen, hg⟩
        match ks with
        | [] => simp at hlen
        | k :: ks' =>
          unfold GappedFor at hg
          simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
          split at hg
          · exact Or.inl ⟨k, ks', rfl, by assumption, hg.1, hlen, hg.2.2⟩
          · exact Or.inr ⟨k, ks', rfl, hg.2.1, hg.1, hlen, hg.2.2⟩
      · rintro (⟨k, ks', rfl, hxk, hNk, hlen, hg⟩ | ⟨k, ks', rfl, hxk, hgk, hlen, hg⟩)
        · refine ⟨by simp [hlen], ?_⟩
          unfold GappedFor
          rw [if_pos hxk]
          exact ⟨hNk, hlo, hg⟩
        · refine ⟨by simp [hlen], ?_⟩
          unfold GappedFor
          rw [if_neg (by omega)]
          exact ⟨hgk, hxk, hg⟩
    rw [genGappedFor]
    split_ifs with hA hB hB
    · support_simp
      rw [hAiff hA, hBiff hB, htarget]
    · rw [hAiff hA, htarget]
      constructor
      · exact Or.inl
      · rintro (h | ⟨k, ks', rfl, hxk, hgk, hlen, hg⟩)
        · exact h
        · exfalso
          have := hg.room
          rw [hlen] at this
          unfold RoomFor at this
          push_cast at this
          exact hB (by push_cast; omega)
    · rw [hBiff hB, htarget]
      constructor
      · exact Or.inr
      · rintro (⟨k, ks', rfl, hxk, hNk, hlen, hg⟩ | h)
        · exfalso
          have := hg.room
          rw [hlen] at this
          unfold Room at this
          push_cast at this
          exact hA (by push_cast; omega)
        · exact h
    · exfalso
      omega

/-! ## Generating the trees `x` splits -/

theorem gap_lt_xgapAt (t h : Nat) : gap t h < xgapAt t h := by
  cases h <;> simp only [gap, xgapAt] <;> omega

/-- Generates one path node's keys: a key count in `[kmin, 2t-1]`, then that many keys missing `x`
and leaving `x`'s child the room it needs. -/
def genKeysFor [Gen G] (t kmin h : Nat) (x lo hi : Int) : G (List Int) := do
  let m ← chooseNat kmin (max kmin (2 * t - 1)) (le_max_left _ _)
  genGappedFor (gap t h) (xgapAt t h) x
    (if RoomFor (gap t h) (xgapAt t h) m lo hi then m else kmin) lo hi

theorem genKeysFor_mem_support (hkm : kmin ≤ 2 * t - 1) (hlo : lo ≤ x) (hhi : x ≤ hi)
    (hfit : RoomFor (gap t h) (xgapAt t h) kmin lo hi) (ks : List Int) :
    ks ∈ SPMF.support (genKeysFor t kmin h x lo hi : SPMF (List Int))
      ↔ kmin ≤ ks.length ∧ ks.length ≤ 2 * t - 1 ∧
          GappedFor (gap t h) (xgapAt t h) x lo hi ks := by
  have hmax : max kmin (2 * t - 1) = 2 * t - 1 := max_eq_right hkm
  have hgN := gap_lt_xgapAt t h
  unfold genKeysFor
  support_simp
  rw [hmax]
  constructor
  · rintro ⟨m, ⟨hm1, hm2⟩, hmem⟩
    by_cases hr : RoomFor (gap t h) (xgapAt t h) m lo hi
    · rw [if_pos hr] at hmem
      obtain ⟨hlen, hg⟩ :=
        (genGappedFor_mem_support _ _ hgN x m lo hi ks hlo hhi hr).mp hmem
      exact ⟨by omega, by omega, hg⟩
    · rw [if_neg hr] at hmem
      obtain ⟨hlen, hg⟩ :=
        (genGappedFor_mem_support _ _ hgN x kmin lo hi ks hlo hhi hfit).mp hmem
      exact ⟨by omega, by omega, hg⟩
  · rintro ⟨hmin, hmaxlen, hg⟩
    refine ⟨ks.length, ⟨hmin, hmaxlen⟩, ?_⟩
    rw [if_pos hg.room]
    exact (genGappedFor_mem_support _ _ hgN x ks.length lo hi ks hlo hhi hg.room).mpr ⟨rfl, hg⟩

/-- Generates the children of a node on `x`'s path: the one whose interval contains `x` continues
the path, the others are ordinary subtrees. -/
def genChildrenFor [Gen G] (gen genx : Int → Int → G Tree) (x : Int) :
    Int → Int → List Int → G (List Tree)
  | lo, hi, [] => do
      let c ← genx lo hi
      return [c]
  | lo, hi, k :: ks =>
      if x < k then do
        let c ← genx lo (k - 1)
        let cs ← genChildren gen (k + 1) hi ks
        return c :: cs
      else do
        let c ← gen lo (k - 1)
        let cs ← genChildrenFor gen genx x (k + 1) hi ks
        return c :: cs

theorem genChildrenFor_mem_support {gen genx : Int → Int → SPMF Tree}
    {P : Int → Int → Tree → Prop} {Q : Tree → Prop} {g N : Nat} {x : Int}
    (hgen : ∀ a b c, a + (g : Int) ≤ b + 1 → (c ∈ SPMF.support (gen a b) ↔ P a b c))
    (hgenx : ∀ a b c, a ≤ x → x ≤ b → a + (N : Int) ≤ b + 1 →
      (c ∈ SPMF.support (genx a b) ↔ P a b c ∧ Q c)) :
    ∀ (ks : List Int) (lo hi : Int) (cs : List Tree), GappedFor g N x lo hi ks →
      (cs ∈ SPMF.support (genChildrenFor gen genx x lo hi ks) ↔ ForestFor P Q x lo hi ks cs) := by
  intro ks
  induction ks with
  | nil =>
    intro lo hi cs hks
    rw [genChildrenFor]
    support_simp
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact (hgenx lo hi c hks.2.1 hks.2.2 hks.1).mp hc
    · intro hf
      match cs with
      | [c] => exact ⟨c, (hgenx lo hi c hks.2.1 hks.2.2 hks.1).mpr hf, rfl⟩
      | [] => exact absurd hf not_false
      | _ :: _ :: _ => exact absurd hf not_false
  | cons k ks ih =>
    intro lo hi cs hks
    unfold GappedFor at hks
    rw [genChildrenFor]
    unfold ForestFor
    split at hks
    · rename_i hlt
      obtain ⟨hk, hlox, htl⟩ := hks
      rw [if_pos hlt]
      support_simp
      match cs with
      | [] => simp
      | c :: cs' =>
        simp only [if_pos hlt, List.cons.injEq]
        constructor
        · rintro ⟨c₀, hc, cs₀, hcs, rfl, rfl⟩
          exact ⟨(hgenx lo (k - 1) c hlox (by omega) (by omega)).mp hc,
            (genChildren_mem_support hgen ks (k + 1) hi cs' htl).mp hcs⟩
        · rintro ⟨hc, hcs⟩
          exact ⟨c, (hgenx lo (k - 1) c hlox (by omega) (by omega)).mpr hc, cs',
            (genChildren_mem_support hgen ks (k + 1) hi cs' htl).mpr hcs, rfl, rfl⟩
    · rename_i hnlt
      obtain ⟨hk, hkx, htl⟩ := hks
      rw [if_neg hnlt]
      support_simp
      match cs with
      | [] => simp
      | c :: cs' =>
        simp only [if_neg hnlt, List.cons.injEq]
        constructor
        · rintro ⟨c₀, hc, cs₀, hcs, rfl, rfl⟩
          exact ⟨(hgen lo (k - 1) c (by omega)).mp hc, (ih (k + 1) hi cs' htl).mp hcs⟩
        · rintro ⟨hc, hcs⟩
          exact ⟨c, (hgen lo (k - 1) c (by omega)).mpr hc, cs',
            (ih (k + 1) hi cs' htl).mpr hcs, rfl, rfl⟩

/-- Generates a height-`h` B-tree that `x` splits: fill the leaf on `x`'s path, and keep every node
along the way clear of `x`. -/
def genFull [Gen G] (t kmin : Nat) (x : Int) : Nat → Int → Int → G Tree
  | 0, lo, hi => do
      let ks ← genGappedFor 0 1 x (2 * t - 1) lo hi
      return ⟨ks, []⟩
  | h + 1, lo, hi => do
      let ks ← genKeysFor t kmin (h + 1) x lo hi
      let cs ← genChildrenFor (fun a b => genNode t (t - 1) h a b)
        (fun a b => genFull t (t - 1) x h a b) x lo hi ks
      return ⟨ks, cs⟩

theorem genFull_mem_support {t : Nat} {x : Int} (ht : 1 ≤ t) :
    ∀ (h kmin : Nat) (lo hi : Int) (tr : Tree), kmin ≤ 2 * t - 1 → lo ≤ x → x ≤ hi →
      XFits t kmin h lo hi →
      (tr ∈ SPMF.support (genFull t kmin x h lo hi : SPMF Tree)
        ↔ Tree.IsBTreeAt t kmin h lo hi tr ∧ Tree.SplitsOn t x h tr) := by
  intro h
  induction h with
  | zero =>
    rintro kmin lo hi ⟨ks, cs⟩ hkm hlo hhi hfit
    have hroom : RoomFor 0 1 (2 * t - 1) lo hi := by
      unfold RoomFor
      unfold XFits xNeed at hfit
      push_cast at hfit ⊢
      omega
    rw [genFull]
    support_simp [genGappedFor_mem_support 0 1 (by omega) x (2 * t - 1) lo hi _ hlo hhi hroom,
      Tree.IsBTreeAt, Tree.SplitsOn, Tree.mk.injEq]
    constructor
    · rintro ⟨ks', ⟨hlen, hg⟩, rfl, rfl⟩
      exact ⟨⟨rfl, by omega, by omega, hg.gapped (by omega)⟩, hg.notMem, hlen⟩
    · rintro ⟨⟨rfl, -, -, hg⟩, hx, hlen⟩
      exact ⟨ks, ⟨hlen, GappedFor.of_gapped_one hlo hhi hx hg⟩, rfl, rfl⟩
  | succ h ih =>
    rintro kmin lo hi ⟨ks, cs⟩ hkm hlo hhi hfit
    have hfit' : RoomFor (gap t (h + 1)) (xgapAt t (h + 1)) kmin lo hi := hfit
    have hgen : ∀ a b c, a + (gap t (h + 1) : Int) ≤ b + 1 →
        (c ∈ SPMF.support (genNode t (t - 1) h a b : SPMF Tree)
          ↔ Tree.IsBTreeAt t (t - 1) h a b c) := by
      intro a b c hab
      refine genNode_mem_support h (t - 1) a b c (by omega) ?_
      unfold Fits Room
      rw [gap] at hab
      push_cast at hab ⊢
      omega
    have hgenx : ∀ a b c, a ≤ x → x ≤ b → a + (xgapAt t (h + 1) : Int) ≤ b + 1 →
        (c ∈ SPMF.support (genFull t (t - 1) x h a b : SPMF Tree)
          ↔ Tree.IsBTreeAt t (t - 1) h a b c ∧ Tree.SplitsOn t x h c) := by
      intro a b c hax hxb hab
      refine ih (t - 1) a b c (by omega) hax hxb ?_
      unfold XFits
      rw [xNeed_nonroot ht]
      exact hab
    rw [genFull]
    support_simp [genKeysFor_mem_support hkm hlo hhi hfit', Tree.IsBTreeAt, Tree.SplitsOn,
      Tree.mk.injEq]
    constructor
    · rintro ⟨ks', ⟨h1, h2, h3⟩, cs', hcs, rfl, rfl⟩
      have hff := (genChildrenFor_mem_support hgen hgenx ks lo hi cs h3).mp hcs
      obtain ⟨hforest, c, hc, hq⟩ := (forestFor_iff ks cs lo hi).mp hff
      exact ⟨⟨h1, h2, (h3.gapped (le_of_lt (gap_lt_xgapAt t (h + 1)))).mono (Nat.zero_le _),
        hforest⟩, h3.notMem, c, hc, hq⟩
    · rintro ⟨⟨h1, h2, h3, hforest⟩, hx, c, hc, hq⟩
      have hff : ForestFor (fun a b c => Tree.IsBTreeAt t (t - 1) h a b c)
          (fun c => Tree.SplitsOn t x h c) x lo hi ks cs :=
        (forestFor_iff ks cs lo hi).mpr ⟨hforest, c, hc, hq⟩
      have hgf : GappedFor (gap t (h + 1)) (xgapAt t (h + 1)) x lo hi ks := by
        refine GappedFor.of_forestFor ?_ ?_ ks cs lo hi hx hlo hhi hff
        · intro a b c hc
          have := Tree.IsBTreeAt.fits h (t - 1) a b c hc
          unfold Fits Room at this
          rw [gap]
          push_cast at this ⊢
          omega
        · intro a b c hc hq ha hb
          have := Tree.IsBTreeAt.xfits ht h (t - 1) a b c hc hq ha hb
          unfold XFits at this
          rw [xNeed_nonroot ht] at this
          exact this
      exact ⟨ks, ⟨h1, h2, hgf⟩, cs,
        (genChildrenFor_mem_support hgen hgenx ks lo hi cs hgf).mpr hff, rfl, rfl⟩

/-- Generates a B-tree of order `t` with keys in `[lo, hi]` and every leaf at depth `h` that
inserting `x` splits. -/
def genSplitting [Gen G] (t h : Nat) (x lo hi : Int) : G Tree := genFull t (min 1 h) x h lo hi

theorem genSplitting_mem_support (ht : 2 ≤ t) (hlo : lo ≤ x) (hhi : x ≤ hi)
    (hfit : XFits t (min 1 h) h lo hi) (tr : Tree) :
    tr ∈ SPMF.support (genSplitting t h x lo hi : SPMF Tree)
      ↔ Tree.IsBTree t h lo hi tr ∧ Tree.SplitsOn t x h tr :=
  genFull_mem_support (by omega) h (min 1 h) lo hi tr (by omega) hlo hhi hfit

theorem genSplitting.sound_complete (ht : 2 ≤ t) (hlo : lo ≤ x) (hhi : x ≤ hi)
    (hfit : XFits t (min 1 h) h lo hi) :
    IsSoundAndComplete (genSplitting t h x lo hi : SPMF Tree)
      (fun tr => Tree.IsBTree t h lo hi tr ∧ Tree.SplitsOn t x h tr) :=
  genSplitting_mem_support ht hlo hhi hfit

/-! ## Walking `x`'s path -/

theorem childFor_mem {x : Int} : ∀ (ks : List Int) (cs : List Tree) (c : Tree),
    childFor x ks cs = some c → c ∈ cs := by
  intro ks
  induction ks with
  | nil =>
    intro cs c hc
    match cs with
    | [c₀] => simp only [childFor, Option.some.injEq] at hc; simp [hc]
    | [] => simp [childFor] at hc
    | _ :: _ :: _ => simp [childFor] at hc
  | cons k ks ih =>
    intro cs c hc
    match cs with
    | [] => simp [childFor] at hc
    | c₀ :: cs' =>
      simp only [childFor] at hc
      split at hc
      · simp only [Option.some.injEq] at hc
        simp [hc]
      · exact List.mem_cons_of_mem _ (ih cs' c hc)

theorem Forest.childFor_some {P : Int → Int → Tree → Prop} {x : Int} :
    ∀ (ks : List Int) (cs : List Tree) (lo hi : Int), Forest P lo hi ks cs →
      ∃ c, childFor x ks cs = some c := by
  intro ks
  induction ks with
  | nil =>
    intro cs lo hi hf
    match cs with
    | [c] => exact ⟨c, rfl⟩
    | [] => exact absurd hf not_false
    | _ :: _ :: _ => exact absurd hf not_false
  | cons k ks ih =>
    intro cs lo hi hf
    match cs with
    | [] => exact absurd hf not_false
    | c :: cs' =>
      simp only [childFor]
      split
      · exact ⟨c, rfl⟩
      · exact ih cs' (k + 1) hi hf.2

/-- Every child sits inside its parent's interval. -/
theorem Forest.mem_interval {P : Int → Int → Tree → Prop} :
    ∀ (ks : List Int) (cs : List Tree) (lo hi : Int), Gapped 0 lo hi ks →
      Forest P lo hi ks cs → ∀ c ∈ cs, ∃ a b, P a b c ∧ lo ≤ a ∧ b ≤ hi := by
  intro ks
  induction ks with
  | nil =>
    intro cs lo hi _ hf
    match cs with
    | [c] =>
      intro c' hc'
      rw [List.mem_singleton.mp hc']
      exact ⟨lo, hi, hf, le_rfl, le_rfl⟩
    | [] => exact absurd hf not_false
    | _ :: _ :: _ => exact absurd hf not_false
  | cons k ks ih =>
    intro cs lo hi hg hf
    match cs with
    | [] => exact absurd hf not_false
    | c :: cs' =>
      obtain ⟨hk, htl⟩ := hg
      obtain ⟨hc, hrest⟩ := hf
      intro c' hc'
      rcases List.mem_cons.mp hc' with rfl | hc'
      · exact ⟨lo, k - 1, hc, le_rfl, by have := htl.lo_le; omega⟩
      · obtain ⟨a, b, hP, ha, hb⟩ := ih cs' (k + 1) hi htl hrest c' hc'
        exact ⟨a, b, hP, by omega, hb⟩

/-! ## Insertion really splits -/

theorem insSorted_length_le (x : Int) (ks : List Int) :
    (insSorted x ks).length ≤ ks.length + 1 := by
  induction ks with
  | nil => simp [insSorted]
  | cons k ks ih =>
    simp only [insSorted]
    split
    · simp
    · split
      · simpa using ih
      · simp

theorem insSorted_length {x : Int} {ks : List Int} (h : x ∉ ks) :
    (insSorted x ks).length = ks.length + 1 := by
  induction ks with
  | nil => simp [insSorted]
  | cons k ks ih =>
    simp only [List.mem_cons, not_or] at h
    simp only [insSorted]
    split
    · simp
    · split
      · simpa using ih h.2
      · omega

/-- A full leaf overflows: the leaf case of `insertAt` splits. -/
theorem insertAt_leaf_split {t : Nat} {x : Int} {ks : List Int} {cs : List Tree}
    (hx : x ∉ ks) (hlen : ks.length = 2 * t - 1) :
    ∃ l k r, insertAt t x 0 ⟨ks, cs⟩ = Ins.split l k r := by
  simp only [insertAt, mkNode]
  rw [if_neg (by rw [insSorted_length hx, hlen]; omega)]
  exact ⟨_, _, _, rfl⟩

/-- A leaf with a key to spare absorbs the new key instead. -/
theorem insertAt_leaf_keep {t : Nat} {x : Int} {ks : List Int} {cs : List Tree}
    (hlen : ks.length < 2 * t - 1) :
    ∃ tr, insertAt t x 0 ⟨ks, cs⟩ = Ins.keep tr := by
  simp only [insertAt, mkNode]
  rw [if_pos (by have := insSorted_length_le x ks; omega)]
  exact ⟨_, rfl⟩

/-- `Tree.SplitsOn` says what it is named for. Its two clauses are a *shape* condition — the search
for `x` meets no key equal to `x`, and the leaf it reaches holds `2t-1` keys — and this is exactly
the condition under which the real insertion, run on the leaf the search reaches, splits it. -/
theorem Tree.splitsOn_iff {t : Nat} {x : Int} :
    ∀ (h kmin : Nat) (lo hi : Int) (tr : Tree), Tree.IsBTreeAt t kmin h lo hi tr →
      (Tree.SplitsOn t x h tr ↔
        Tree.PathMisses x h tr ∧
          ∃ ks cs l k r, leafFor x h tr = some ⟨ks, cs⟩ ∧
            insertAt t x 0 ⟨ks, cs⟩ = Ins.split l k r) := by
  intro h
  induction h with
  | zero =>
    rintro kmin lo hi ⟨ks, cs⟩ ⟨-, -, hmax, -⟩
    constructor
    · rintro ⟨hx, hlen⟩
      obtain ⟨l, k, r, hs⟩ := insertAt_leaf_split (cs := cs) hx hlen
      exact ⟨hx, ks, cs, l, k, r, rfl, hs⟩
    · rintro ⟨hx, ks', cs', l, k, r, hleaf, hins⟩
      simp only [leafFor, Option.some.injEq, Tree.mk.injEq] at hleaf
      obtain ⟨rfl, rfl⟩ := hleaf
      refine ⟨hx, ?_⟩
      have hlt : ¬ ks.length < 2 * t - 1 := by
        intro hlt
        obtain ⟨tr', hkeep⟩ := insertAt_leaf_keep (t := t) (x := x) (cs := cs) hlt
        rw [hkeep] at hins
        exact Ins.noConfusion hins
      omega
  | succ h ih =>
    rintro kmin lo hi ⟨ks, cs⟩ ⟨-, -, hg, hforest⟩
    have hchild : ∀ c, childFor x ks cs = some c →
        ∃ a b, Tree.IsBTreeAt t (t - 1) h a b c := by
      intro c hc
      obtain ⟨a, b, hval, -, -⟩ :=
        Forest.mem_interval ks cs lo hi hg hforest c (childFor_mem ks cs c hc)
      exact ⟨a, b, hval⟩
    constructor
    · rintro ⟨hx, c, hc, hsp⟩
      obtain ⟨a, b, hval⟩ := hchild c hc
      obtain ⟨hpm, ks', cs', l, k, r, hleaf, hins⟩ := (ih (t - 1) a b c hval).mp hsp
      exact ⟨⟨hx, c, hc, hpm⟩, ks', cs', l, k, r, by simp [leafFor, hc, hleaf], hins⟩
    · rintro ⟨⟨hx, c, hc, hpm⟩, ks', cs', l, k, r, hleaf, hins⟩
      obtain ⟨a, b, hval⟩ := hchild c hc
      simp only [leafFor, hc, Option.bind_some] at hleaf
      exact ⟨hx, c, hc, (ih (t - 1) a b c hval).mpr ⟨hpm, ks', cs', l, k, r, hleaf, hins⟩⟩

theorem Tree.SplitsOn.pathMisses {t : Nat} {x : Int} :
    ∀ (h : Nat) (tr : Tree), Tree.SplitsOn t x h tr → Tree.PathMisses x h tr := by
  intro h
  induction h with
  | zero => rintro ⟨ks, cs⟩ ⟨hx, -⟩; exact hx
  | succ h ih =>
    rintro ⟨ks, cs⟩ ⟨hx, c, hc, hsp⟩
    exact ⟨hx, c, hc, ih c hsp⟩

/-! ## Absence

The trees `x` splits are the ones the paper inserts a *fresh* key into: missing every key on the
search path is, for a valid B-tree, the same as missing every key.
-/

theorem Tree.HasKey.interval {t : Nat} {x : Int} :
    ∀ (h kmin : Nat) (lo hi : Int) (tr : Tree), Tree.IsBTreeAt t kmin h lo hi tr →
      Tree.HasKey x h tr → lo ≤ x ∧ x ≤ hi := by
  intro h
  induction h with
  | zero =>
    rintro kmin lo hi ⟨ks, cs⟩ ⟨-, -, -, hg⟩ hk
    exact ⟨hg.le_of_mem x hk, hg.le_hi x hk⟩
  | succ h ih =>
    rintro kmin lo hi ⟨ks, cs⟩ ⟨-, -, hg, hforest⟩ hk
    rcases hk with hk | ⟨c, hc, hk⟩
    · exact ⟨hg.le_of_mem x hk, hg.le_hi x hk⟩
    · obtain ⟨a, b, hval, ha, hb⟩ := Forest.mem_interval ks cs lo hi hg hforest c hc
      have := ih (t - 1) a b c hval hk
      omega

/-- Off the search path there is no `x` to find: the other children's intervals are on the wrong
side of the key the search compared `x` against. -/
theorem Forest.not_hasKey_off_path {P : Int → Int → Tree → Prop} {x : Int} {hh : Nat}
    (hP : ∀ a b c, P a b c → Tree.HasKey x hh c → a ≤ x ∧ x ≤ b) :
    ∀ (ks : List Int) (cs : List Tree) (lo hi : Int) (c : Tree), Gapped 0 lo hi ks → x ∉ ks →
      Forest P lo hi ks cs → childFor x ks cs = some c → ¬ Tree.HasKey x hh c →
      ∀ c' ∈ cs, ¬ Tree.HasKey x hh c' := by
  intro ks
  induction ks with
  | nil =>
    intro cs lo hi c _ _ hf hc hnk
    match cs with
    | [c₀] =>
      simp only [childFor, Option.some.injEq] at hc
      intro c' hc'
      rw [List.mem_singleton.mp hc', hc]
      exact hnk
    | [] => exact absurd hf not_false
    | _ :: _ :: _ => exact absurd hf not_false
  | cons k ks ih =>
    intro cs lo hi c hg hx hf hc hnk
    match cs with
    | [] => exact absurd hf not_false
    | c₀ :: cs' =>
      obtain ⟨hk, htl⟩ := hg
      obtain ⟨hc₀, hrest⟩ := hf
      simp only [List.mem_cons, not_or] at hx
      simp only [childFor] at hc
      split at hc
      · rename_i hlt
        simp only [Option.some.injEq] at hc
        intro c' hc'
        rcases List.mem_cons.mp hc' with rfl | hc'
        · rw [hc]; exact hnk
        · intro hk'
          obtain ⟨a, b, hP', ha, -⟩ := Forest.mem_interval ks cs' (k + 1) hi htl hrest c' hc'
          have := hP a b c' hP' hk'
          omega
      · rename_i hnlt
        have hkx : k < x := by
          have : x ≠ k := hx.1
          omega
        intro c' hc'
        rcases List.mem_cons.mp hc' with rfl | hc'
        · intro hk'
          have := hP lo (k - 1) c' hc₀ hk'
          omega
        · exact ih cs' (k + 1) hi c htl hx.2 hrest hc hnk c' hc'

/-- For a valid B-tree, the search path is the only place `x` could be. -/
theorem Tree.pathMisses_iff_not_hasKey {t : Nat} {x : Int} :
    ∀ (h kmin : Nat) (lo hi : Int) (tr : Tree), Tree.IsBTreeAt t kmin h lo hi tr →
      (Tree.PathMisses x h tr ↔ ¬ Tree.HasKey x h tr) := by
  intro h
  induction h with
  | zero => rintro kmin lo hi ⟨ks, cs⟩ -; exact Iff.rfl
  | succ h ih =>
    rintro kmin lo hi ⟨ks, cs⟩ ⟨-, -, hg, hforest⟩
    have hchild : ∀ c ∈ cs, ∃ a b, Tree.IsBTreeAt t (t - 1) h a b c := by
      intro c hc
      obtain ⟨a, b, hval, -, -⟩ := Forest.mem_interval ks cs lo hi hg hforest c hc
      exact ⟨a, b, hval⟩
    constructor
    · rintro ⟨hx, c, hc, hpm⟩
      obtain ⟨a, b, hval⟩ := hchild c (childFor_mem ks cs c hc)
      have hnk : ¬ Tree.HasKey x h c := (ih (t - 1) a b c hval).mp hpm
      have hoff := Forest.not_hasKey_off_path
        (fun a b c hP hk => Tree.HasKey.interval h (t - 1) a b c hP hk)
        ks cs lo hi c hg hx hforest hc hnk
      rintro (hk | ⟨c', hc', hk⟩)
      · exact hx hk
      · exact hoff c' hc' hk
    · intro hnk
      simp only [Tree.HasKey, not_or, not_exists] at hnk
      obtain ⟨c, hc⟩ := Forest.childFor_some (x := x) ks cs lo hi hforest
      obtain ⟨a, b, hval⟩ := hchild c (childFor_mem ks cs c hc)
      refine ⟨hnk.1, c, hc, (ih (t - 1) a b c hval).mpr ?_⟩
      intro hk
      exact hnk.2 c ⟨childFor_mem ks cs c hc, hk⟩

/-- The key a generated tree splits on is fresh: it is none of the tree's keys. -/
theorem Tree.SplitsOn.not_hasKey {t kmin h : Nat} {x lo hi : Int} {tr : Tree}
    (hv : Tree.IsBTreeAt t kmin h lo hi tr) (hs : Tree.SplitsOn t x h tr) :
    ¬ Tree.HasKey x h tr :=
  (Tree.pathMisses_iff_not_hasKey h kmin lo hi tr hv).mp (Tree.SplitsOn.pathMisses h tr hs)

end BTree
