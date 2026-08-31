/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt
import BasaltExamples.BTree.Def

open RandomChoice

/-!
# B-Trees

`genBTree t h lo hi` generates the B-trees of order `t` with keys in `[lo, hi]` and every leaf
at depth `h`, by choosing each node's keys and recursing on the intervals they cut out. The keys
must be spread far enough apart to leave every child room for its own minimum load, which is what
`gap` measures and `Room` asserts; the law holds on any interval with room for the whole tree.
-/

namespace BTree

/-! ## Room -/

/-- The width of the interval a height-`h` subtree of a tree of order `t` reserves for each of its
children: the least number of keys such a child can hold. -/
def gap (t : Nat) : Nat → Nat
  | 0 => 0
  | h + 1 => (t - 1) * (gap t h + 1) + gap t h

/-- `[lo, hi]` has room for `m` keys spaced `g` apart, with a gap at each end. -/
def Room (g m : Nat) (lo hi : Int) : Prop := lo + (m * (g + 1) + g : Nat) ≤ hi + 1

instance : Decidable (Room g m lo hi) := by unfold Room; infer_instance

/-- `[lo, hi]` has room for a height-`h` subtree of order `t` whose root holds `kmin` keys. -/
def Fits (t kmin h : Nat) (lo hi : Int) : Prop := Room (gap t h) kmin lo hi

theorem Room.mono (hle : m' ≤ m) (h : Room g m lo hi) : Room g m' lo hi := by
  unfold Room at *
  have : (m' * (g + 1) + g : Nat) ≤ (m * (g + 1) + g : Nat) := by
    have := Nat.mul_le_mul_right (g + 1) hle
    omega
  omega

/-- A gapped key list leaves room for itself. -/
theorem Gapped.room (h : Gapped g lo hi ks) : Room g ks.length lo hi := by
  induction ks generalizing lo with
  | nil => simpa [Gapped, Room] using h
  | cons k ks ih =>
    obtain ⟨hk, htl⟩ := h
    have hrec := ih htl
    unfold Room at *
    have hexp : ((ks.length + 1) * (g + 1) + g : Nat)
        = (ks.length * (g + 1) + g : Nat) + (g + 1) := by ring
    simp only [List.length_cons, hexp]
    push_cast at hrec ⊢
    omega

/-- Gapped keys lie above the interval's lower end. -/
theorem Gapped.le_of_mem (h : Gapped g lo hi ks) : ∀ y ∈ ks, lo ≤ y := by
  induction ks generalizing lo with
  | nil => simp
  | cons k ks ih =>
    obtain ⟨hk, htl⟩ := h
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · omega
    · have := ih htl y hy
      omega

/-- A gapped interval is not empty of positions. -/
theorem Gapped.lo_le (h : Gapped g lo hi ks) : lo ≤ hi + 1 := by
  induction ks generalizing lo with
  | nil => simp only [Gapped] at h; omega
  | cons k ks ih =>
    obtain ⟨hk, htl⟩ := h
    have := ih htl
    omega

/-- Gapped keys lie below the interval's upper end. -/
theorem Gapped.le_hi (h : Gapped g lo hi ks) : ∀ y ∈ ks, y ≤ hi := by
  induction ks generalizing lo with
  | nil => simp
  | cons k ks ih =>
    obtain ⟨hk, htl⟩ := h
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · have := htl.lo_le
      omega
    · exact ih htl y hy

/-- Wider gaps are a stronger requirement. -/
theorem Gapped.mono (hle : g' ≤ g) (h : Gapped g lo hi ks) : Gapped g' lo hi ks := by
  induction ks generalizing lo with
  | nil => simp only [Gapped] at *; omega
  | cons k ks ih =>
    obtain ⟨hk, htl⟩ := h
    exact ⟨by omega, ih htl⟩

/-- Children that each need `g` values of their own force their separating keys `g` apart. -/
theorem Gapped.of_forest {P : Int → Int → Tree → Prop} {g : Nat}
    (hP : ∀ a b c, P a b c → a + (g : Int) ≤ b + 1)
    {lo hi : Int} {ks : List Int} {cs : List Tree} (h : Forest P lo hi ks cs) :
    Gapped g lo hi ks := by
  induction ks generalizing lo cs with
  | nil =>
    match cs with
    | [c] => exact hP _ _ _ h
    | [] => exact absurd h not_false
    | _ :: _ :: _ => exact absurd h not_false
  | cons k ks ih =>
    match cs with
    | [] => exact absurd h not_false
    | c :: cs =>
      obtain ⟨hc, htl⟩ := h
      exact ⟨by have := hP _ _ _ hc; omega, ih htl⟩

/-- Every valid subtree needs the room its minimum load takes up. -/
theorem Tree.IsBTreeAt.fits : ∀ (h kmin : Nat) (lo hi : Int) (tr : Tree),
    Tree.IsBTreeAt t kmin h lo hi tr → Fits t kmin h lo hi := by
  intro h
  induction h with
  | zero =>
    rintro kmin lo hi ⟨ks, cs⟩ ⟨-, hmin, -, hg⟩
    exact Room.mono hmin hg.room
  | succ h ih =>
    rintro kmin lo hi ⟨ks, cs⟩ ⟨hmin, -, -, hforest⟩
    refine Room.mono hmin (Gapped.room (Gapped.of_forest ?_ hforest))
    intro a b c hc
    have := ih (t - 1) a b c hc
    unfold Fits Room at this
    rw [gap]
    push_cast at this ⊢
    omega

/-! ## Generators -/

/-- Generates `m` keys spaced `g` apart inside `[lo, hi]`, leaving a gap of `g` at each end. -/
def genGapped [Gen G] (g : Nat) : Nat → Int → Int → G (List Int)
  | 0, _, _ => pure []
  | m + 1, lo, hi =>
    if h : lo + (g : Int) ≤ hi - (m * (g + 1) + g : Nat) then do
      let k ← chooseInt (lo + g) (hi - (m * (g + 1) + g : Nat)) h
      let ks ← genGapped g m (k + 1) hi
      return k :: ks
    else
      pure []

theorem genGapped_mem_support (g : Nat) : ∀ (m : Nat) (lo hi : Int) (ks : List Int),
    Room g m lo hi →
    (ks ∈ SPMF.support (genGapped g m lo hi : SPMF (List Int))
      ↔ ks.length = m ∧ Gapped g lo hi ks) := by
  intro m
  induction m with
  | zero =>
    intro lo hi ks hroom
    rw [genGapped]
    support_simp
    unfold Room at hroom
    push_cast at hroom
    constructor
    · rintro rfl
      exact ⟨rfl, by simp only [Gapped]; omega⟩
    · rintro ⟨hlen, -⟩
      exact List.length_eq_zero_iff.mp hlen
  | succ m ih =>
    intro lo hi ks hroom
    have hexp : (((m + 1) * (g + 1) + g : Nat) : Int)
        = ((m * (g + 1) + g : Nat) : Int) + (g + 1) := by push_cast; ring
    have hd : lo + (g : Int) ≤ hi - (m * (g + 1) + g : Nat) := by
      unfold Room at hroom
      rw [hexp] at hroom
      omega
    rw [genGapped, dif_pos hd]
    support_simp
    constructor
    · rintro ⟨k, ⟨hk1, hk2⟩, ks', hmem, rfl⟩
      have hroom' : Room g m (k + 1) hi := by
        unfold Room
        push_cast at hk2 ⊢
        omega
      obtain ⟨hlen, hg⟩ := (ih (k + 1) hi ks' hroom').mp hmem
      exact ⟨by simp [hlen], by omega, hg⟩
    · rintro ⟨hlen, hg⟩
      match ks with
      | [] => simp at hlen
      | k :: ks' =>
        obtain ⟨hk, hg'⟩ := hg
        have hlen' : ks'.length = m := by simpa using hlen
        have hroom' := hg'.room
        rw [hlen'] at hroom'
        refine ⟨k, ⟨by omega, ?_⟩, ks', (ih (k + 1) hi ks' hroom').mpr ⟨hlen', hg'⟩, rfl⟩
        unfold Room at hroom'
        push_cast at hroom' ⊢
        omega

/-- Generates one node's keys: a key count in `[kmin, 2t-1]`, then that many keys, spaced far
enough apart to leave every child its own room. A count the interval cannot hold falls back to
`kmin`, which it always can. -/
def genKeys [Gen G] (t kmin h : Nat) (lo hi : Int) : G (List Int) := do
  let m ← chooseNat kmin (max kmin (2 * t - 1)) (le_max_left _ _)
  genGapped (gap t h) (if Room (gap t h) m lo hi then m else kmin) lo hi

theorem genKeys_mem_support (hkm : kmin ≤ 2 * t - 1) (hfit : Fits t kmin h lo hi)
    (ks : List Int) :
    ks ∈ SPMF.support (genKeys t kmin h lo hi : SPMF (List Int))
      ↔ kmin ≤ ks.length ∧ ks.length ≤ 2 * t - 1 ∧ Gapped (gap t h) lo hi ks := by
  have hmax : max kmin (2 * t - 1) = 2 * t - 1 := max_eq_right hkm
  unfold genKeys
  support_simp
  rw [hmax]
  constructor
  · rintro ⟨m, ⟨hm1, hm2⟩, hmem⟩
    by_cases hr : Room (gap t h) m lo hi
    · rw [if_pos hr] at hmem
      obtain ⟨hlen, hg⟩ := (genGapped_mem_support _ m lo hi ks hr).mp hmem
      exact ⟨by omega, by omega, hg⟩
    · rw [if_neg hr] at hmem
      obtain ⟨hlen, hg⟩ := (genGapped_mem_support _ kmin lo hi ks hfit).mp hmem
      exact ⟨by omega, by omega, hg⟩
  · rintro ⟨hmin, hmaxlen, hg⟩
    refine ⟨ks.length, ⟨hmin, hmaxlen⟩, ?_⟩
    rw [if_pos hg.room]
    exact (genGapped_mem_support _ ks.length lo hi ks hg.room).mpr ⟨rfl, hg⟩

/-- Generates the children of a node: one per interval that `ks` cuts out of `[lo, hi]`. -/
def genChildren [Gen G] (gen : Int → Int → G Tree) : Int → Int → List Int → G (List Tree)
  | lo, hi, [] => do
      let c ← gen lo hi
      return [c]
  | lo, hi, k :: ks => do
      let c ← gen lo (k - 1)
      let cs ← genChildren gen (k + 1) hi ks
      return c :: cs

theorem genChildren_mem_support {gen : Int → Int → SPMF Tree} {P : Int → Int → Tree → Prop}
    {g : Nat} (hgen : ∀ a b c, a + (g : Int) ≤ b + 1 → (c ∈ SPMF.support (gen a b) ↔ P a b c)) :
    ∀ (ks : List Int) (lo hi : Int) (cs : List Tree), Gapped g lo hi ks →
      (cs ∈ SPMF.support (genChildren gen lo hi ks) ↔ Forest P lo hi ks cs) := by
  intro ks
  induction ks with
  | nil =>
    intro lo hi cs hks
    rw [genChildren]
    support_simp
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact (hgen lo hi c hks).mp hc
    · intro hf
      match cs with
      | [c] => exact ⟨c, (hgen lo hi c hks).mpr hf, rfl⟩
      | [] => exact absurd hf not_false
      | _ :: _ :: _ => exact absurd hf not_false
  | cons k ks ih =>
    intro lo hi cs hks
    obtain ⟨hk, htl⟩ := hks
    rw [genChildren]
    support_simp
    constructor
    · rintro ⟨c, hc, cs', hcs, rfl⟩
      exact ⟨(hgen lo (k - 1) c (by omega)).mp hc, (ih (k + 1) hi cs' htl).mp hcs⟩
    · intro hf
      match cs with
      | [] => exact absurd hf not_false
      | c :: cs' =>
        obtain ⟨hc, hcs⟩ := hf
        exact ⟨c, (hgen lo (k - 1) c (by omega)).mpr hc, cs',
          (ih (k + 1) hi cs' htl).mpr hcs, rfl⟩

/-- Generates a B-tree of order `t` with keys in `[lo, hi]` and every leaf at depth `h`, whose root
holds at least `kmin` keys: choose the root's keys, then fill in the intervals they cut out. -/
def genNode [Gen G] (t kmin : Nat) : Nat → Int → Int → G Tree
  | 0, lo, hi => do
      let ks ← genKeys t kmin 0 lo hi
      return ⟨ks, []⟩
  | h + 1, lo, hi => do
      let ks ← genKeys t kmin (h + 1) lo hi
      let cs ← genChildren (fun a b => genNode t (t - 1) h a b) lo hi ks
      return ⟨ks, cs⟩

theorem genNode_mem_support : ∀ (h kmin : Nat) (lo hi : Int) (tr : Tree),
    kmin ≤ 2 * t - 1 → Fits t kmin h lo hi →
    (tr ∈ SPMF.support (genNode t kmin h lo hi : SPMF Tree)
      ↔ Tree.IsBTreeAt t kmin h lo hi tr) := by
  intro h
  induction h with
  | zero =>
    rintro kmin lo hi ⟨ks, cs⟩ hkm hfit
    rw [genNode]
    support_simp [genKeys_mem_support hkm hfit, Tree.IsBTreeAt, gap, Tree.mk.injEq]
    constructor
    · rintro ⟨ks', ⟨h1, h2, h3⟩, rfl, rfl⟩
      exact ⟨rfl, h1, h2, h3⟩
    · rintro ⟨rfl, h1, h2, h3⟩
      exact ⟨ks, ⟨h1, h2, h3⟩, rfl, rfl⟩
  | succ h ih =>
    rintro kmin lo hi ⟨ks, cs⟩ hkm hfit
    have hchild : ∀ a b c, a + (gap t (h + 1) : Int) ≤ b + 1 →
        (c ∈ SPMF.support (genNode t (t - 1) h a b : SPMF Tree)
          ↔ Tree.IsBTreeAt t (t - 1) h a b c) := by
      intro a b c hab
      refine ih (t - 1) a b c (by omega) ?_
      unfold Fits Room
      rw [gap] at hab
      push_cast at hab ⊢
      omega
    rw [genNode]
    support_simp [genKeys_mem_support hkm hfit, Tree.IsBTreeAt, Tree.mk.injEq]
    constructor
    · rintro ⟨ks', ⟨h1, h2, h3⟩, cs', hcs, rfl, rfl⟩
      exact ⟨h1, h2, h3.mono (Nat.zero_le _),
        (genChildren_mem_support hchild ks lo hi cs h3).mp hcs⟩
    · rintro ⟨h1, h2, h3, hforest⟩
      have hg : Gapped (gap t (h + 1)) lo hi ks := by
        refine Gapped.of_forest ?_ hforest
        intro a b c hc
        have := Tree.IsBTreeAt.fits h (t - 1) a b c hc
        unfold Fits Room at this
        rw [gap]
        push_cast at this ⊢
        omega
      exact ⟨ks, ⟨h1, h2, hg⟩, cs, (genChildren_mem_support hchild ks lo hi cs hg).mpr hforest,
        rfl, rfl⟩

/-- Generates a B-tree of order `t` with keys in `[lo, hi]` and every leaf at depth `h`. -/
def genBTree [Gen G] (t h : Nat) (lo hi : Int) : G Tree := genNode t (min 1 h) h lo hi

theorem genBTree_mem_support (ht : 2 ≤ t) (hfit : Fits t (min 1 h) h lo hi) (tr : Tree) :
    tr ∈ SPMF.support (genBTree t h lo hi : SPMF Tree) ↔ Tree.IsBTree t h lo hi tr :=
  genNode_mem_support h (min 1 h) lo hi tr (by omega) hfit

theorem genBTree.sound_complete (ht : 2 ≤ t) (hfit : Fits t (min 1 h) h lo hi) :
    IsSoundAndComplete (genBTree t h lo hi : SPMF Tree) (Tree.IsBTree t h lo hi) :=
  genBTree_mem_support ht hfit

end BTree
