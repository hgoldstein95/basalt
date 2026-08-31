/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt
import Mathlib.Data.Nat.Log
import BasaltExamples.BinaryHeap.Def

open RandomChoice

/-!
# Worst-Case Array Heaps

`genWorstCase n maxVal` generates the benchmark's *additional property* (Dewey, Nichols and
Hardekopf, ICSE 2015, §V): the array-backed min-heaps of `n` nodes whose `dequeue` performs exactly
`Nat.log 2 n` sift-down swaps. Positions are drawn in index order along a chosen descent path,
which is the order that keeps every index's interval nonempty, so nothing is ever rejected;
`Feasible` names the node counts that admit such a heap at all.
-/

namespace BinaryHeap

/-! ## Ancestors -/

/-- The indices on the path from `j` up to the root, `j` itself included. -/
def ancestors : Nat → List Nat
  | 0 => [0]
  | j + 1 => (j + 1) :: ancestors (j / 2)
decreasing_by omega

theorem self_mem_ancestors (j : Nat) : j ∈ ancestors j := by
  cases j <;> simp [ancestors]

theorem parent_mem_ancestors {j k : Nat} (h : k ∈ ancestors j) (hk : k ≠ 0) :
    (k - 1) / 2 ∈ ancestors j := by
  induction j using ancestors.induct with
  | case1 => rw [ancestors] at h; simp at h; omega
  | case2 j ih =>
    rw [ancestors] at h ⊢
    rcases List.mem_cons.mp h with rfl | h'
    · refine List.mem_cons_of_mem _ ?_
      rw [show (j + 1 - 1) / 2 = j / 2 by omega]
      exact self_mem_ancestors _
    · exact List.mem_cons_of_mem _ (ih h')

/-- A heap's values increase down every ancestor chain. -/
theorem IsHeap.le_of_mem_ancestors {maxVal : Nat} {a : List Nat} (h : IsHeap maxVal a) :
    ∀ (j k x y : Nat), k ∈ ancestors j → a[k]? = some x → a[j]? = some y → x ≤ y := by
  intro j
  induction j using ancestors.induct with
  | case1 =>
    intro k x y hk hx hy
    rw [ancestors] at hk
    simp at hk
    subst hk
    rw [hx] at hy
    simp at hy
    omega
  | case2 j ih =>
    intro k x y hk hx hy
    rw [ancestors] at hk
    rcases List.mem_cons.mp hk with rfl | hk'
    · rw [hx] at hy; simp at hy; omega
    · have hlt : j + 1 < a.length := (List.getElem?_eq_some_iff.mp hy).1
      obtain ⟨p, hp⟩ : ∃ p, a[j / 2]? = some p :=
        ⟨_, List.getElem?_eq_getElem (by omega)⟩
      have h1 : x ≤ p := ih k x p hk' hx hp
      have h2 : p ≤ y := by
        rcases (show j + 1 = 2 * (j / 2) + 1 ∨ j + 1 = 2 * (j / 2) + 2 by omega) with he | he
        · exact (h.2 (j / 2) p hp).1 y (he ▸ hy)
        · exact (h.2 (j / 2) p hp).2 y (he ▸ hy)
      omega

/-! ## The sift-down path -/

/-- `IsPath lim i d qs`: `qs` is a downward path of `d` nodes below `i` that stays within the first
`lim` indices. A right turn is available only when the rest of the descent still fits. -/
def IsPath (lim : Nat) : Nat → Nat → List Nat → Prop
  | _, 0, [] => True
  | i, d + 1, c :: qs =>
      (c = 2 * i + 1 ∧ IsPath lim c d qs) ∨
      (c = 2 * i + 2 ∧ (2 * i + 3) * 2 ^ d ≤ lim ∧ IsPath lim c d qs)
  | _, _, _ => False

/-- Generates a downward path of `d` nodes below `i` within the first `lim` indices. -/
def genPath [Gen G] (lim : Nat) : Nat → Nat → G (List Nat)
  | _, 0 => pure []
  | i, d + 1 =>
    if (2 * i + 3) * 2 ^ d ≤ lim then
      pick
        (fun () => do let qs ← genPath lim (2 * i + 1) d; return (2 * i + 1) :: qs)
        (fun () => do let qs ← genPath lim (2 * i + 2) d; return (2 * i + 2) :: qs)
    else do
      let qs ← genPath lim (2 * i + 1) d
      return (2 * i + 1) :: qs

theorem genPath_mem_support {lim i d : Nat} {qs : List Nat} :
    qs ∈ SPMF.support (genPath lim i d) ↔ IsPath lim i d qs := by
  induction d generalizing i qs with
  | zero => cases qs <;> simp [genPath, IsPath]
  | succ d ih =>
    rw [genPath]
    split
    · rename_i h
      match qs with
      | [] => support_simp [ih]; simp [IsPath]
      | c :: t =>
        support_simp [ih]
        simp only [IsPath, List.cons.injEq]
        constructor
        · rintro (⟨q, hq, rfl, rfl⟩ | ⟨q, hq, rfl, rfl⟩)
          · exact Or.inl ⟨rfl, hq⟩
          · exact Or.inr ⟨rfl, h, hq⟩
        · rintro (⟨rfl, hq⟩ | ⟨rfl, -, hq⟩)
          · exact Or.inl ⟨t, hq, rfl, rfl⟩
          · exact Or.inr ⟨t, hq, rfl, rfl⟩
    · rename_i h
      match qs with
      | [] => support_simp [ih]; simp [IsPath]
      | c :: t =>
        support_simp [ih]
        simp only [IsPath, List.cons.injEq]
        constructor
        · rintro ⟨q, hq, rfl, rfl⟩
          exact Or.inl ⟨rfl, hq⟩
        · rintro (⟨rfl, hq⟩ | ⟨rfl, hc, -⟩)
          · exact ⟨t, hq, rfl, rfl⟩
          · exact absurd hc h

theorem IsPath.length_eq {lim : Nat} : ∀ {d i : Nat} {qs : List Nat},
    IsPath lim i d qs → qs.length = d := by
  intro d
  induction d with
  | zero => intro i qs h; cases qs <;> simp_all [IsPath]
  | succ d ih =>
    intro i qs h
    match qs with
    | [] => simp [IsPath] at h
    | c :: t =>
      rcases h with ⟨rfl, ht⟩ | ⟨rfl, -, ht⟩ <;> simp [ih ht]

theorem IsPath.lower {lim : Nat} : ∀ {d i : Nat} {qs : List Nat},
    IsPath lim i d qs → ∀ x ∈ qs, 2 * i + 1 ≤ x := by
  intro d
  induction d with
  | zero => intro i qs h; cases qs <;> simp_all [IsPath]
  | succ d ih =>
    intro i qs h x hx
    match qs with
    | [] => simp at hx
    | c :: t =>
      rcases h with ⟨rfl, ht⟩ | ⟨rfl, -, ht⟩ <;>
        rcases List.mem_cons.mp hx with rfl | hx <;>
        first
          | omega
          | (have := ih ht x hx; omega)

theorem IsPath.no_adj {lim : Nat} : ∀ {d i : Nat} {qs : List Nat},
    IsPath lim i d qs → ∀ x ∈ qs, ∀ y ∈ qs, x + 1 ≠ y := by
  intro d
  induction d with
  | zero => intro i qs h; cases qs <;> simp_all [IsPath]
  | succ d ih =>
    intro i qs h x hx y hy
    match qs with
    | [] => simp at hx
    | c :: t =>
      have hc : c = 2 * i + 1 ∨ c = 2 * i + 2 := by
        rcases h with ⟨rfl, -⟩ | ⟨rfl, -, -⟩ <;> simp
      have ht : IsPath lim c d t := by
        rcases h with ⟨rfl, ht⟩ | ⟨rfl, -, ht⟩ <;> exact ht
      rcases List.mem_cons.mp hx with rfl | hx' <;> rcases List.mem_cons.mp hy with rfl | hy'
      · omega
      · have := ht.lower y hy'; omega
      · have := ht.lower x hx'; omega
      · exact ih ht x hx' y hy'

theorem IsPath.parent_mem {lim : Nat} : ∀ {d i : Nat} {qs : List Nat},
    IsPath lim i d qs → ∀ x ∈ qs, (x - 1) / 2 = i ∨ (x - 1) / 2 ∈ qs := by
  intro d
  induction d with
  | zero => intro i qs h; cases qs <;> simp_all [IsPath]
  | succ d ih =>
    intro i qs h x hx
    match qs with
    | [] => simp at hx
    | c :: t =>
      have ht : IsPath lim c d t := by
        rcases h with ⟨rfl, ht⟩ | ⟨rfl, -, ht⟩ <;> exact ht
      rcases List.mem_cons.mp hx with rfl | hx'
      · left; rcases h with ⟨rfl, -⟩ | ⟨rfl, -, -⟩ <;> omega
      · rcases ih ht x hx' with heq | hmem
        · right; rw [heq]; exact List.mem_cons_self
        · right; exact List.mem_cons_of_mem _ hmem

/-- Every node of a path that fits below `i` lies inside the first `lim` indices. -/
theorem IsPath.mem_lt {lim : Nat} : ∀ (d i : Nat) (qs : List Nat), IsPath lim i d qs →
    (i + 1) * 2 ^ d ≤ lim → ∀ x ∈ qs, x < lim := by
  intro d
  induction d with
  | zero => intro i qs h _ x hx; cases qs <;> simp_all [IsPath]
  | succ d ih =>
    intro i qs h hb x hx
    have hpow : (0 : Nat) < 2 ^ d := by positivity
    match qs with
    | [] => simp at hx
    | c :: t =>
      have hstep : (c + 1) * 2 ^ d ≤ lim := by
        rcases h with ⟨rfl, -⟩ | ⟨rfl, hc, -⟩
        · calc (2 * i + 1 + 1) * 2 ^ d = (i + 1) * 2 ^ (d + 1) := by rw [pow_succ]; ring
            _ ≤ lim := hb
        · rw [show 2 * i + 2 + 1 = 2 * i + 3 by omega]; exact hc
      have ht : IsPath lim c d t := by
        rcases h with ⟨rfl, ht⟩ | ⟨rfl, -, ht⟩ <;> exact ht
      rcases List.mem_cons.mp hx with rfl | hx'
      · have : x + 1 ≤ (x + 1) * 2 ^ d := Nat.le_mul_of_pos_right _ hpow
        omega
      · exact ih c t ht hstep x hx'

/-! ## Sift-down -/

theorem minChild_index {a : List Nat} {i j y : Nat} (h : minChild a i = some (j, y)) :
    j = 2 * i + 1 ∨ j = 2 * i + 2 := by
  unfold minChild at h
  split at h <;> [skip; skip; split at h] <;> simp_all

theorem minChild_getElem {a : List Nat} {i j y : Nat} (h : minChild a i = some (j, y)) :
    a[j]? = some y := by
  unfold minChild at h
  split at h <;> rename_i hl hr <;> [skip; skip; split at h] <;> simp_all

theorem minChild_none {a : List Nat} {i : Nat} (h : a[2 * i + 1]? = none) :
    minChild a i = none := by
  unfold minChild; rw [h]

theorem minChild_left {a : List Nat} {i l : Nat} (hl : a[2 * i + 1]? = some l)
    (hr : ∀ r ∈ a[2 * i + 2]?, l ≤ r) : minChild a i = some (2 * i + 1, l) := by
  unfold minChild
  rw [hl]
  cases hr' : a[2 * i + 2]? with
  | none => rfl
  | some r => have := hr r hr'; simp [Nat.not_lt.mpr this]

theorem minChild_right {a : List Nat} {i l r : Nat} (hl : a[2 * i + 1]? = some l)
    (hr : a[2 * i + 2]? = some r) (hlt : r < l) : minChild a i = some (2 * i + 2, r) := by
  unfold minChild; rw [hl, hr]; simp [hlt]

theorem minChild_congr {a a' : List Nat} {i : Nat}
    (h : ∀ k, i < k → a[k]? = a'[k]?) : minChild a i = minChild a' i := by
  unfold minChild
  rw [h (2 * i + 1) (by omega), h (2 * i + 2) (by omega)]

/-- The swap count depends only on the array below the hole, so the swaps already performed do not
affect the ones still to come. -/
theorem siftDown_snd_congr : ∀ (fuel : Nat) (a a' : List Nat) (i x : Nat),
    (∀ k, i < k → a[k]? = a'[k]?) → (siftDown fuel a i x).2 = (siftDown fuel a' i x).2 := by
  intro fuel
  induction fuel with
  | zero => intro a a' i x _; rfl
  | succ f ih =>
    intro a a' i x h
    rw [siftDown, siftDown, minChild_congr h]
    cases hm : minChild a' i with
    | none => rfl
    | some jy =>
      obtain ⟨j, y⟩ := jy
      have hj : i < j := by rcases minChild_index hm with rfl | rfl <;> omega
      simp only
      split
      · dsimp only
        refine congrArg (· + 1) (ih (a.set i y) (a'.set i y) j x fun k hk => ?_)
        simp only [List.getElem?_set, if_neg (show ¬ (i = k) by omega)]
        exact h k (by omega)
      · rfl

theorem siftDown_snd_of_none {a : List Nat} {f i x : Nat} (hm : minChild a i = none) :
    (siftDown f a i x).2 = 0 := by
  cases f with
  | zero => rfl
  | succ g => rw [siftDown, hm]

theorem siftDown_snd_succ {a : List Nat} {f i j y x : Nat} (hm : minChild a i = some (j, y))
    (hy : y < x) : (siftDown (f + 1) a i x).2 = (siftDown f a j x).2 + 1 := by
  have hj : i < j := by rcases minChild_index hm with rfl | rfl <;> omega
  rw [siftDown, hm]
  simp only [hy, if_true]
  refine congrArg (· + 1) (siftDown_snd_congr f (a.set i y) a j x fun k hk => ?_)
  rw [List.getElem?_set, if_neg (by omega)]

/-- A descent from index `i` swaps at most `d` times once the array is too short to hold a node
`d + 1` levels below `i`: each swap at least doubles `i + 1`. -/
theorem siftDown_snd_le : ∀ (d fuel : Nat) (b : List Nat) (i x : Nat),
    b.length < 2 ^ (d + 1) * (i + 1) → (siftDown fuel b i x).2 ≤ d := by
  intro d
  induction d with
  | zero =>
    intro fuel b i x hb
    rw [pow_one] at hb
    exact le_of_eq (siftDown_snd_of_none (minChild_none (List.getElem?_eq_none (by omega))))
  | succ d ih =>
    intro fuel b i x hb
    cases fuel with
    | zero => simp [siftDown]
    | succ f =>
      cases hm : minChild b i with
      | none => rw [siftDown_snd_of_none hm]; omega
      | some jy =>
        obtain ⟨j, y⟩ := jy
        by_cases hy : y < x
        · rw [siftDown_snd_succ hm hy]
          have hj : 2 * (i + 1) ≤ j + 1 := by
            rcases minChild_index hm with rfl | rfl <;> omega
          have hb' : b.length < 2 ^ (d + 1) * (j + 1) := by
            calc b.length < 2 ^ (d + 1 + 1) * (i + 1) := hb
              _ = 2 ^ (d + 1) * (2 * (i + 1)) := by rw [pow_succ]; ring
              _ ≤ 2 ^ (d + 1) * (j + 1) := Nat.mul_le_mul_left _ hj
          have := ih f b j x hb'
          omega
        · rw [siftDown, hm]
          simp [hy]

/-- `Descends b v i qs`: sifting `v` down from the hole at `i` swaps along exactly `qs`. -/
def Descends (b : List Nat) (v : Nat) : Nat → List Nat → Prop
  | _, [] => True
  | i, c :: qs => (∃ y, minChild b i = some (c, y) ∧ y < v) ∧ Descends b v c qs

theorem exists_descends {b : List Nat} {v : Nat} : ∀ (d f i : Nat), (siftDown f b i v).2 = d →
    ∃ qs, qs.length = d ∧ Descends b v i qs := by
  intro d
  induction d with
  | zero => intro f i _; exact ⟨[], rfl, trivial⟩
  | succ d ih =>
    intro f i h
    cases f with
    | zero => simp [siftDown] at h
    | succ g =>
      rw [siftDown] at h
      cases hm : minChild b i with
      | none => rw [hm] at h; simp at h
      | some jy =>
        obtain ⟨j, y⟩ := jy
        rw [hm] at h
        by_cases hy : y < v
        · simp only [hy, if_true] at h
          have hj : i < j := by rcases minChild_index hm with rfl | rfl <;> omega
          have h' : (siftDown g b j v).2 = d := by
            rw [← siftDown_snd_congr g (b.set i y) b j v fun k hk => by
              rw [List.getElem?_set, if_neg (by omega)]]
            simpa using h
          obtain ⟨qs, hlen, hd⟩ := ih g j h'
          exact ⟨j :: qs, by simp [hlen], ⟨y, hm, hy⟩, hd⟩
        · simp [hy] at h

/-- A descent of `d` further swaps below `i` needs an array long enough to hold the shallowest
node `d` levels down. -/
theorem Descends.bound {b : List Nat} {v : Nat} : ∀ (qs : List Nat) (i : Nat),
    Descends b v i qs → i < b.length → (i + 1) * 2 ^ qs.length ≤ b.length := by
  intro qs
  induction qs with
  | nil => intro i _ hi; simpa using hi
  | cons c qs' ih =>
    rintro i ⟨⟨y, hmin, -⟩, hrest⟩ hi
    have hc : c = 2 * i + 1 ∨ c = 2 * i + 2 := minChild_index hmin
    have hclt : c < b.length := (List.getElem?_eq_some_iff.mp (minChild_getElem hmin)).1
    have hIH := ih c hrest hclt
    calc (i + 1) * 2 ^ (c :: qs').length = 2 * (i + 1) * 2 ^ qs'.length := by
          simp only [List.length_cons]; rw [pow_succ]; ring
      _ ≤ (c + 1) * 2 ^ qs'.length := Nat.mul_le_mul_right _ (by omega)
      _ ≤ b.length := hIH

theorem descends_isPath {b : List Nat} {v : Nat} : ∀ (qs : List Nat) (i : Nat),
    Descends b v i qs → IsPath b.length i qs.length qs := by
  intro qs
  induction qs with
  | nil => intro i _; trivial
  | cons c qs' ih =>
    rintro i ⟨⟨y, hmin, hyv⟩, hrest⟩
    have hclt : c < b.length := (List.getElem?_eq_some_iff.mp (minChild_getElem hmin)).1
    rcases minChild_index hmin with rfl | rfl
    · exact Or.inl ⟨rfl, ih _ hrest⟩
    · refine Or.inr ⟨rfl, ?_, ih _ hrest⟩
      have h := Descends.bound qs' (2 * i + 2) hrest hclt
      rw [show 2 * i + 2 + 1 = 2 * i + 3 by omega] at h
      exact h

/-! ## Index-wise bounds -/

/-- The lower bound on the value at index `k` of an `n`-node heap, given `pre`, the values at the
indices below `k`. -/
def loB (n v : Nat) (ps pre : List Nat) (k : Nat) : Nat :=
  if k = n - 1 then v
  else if k = 0 then 0
  else if k ∈ ps then (pre[(k - 1) / 2]?).getD 0
  else if k % 2 = 1 ∧ k + 1 ∈ ps then (pre[(k - 1) / 2]?).getD 0 + 1
  else if k % 2 = 0 ∧ k - 1 ∈ ps then
    max ((pre[(k - 1) / 2]?).getD 0) ((pre[k - 1]?).getD 0)
  else (pre[(k - 1) / 2]?).getD 0

/-- The upper bound on the value at index `k`. Path nodes stay below the sifted value `v`, a right
turn must beat its left sibling, and the ancestors of the last index stay below `v`, which sits
there. -/
def hiB (n maxVal v : Nat) (ps pre : List Nat) (k : Nat) : Nat :=
  if k = n - 1 then v
  else if k = 0 then v - 1
  else if k ∈ ps then
    (if k % 2 = 0 then min (v - 1) ((pre[k - 1]?).getD 0 - 1) else v - 1)
  else if k ∈ ancestors (n - 1) then v
  else maxVal

theorem hiB_le_maxVal {n maxVal v k : Nat} {ps pre : List Nat} (hvm : v ≤ maxVal) :
    hiB n maxVal v ps pre k ≤ maxVal := by
  unfold hiB
  split
  · omega
  split
  · omega
  split
  · split <;> omega
  split <;> omega

theorem hiB_le_v {n maxVal v k : Nat} {ps pre : List Nat}
    (h : k ∈ ps ∨ k = 0 ∨ k ∈ ancestors (n - 1)) : hiB n maxVal v ps pre k ≤ v := by
  unfold hiB
  split
  · omega
  split
  · omega
  split
  · split <;> omega
  split
  · omega
  · rcases h with h | h | h <;> simp_all

theorem hiB_le_pred {n maxVal v k : Nat} {ps pre : List Nat}
    (hlast : k ≠ n - 1) (h : k ∈ ps ∨ k = 0) : hiB n maxVal v ps pre k ≤ v - 1 := by
  unfold hiB
  rw [if_neg hlast]
  split
  · omega
  split
  · split <;> omega
  · rcases h with h | h <;> simp_all

theorem loB_congr {n v k : Nat} {ps pre pre' : List Nat} (h : ∀ j, j < k → pre[j]? = pre'[j]?) :
    loB n v ps pre k = loB n v ps pre' k := by
  unfold loB
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · split <;> simp
  · simp only [h ((k - 1) / 2) (by omega), h (k - 1) (by omega)]

theorem hiB_congr {n maxVal v k : Nat} {ps pre pre' : List Nat}
    (h : ∀ j, j < k → pre[j]? = pre'[j]?) :
    hiB n maxVal v ps pre k = hiB n maxVal v ps pre' k := by
  unfold hiB
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · split <;> simp
  · simp only [h (k - 1) (by omega)]

/-- Index `k` of `a` holds a value in the interval the generator draws it from. -/
def InB (n maxVal v : Nat) (ps a : List Nat) (k : Nat) : Prop :=
  ∀ x ∈ a[k]?, loB n v ps a k ≤ x ∧ x ≤ hiB n maxVal v ps a k

/-- Every index's interval is nonempty, so the generator's draw covers exactly `[loB, hiB]`. -/
theorem loB_le_hiB {n maxVal v L : Nat} {ps pre : List Nat}
    (hL : 2 ^ L < n) (hv : 1 ≤ v) (hvm : v ≤ maxVal)
    (hps : IsPath (n - 1) 0 L ps)
    (hpre : ∀ m, m < pre.length → InB n maxVal v ps pre m) :
    loB n v ps pre pre.length ≤ hiB n maxVal v ps pre pre.length := by
  have hpow : (1 : Nat) ≤ 2 ^ L := Nat.one_le_two_pow
  set k := pre.length with hklen
  have hps_lt : ∀ x ∈ ps, x < n - 1 := IsPath.mem_lt L 0 ps hps (by simp; omega)
  have hps_par : ∀ x ∈ ps, (x - 1) / 2 = 0 ∨ (x - 1) / 2 ∈ ps := IsPath.parent_mem hps
  have hps_adj : ∀ x ∈ ps, ∀ y ∈ ps, x + 1 ≠ y := IsPath.no_adj hps
  have hsome : ∀ m, m < k → ∃ x, pre[m]? = some x := fun m hm =>
    ⟨pre[m]'(by omega), List.getElem?_eq_getElem (by omega)⟩
  have hle_max : ∀ m x, m < k → pre[m]? = some x → x ≤ maxVal := fun m x hm hx =>
    le_trans (hpre m hm x hx).2 (hiB_le_maxVal hvm)
  have hle_v : ∀ m x, m < k → (m ∈ ps ∨ m = 0 ∨ m ∈ ancestors (n - 1)) → pre[m]? = some x →
      x ≤ v := fun m x hm hmm hx => le_trans (hpre m hm x hx).2 (hiB_le_v hmm)
  have hle_pred : ∀ m x, m < k → (m ∈ ps ∨ m = 0) → pre[m]? = some x → x ≤ v - 1 := by
    intro m x hm hmm hx
    refine le_trans (hpre m hm x hx).2 (hiB_le_pred ?_ hmm)
    rcases hmm with h | rfl
    · have := hps_lt m h; omega
    · omega
  by_cases hlast : k = n - 1
  · simp [loB, hiB, hlast]
  by_cases hzero : k = 0
  · have h1 : loB n v ps pre k = 0 := by unfold loB; rw [if_neg hlast, if_pos hzero]
    rw [h1]
    exact Nat.zero_le _
  have hparlt : (k - 1) / 2 < k := by omega
  obtain ⟨P, hP⟩ := hsome ((k - 1) / 2) hparlt
  by_cases hmem : k ∈ ps
  · have hkn : k < n - 1 := hps_lt k hmem
    have hparv : P ≤ v - 1 := by
      rcases hps_par k hmem with h0 | hpm
      · exact hle_pred _ _ hparlt (Or.inr h0) hP
      · exact hle_pred _ _ hparlt (Or.inl hpm) hP
    simp only [loB, hiB, if_neg hlast, if_neg hzero, if_pos hmem, hP, Option.getD_some]
    by_cases hpar2 : k % 2 = 0
    · rw [if_pos hpar2]
      obtain ⟨S, hS⟩ := hsome (k - 1) (by omega)
      rw [hS, Option.getD_some]
      have hnotmem : k - 1 ∉ ps := fun hc => hps_adj _ hc _ hmem (by omega)
      have hlo : loB n v ps pre (k - 1) = P + 1 := by
        unfold loB
        rw [if_neg (by omega), if_neg (by omega), if_neg hnotmem,
          if_pos (show (k - 1) % 2 = 1 ∧ k - 1 + 1 ∈ ps from
            ⟨by omega, by rwa [show k - 1 + 1 = k by omega]⟩),
          show (k - 1 - 1) / 2 = (k - 1) / 2 by omega, hP]
        rfl
      have hge := (hpre (k - 1) (by omega) S hS).1
      rw [hlo] at hge
      omega
    · rw [if_neg hpar2]; omega
  by_cases hsib1 : k % 2 = 1 ∧ k + 1 ∈ ps
  · have hparv : P ≤ v - 1 := by
      have hpk : (k + 1 - 1) / 2 = (k - 1) / 2 := by omega
      rcases hps_par (k + 1) hsib1.2 with h0 | hpm
      · exact hle_pred _ _ hparlt (Or.inr (by omega)) hP
      · exact hle_pred _ _ hparlt (Or.inl (hpk ▸ hpm)) hP
    simp only [loB, hiB, if_neg hlast, if_neg hzero, if_neg hmem, if_pos hsib1, hP,
      Option.getD_some]
    split <;> omega
  by_cases hsib2 : k % 2 = 0 ∧ k - 1 ∈ ps
  · obtain ⟨S, hS⟩ := hsome (k - 1) (by omega)
    have hSv : S ≤ v - 1 := hle_pred _ _ (by omega) (Or.inl hsib2.2) hS
    have hparv : P ≤ v - 1 := by
      have hpk : (k - 1 - 1) / 2 = (k - 1) / 2 := by omega
      rcases hps_par (k - 1) hsib2.2 with h0 | hpm
      · exact hle_pred _ _ hparlt (Or.inr (by omega)) hP
      · exact hle_pred _ _ hparlt (Or.inl (hpk ▸ hpm)) hP
    simp only [loB, hiB, if_neg hlast, if_neg hzero, if_neg hmem, if_neg hsib1, if_pos hsib2,
      hP, hS, Option.getD_some]
    split <;> omega
  · simp only [loB, hiB, if_neg hlast, if_neg hzero, if_neg hmem, if_neg hsib1, if_neg hsib2,
      hP, Option.getD_some]
    split
    · rename_i hanc
      exact hle_v _ _ hparlt (Or.inr (Or.inr (parent_mem_ancestors hanc hzero))) hP
    · exact hle_max _ _ hparlt hP

/-! ## Filling the array -/

/-- Fills index `pre.length` onwards, drawing each position from its interval. -/
def genFill [Gen G] (n maxVal v : Nat) (ps : List Nat) : Nat → List Nat → G (List Nat)
  | 0, pre => pure pre
  | fuel + 1, pre => do
      let d ← chooseNat 0 (hiB n maxVal v ps pre pre.length - loB n v ps pre pre.length)
        (Nat.zero_le _)
      genFill n maxVal v ps fuel (pre ++ [loB n v ps pre pre.length + d])

theorem genFill_mem_support {n maxVal v L : Nat} {ps : List Nat}
    (hL : 2 ^ L < n) (hv : 1 ≤ v) (hvm : v ≤ maxVal)
    (hps : IsPath (n - 1) 0 L ps) :
    ∀ (fuel : Nat) (pre a : List Nat), (∀ m, m < pre.length → InB n maxVal v ps pre m) →
      (a ∈ SPMF.support (genFill n maxVal v ps fuel pre) ↔
        a.length = fuel + pre.length ∧ a.take pre.length = pre ∧
        ∀ m, pre.length ≤ m → InB n maxVal v ps a m) := by
  intro fuel
  induction fuel with
  | zero =>
    intro pre a hpre
    rw [genFill]
    simp only [SPMF.mem_support_pure_iff, Nat.zero_add]
    constructor
    · rintro rfl
      refine ⟨rfl, List.take_length, fun m hm x hx => ?_⟩
      rw [List.getElem?_eq_none (by omega)] at hx
      exact absurd hx.symm (by simp)
    · rintro ⟨hlen, htake, -⟩
      have hself : a.take pre.length = a := by rw [← hlen]; exact List.take_length
      exact hself.symm.trans htake
  | succ f ih =>
    intro pre a hpre
    have hfeas : loB n v ps pre pre.length ≤ hiB n maxVal v ps pre pre.length :=
      loB_le_hiB hL hv hvm hps hpre
    have key : ∀ (x : Nat), loB n v ps pre pre.length ≤ x →
        x ≤ hiB n maxVal v ps pre pre.length →
        ∀ m, m < (pre ++ [x]).length → InB n maxVal v ps (pre ++ [x]) m := by
      intro x hx1 hx2 m hm y hy
      simp only [List.length_append, List.length_cons, List.length_nil] at hm
      rcases Nat.lt_or_ge m pre.length with hmk | hmk
      · rw [List.getElem?_append_left hmk] at hy
        have hcongr : ∀ j, j < m → (pre ++ [x])[j]? = pre[j]? :=
          fun j hj => List.getElem?_append_left (by omega)
        rw [loB_congr hcongr, hiB_congr hcongr]
        exact hpre m hmk y hy
      · obtain rfl : m = pre.length := by omega
        rw [List.getElem?_append_right (le_refl _)] at hy
        have hyx : y = x := by simpa using hy.symm
        have hcongr : ∀ j, j < pre.length → (pre ++ [x])[j]? = pre[j]? :=
          fun j hj => List.getElem?_append_left hj
        rw [loB_congr hcongr, hiB_congr hcongr, hyx]
        exact ⟨hx1, hx2⟩
    rw [genFill]
    support_simp
    constructor
    · rintro ⟨d, ⟨-, hd⟩, hmem⟩
      have hx1 : loB n v ps pre pre.length ≤ loB n v ps pre pre.length + d := by omega
      have hx2 : loB n v ps pre pre.length + d ≤ hiB n maxVal v ps pre pre.length := by omega
      rw [ih (pre ++ [loB n v ps pre pre.length + d]) a (key _ hx1 hx2)] at hmem
      obtain ⟨hlen, htake, hall⟩ := hmem
      simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add]
        at hlen htake hall
      have hak : a[pre.length]? = some (loB n v ps pre pre.length + d) := by
        have hh : (a.take (pre.length + 1))[pre.length]? = a[pre.length]? := by
          rw [List.getElem?_take, if_pos (by omega)]
        rw [htake] at hh
        rw [← hh, List.getElem?_append_right (le_refl _)]
        simp
      have htk : a.take pre.length = pre := by
        have hh := congrArg (List.take pre.length) htake
        rw [List.take_take, Nat.min_eq_left (by omega)] at hh
        simpa using hh
      refine ⟨by omega, htk, fun m hm => ?_⟩
      rcases Nat.lt_or_ge pre.length m with hgt' | hgt'
      · exact hall m (by omega)
      · obtain rfl : m = pre.length := by omega
        intro y hy
        rw [hak] at hy
        obtain rfl : y = loB n v ps pre pre.length + d := by simpa using hy.symm
        have hcongr : ∀ j, j < pre.length → a[j]? = pre[j]? := fun j hj => by
          rw [← htk, List.getElem?_take, if_pos hj]
        rw [loB_congr hcongr, hiB_congr hcongr]
        exact ⟨hx1, hx2⟩
    · rintro ⟨hlen, htake, hall⟩
      have hk : pre.length < a.length := by omega
      obtain ⟨x, hax⟩ : ∃ x, a[pre.length]? = some x :=
        ⟨a[pre.length]'hk, List.getElem?_eq_getElem hk⟩
      have hcongr : ∀ j, j < pre.length → a[j]? = pre[j]? := fun j hj => by
        rw [← htake, List.getElem?_take, if_pos hj]
      obtain ⟨hx1, hx2⟩ := hall pre.length (le_refl _) x hax
      rw [loB_congr hcongr] at hx1
      rw [hiB_congr hcongr] at hx2
      refine ⟨x - loB n v ps pre pre.length, ⟨Nat.zero_le _, by omega⟩, ?_⟩
      rw [show loB n v ps pre pre.length + (x - loB n v ps pre pre.length) = x by omega]
      have hlenapp : (pre ++ [x]).length = pre.length + 1 := by simp
      rw [ih (pre ++ [x]) a (key x hx1 hx2)]
      refine ⟨by rw [hlenapp]; omega, ?_, fun m hm => hall m (by rw [hlenapp] at hm; omega)⟩
      rw [hlenapp, List.take_add_one, htake, hax]
      rfl

/-! ## From the index bounds to the heap laws -/

theorem getElem_last {n maxVal v : Nat} {ps a : List Nat} (hn : 1 ≤ n)
    (hlen : a.length = n) (hcond : ∀ m, InB n maxVal v ps a m) : a[n - 1]? = some v := by
  obtain ⟨x, hx⟩ : ∃ x, a[n - 1]? = some x :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨hlo, hhi⟩ := hcond _ x hx
  simp only [loB, hiB, if_true] at hlo hhi
  rw [hx]
  congr 1
  omega

theorem le_loB_of_parent {n v k i p : Nat} {ps a : List Nat} (hp : a[i]? = some p)
    (hk : k = 2 * i + 1 ∨ k = 2 * i + 2) (hne : k ≠ n - 1) : p ≤ loB n v ps a k := by
  have hpar : (k - 1) / 2 = i := by omega
  unfold loB
  rw [if_neg hne, if_neg (by omega : ¬ k = 0)]
  simp only [hpar, hp, Option.getD_some]
  split
  · omega
  split
  · omega
  split
  · exact le_max_left _ _
  · omega

theorem isHeap_of_cond {n maxVal v : Nat} {ps a : List Nat} (hn : 1 ≤ n) (hvm : v ≤ maxVal)
    (hlen : a.length = n) (hcond : ∀ m, InB n maxVal v ps a m) : IsHeap maxVal a := by
  constructor
  · intro x hx
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hx
    exact le_trans (hcond i x hi).2 (hiB_le_maxVal hvm)
  · intro i p hp
    have hchild : ∀ k, (k = 2 * i + 1 ∨ k = 2 * i + 2) → ∀ y ∈ a[k]?, p ≤ y := by
      intro k hk y hy
      by_cases hne : k = n - 1
      · have hpar : (n - 1 - 1) / 2 = i := by omega
        have hiv : i ∈ ancestors (n - 1) :=
          hpar ▸ parent_mem_ancestors (self_mem_ancestors (n - 1)) (by omega)
        have hyv : y = v := by
          rw [hne, getElem_last hn hlen hcond] at hy
          simpa using hy.symm
        have h1 := (hcond i p hp).2
        have h2 := hiB_le_v (n := n) (maxVal := maxVal) (v := v) (ps := ps) (pre := a) (k := i)
          (Or.inr (Or.inr hiv))
        omega
      · exact le_trans (le_loB_of_parent hp hk hne) (hcond k y hy).1
    exact ⟨hchild _ (Or.inl rfl), hchild _ (Or.inr rfl)⟩

theorem le_loB_sibling_right {n v i l : Nat} {ps a : List Nat} (hl : a[2 * i + 1]? = some l)
    (hmem : 2 * i + 1 ∈ ps) (hnm : 2 * i + 2 ∉ ps) (hne : 2 * i + 2 ≠ n - 1) :
    l ≤ loB n v ps a (2 * i + 2) := by
  unfold loB
  rw [if_neg hne, if_neg (by omega : ¬ 2 * i + 2 = 0), if_neg hnm,
    if_neg (by rintro ⟨h, -⟩; omega),
    if_pos (show (2 * i + 2) % 2 = 0 ∧ 2 * i + 2 - 1 ∈ ps from
      ⟨by omega, by rw [show 2 * i + 2 - 1 = 2 * i + 1 by omega]; exact hmem⟩),
    show 2 * i + 2 - 1 = 2 * i + 1 by omega, hl]
  exact le_max_right _ _

theorem one_le_loB_sibling_left {n v i : Nat} {ps a : List Nat} (hmem : 2 * i + 2 ∈ ps)
    (hnm : 2 * i + 1 ∉ ps) (hne : 2 * i + 1 ≠ n - 1) : 1 ≤ loB n v ps a (2 * i + 1) := by
  unfold loB
  rw [if_neg hne, if_neg (by omega : ¬ 2 * i + 1 = 0), if_neg hnm,
    if_pos (show (2 * i + 1) % 2 = 1 ∧ 2 * i + 1 + 1 ∈ ps from
      ⟨by omega, by rw [show 2 * i + 1 + 1 = 2 * i + 2 by omega]; exact hmem⟩)]
  omega

theorem hiB_right_child {n maxVal v i : Nat} {ps a : List Nat} (hmem : 2 * i + 2 ∈ ps)
    (hne : 2 * i + 2 ≠ n - 1) :
    hiB n maxVal v ps a (2 * i + 2) = min (v - 1) ((a[2 * i + 1]?).getD 0 - 1) := by
  unfold hiB
  rw [if_neg hne, if_neg (by omega : ¬ 2 * i + 2 = 0), if_pos hmem, if_pos (by omega),
    show 2 * i + 2 - 1 = 2 * i + 1 by omega]

/-- The generated array's `dequeue` sifts along the chosen path, one swap per level. -/
theorem dequeue_snd_eq {n maxVal v L : Nat} {ps a : List Nat}
    (hn : 1 ≤ n) (hL : 2 ^ L < n) (hLn : n < 2 ^ (L + 1)) (hv : 1 ≤ v)
    (hps : IsPath (n - 1) 0 L ps) (hlen : a.length = n) (hcond : ∀ m, InB n maxVal v ps a m) :
    (dequeue a).2 = L := by
  have hpowpos : (1 : Nat) ≤ 2 ^ L := Nat.one_le_two_pow
  have hpow1 : (2 : Nat) ^ (L + 1) = 2 * 2 ^ L := by rw [pow_succ]; ring
  have hps_lt : ∀ x ∈ ps, x < n - 1 := IsPath.mem_lt L 0 ps hps (by simp; omega)
  have hps_adj : ∀ x ∈ ps, ∀ y ∈ ps, x + 1 ≠ y := IsPath.no_adj hps
  have hpslen : ps.length = L := IsPath.length_eq hps
  have hb : ∀ k, k < n - 1 → (a.dropLast)[k]? = a[k]? := by
    intro k hk
    rw [List.dropLast_eq_take, hlen, List.getElem?_take, if_pos (by omega)]
  have hbn : ∀ k, n - 1 ≤ k → (a.dropLast)[k]? = none := by
    intro k hk
    rw [List.dropLast_eq_take, hlen, List.getElem?_take, if_neg (by omega)]
  have hgetlast : a.getLast? = some v := by
    rw [List.getLast?_eq_getElem?, hlen]
    exact getElem_last hn hlen hcond
  have walk : ∀ (qs : List Nat) (i fuel : Nat), IsPath (n - 1) i qs.length qs →
      (∀ x ∈ qs, x ∈ ps) → 2 ^ L ≤ 2 ^ qs.length * (i + 1) → qs.length ≤ fuel →
      (siftDown fuel (a.dropLast) i v).2 = qs.length := by
    intro qs
    induction qs with
    | nil =>
      intro i fuel _ _ hgrow _
      simp only [List.length_nil, pow_zero, one_mul] at hgrow
      exact siftDown_snd_of_none (minChild_none (hbn _ (by omega)))
    | cons c qs' ih =>
      intro i fuel hpath hmem hgrow hfuel
      simp only [List.length_cons] at hgrow hfuel
      have hstep : (c = 2 * i + 1 ∨ c = 2 * i + 2) ∧ IsPath (n - 1) c qs'.length qs' := by
        simp only [List.length_cons, IsPath] at hpath
        rcases hpath with ⟨rfl, h⟩ | ⟨rfl, -, h⟩
        · exact ⟨Or.inl rfl, h⟩
        · exact ⟨Or.inr rfl, h⟩
      obtain ⟨hcc, hpath'⟩ := hstep
      have hcps : c ∈ ps := hmem c (by simp)
      have hclt : c < n - 1 := hps_lt c hcps
      obtain ⟨yc, hyc⟩ : ∃ y, a[c]? = some y := ⟨_, List.getElem?_eq_getElem (by omega)⟩
      have hycv : yc < v := by
        have h1 := (hcond c yc hyc).2
        have h2 := hiB_le_pred (n := n) (maxVal := maxVal) (v := v) (ps := ps) (pre := a)
          (k := c) (by omega) (Or.inl hcps)
        omega
      have hmin : minChild (a.dropLast) i = some (c, yc) := by
        rcases hcc with rfl | rfl
        · refine minChild_left (by rw [hb _ (by omega)]; exact hyc) (fun r hr => ?_)
          by_cases hlt : 2 * i + 2 < n - 1
          · rw [hb _ hlt] at hr
            have hnm : 2 * i + 2 ∉ ps := fun hc => hps_adj _ hcps _ hc (by omega)
            exact le_trans (le_loB_sibling_right hyc hcps hnm (by omega)) (hcond _ r hr).1
          · rw [hbn _ (by omega)] at hr; simp at hr
        · have hlsome : ∃ l, a[2 * i + 1]? = some l := ⟨_, List.getElem?_eq_getElem (by omega)⟩
          obtain ⟨l, hl⟩ := hlsome
          have hnm : 2 * i + 1 ∉ ps := fun hc => hps_adj _ hc _ hcps (by omega)
          have hone : 1 ≤ l :=
            le_trans (one_le_loB_sibling_left hcps hnm (by omega)) (hcond _ l hl).1
          have hstrict : yc ≤ l - 1 := by
            have h1 := (hcond _ yc hyc).2
            rw [hiB_right_child hcps (by omega), hl, Option.getD_some] at h1
            omega
          refine minChild_right (by rw [hb _ (by omega)]; exact hl)
            (by rw [hb _ (by omega)]; exact hyc) (by omega)
      cases fuel with
      | zero => omega
      | succ f =>
        rw [siftDown_snd_succ hmin hycv]
        have hgrow' : 2 ^ L ≤ 2 ^ qs'.length * (c + 1) := by
          have h2 : 2 * (i + 1) ≤ c + 1 := by omega
          calc 2 ^ L ≤ 2 ^ (qs'.length + 1) * (i + 1) := hgrow
            _ = 2 ^ qs'.length * (2 * (i + 1)) := by rw [pow_succ]; ring
            _ ≤ 2 ^ qs'.length * (c + 1) := Nat.mul_le_mul_left _ h2
        rw [ih c f hpath' (fun x hx => hmem x (by simp [hx])) hgrow' (by omega)]
        simp
  have hfuel : ps.length ≤ a.length := by
    have : L < 2 ^ L := Nat.lt_two_pow_self
    omega
  simp only [dequeue, hgetlast]
  rw [walk ps 0 a.length (hpslen ▸ hps) (fun x hx => hx) (by simp [hpslen]) hfuel, hpslen]

/-! ## From the heap laws back to the index bounds -/

theorem minChild_inv {a : List Nat} {i j y : Nat} (h : minChild a i = some (j, y)) :
    (j = 2 * i + 1 ∧ a[j]? = some y ∧ ∀ r ∈ a[2 * i + 2]?, y ≤ r) ∨
    (j = 2 * i + 2 ∧ a[j]? = some y ∧ ∃ l, a[2 * i + 1]? = some l ∧ y < l) := by
  obtain hl | ⟨l, hl⟩ := Option.eq_none_or_eq_some a[2 * i + 1]?
  · rw [minChild_none hl] at h; simp at h
  obtain hr | ⟨r, hr⟩ := Option.eq_none_or_eq_some a[2 * i + 2]?
  · have hge : ∀ r' ∈ a[2 * i + 2]?, l ≤ r' := by rw [hr]; simp
    rw [minChild_left hl hge] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact Or.inl ⟨rfl, hl, hge⟩
  by_cases hlt : r < l
  · rw [minChild_right hl hr hlt] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact Or.inr ⟨rfl, hr, l, hl, hlt⟩
  · have hge : ∀ r' ∈ a[2 * i + 2]?, l ≤ r' := by
      rw [hr]
      intro r' hr'
      simp only [Option.mem_def, Option.some.injEq] at hr'
      omega
    rw [minChild_left hl hge] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact Or.inl ⟨rfl, hl, hge⟩

theorem Descends.facts {b : List Nat} {v : Nat} : ∀ (i : Nat) (qs : List Nat),
    Descends b v i qs → ∀ c ∈ qs, ∃ y, minChild b ((c - 1) / 2) = some (c, y) ∧ y < v := by
  intro i qs
  induction qs generalizing i with
  | nil => intro _ c hc; simp at hc
  | cons c' qs' ih =>
    rintro ⟨⟨y, hmin, hyv⟩, hrest⟩ c hc
    rcases List.mem_cons.mp hc with rfl | hc'
    · have : (c - 1) / 2 = i := by rcases minChild_index hmin with rfl | rfl <;> omega
      rw [this]
      exact ⟨y, hmin, hyv⟩
    · exact ih c' hrest c hc'

/-- A worst-case heap is generated by the path its own `dequeue` takes. -/
theorem cond_of_isHeap {n maxVal L : Nat} {a : List Nat} (hn : 2 ≤ n) (hLn : n < 2 ^ (L + 1))
    (hlen : a.length = n) (hheap : IsHeap maxVal a) (hdeq : (dequeue a).2 = L) :
    ∃ v ps, 1 ≤ v ∧ v ≤ maxVal ∧ IsPath (n - 1) 0 L ps ∧ ∀ m, InB n maxVal v ps a m := by
  have hL1 : 1 ≤ L := by
    rcases Nat.eq_zero_or_pos L with rfl | h
    · simp at hLn; omega
    · exact h
  obtain ⟨v, hv⟩ : ∃ v, a[n - 1]? = some v := ⟨_, List.getElem?_eq_getElem (by omega)⟩
  have hgetlast : a.getLast? = some v := by rw [List.getLast?_eq_getElem?, hlen]; exact hv
  have hb : ∀ k, k < n - 1 → (a.dropLast)[k]? = a[k]? := by
    intro k hk
    rw [List.dropLast_eq_take, hlen, List.getElem?_take, if_pos (by omega)]
  have hbn : ∀ k, n - 1 ≤ k → (a.dropLast)[k]? = none := by
    intro k hk
    rw [List.dropLast_eq_take, hlen, List.getElem?_take, if_neg (by omega)]
  have hblen : (a.dropLast).length = n - 1 := by rw [List.length_dropLast, hlen]
  have hdeq' : (siftDown a.length (a.dropLast) 0 v).2 = L := by
    simpa [dequeue, hgetlast] using hdeq
  obtain ⟨ps, hpslen, hdesc⟩ := exists_descends L a.length 0 hdeq'
  have hpath : IsPath (n - 1) 0 L ps := by
    have h := descends_isPath ps 0 hdesc
    rw [hpslen, hblen] at h
    exact h
  have hkey : ∀ c ∈ ps, ∃ y, minChild (a.dropLast) ((c - 1) / 2) = some (c, y) ∧ y < v :=
    Descends.facts 0 ps hdesc
  have hclt : ∀ c ∈ ps, c < n - 1 := by
    intro c hc
    obtain ⟨y, hmin, -⟩ := hkey c hc
    obtain ⟨hb', -⟩ := List.getElem?_eq_some_iff.mp (minChild_getElem hmin)
    rw [hblen] at hb'
    exact hb'
  have hval : ∀ c ∈ ps, ∀ x, a[c]? = some x → x < v := by
    intro c hc x hx
    obtain ⟨y, hmin, hyv⟩ := hkey c hc
    have h1 := minChild_getElem hmin
    rw [hb c (hclt c hc), hx] at h1
    obtain rfl : x = y := by simpa using h1
    exact hyv
  have hright : ∀ c ∈ ps, c % 2 = 0 → ∀ x z, a[c]? = some x → a[c - 1]? = some z → x < z := by
    intro c hc hp2 x z hx hz
    obtain ⟨y, hmin, -⟩ := hkey c hc
    have hcpos : 1 ≤ c := by
      obtain ⟨y', hmin', -⟩ := hkey c hc
      rcases minChild_index hmin' with h | h <;> omega
    rcases minChild_inv hmin with ⟨hcc, -, -⟩ | ⟨-, hby, l, hl, hyl⟩
    · omega
    · rw [show 2 * ((c - 1) / 2) + 1 = c - 1 by omega, hb (c - 1) (by have := hclt c hc; omega),
        hz] at hl
      obtain rfl : z = l := by simpa using hl
      rw [hb c (hclt c hc), hx] at hby
      obtain rfl : x = y := by simpa using hby
      exact hyl
  have hleft : ∀ c ∈ ps, c % 2 = 1 → ∀ x z, a[c]? = some x → a[c + 1]? = some z →
      c + 1 < n - 1 → x ≤ z := by
    intro c hc hp2 x z hx hz hlt
    obtain ⟨y, hmin, -⟩ := hkey c hc
    rcases minChild_inv hmin with ⟨-, hby, hge⟩ | ⟨hcc, -, -⟩
    · rw [hb c (hclt c hc), hx] at hby
      obtain rfl : x = y := by simpa using hby
      refine hge z ?_
      rw [show 2 * ((c - 1) / 2) + 2 = c + 1 by omega, hb (c + 1) hlt]
      exact hz
    · omega
  have hheapc : ∀ i p, a[i]? = some p → ∀ k, (k = 2 * i + 1 ∨ k = 2 * i + 2) → ∀ z,
      a[k]? = some z → p ≤ z := by
    intro i p hp k hk z hz
    rcases hk with rfl | rfl
    · exact (hheap.2 i p hp).1 z hz
    · exact (hheap.2 i p hp).2 z hz
  obtain ⟨c0, rest, hpseq⟩ : ∃ c rest, ps = c :: rest := by
    cases ps with
    | nil => simp at hpslen; omega
    | cons c rest => exact ⟨c, rest, rfl⟩
  have hc0mem : c0 ∈ ps := by rw [hpseq]; exact List.mem_cons_self
  have hc0child : c0 = 1 ∨ c0 = 2 := by
    have hd : Descends (a.dropLast) v 0 (c0 :: rest) := hpseq ▸ hdesc
    obtain ⟨y, hmin, -⟩ := hd.1
    rcases minChild_index hmin with h | h <;> omega
  have hvpos : 1 ≤ v := by
    obtain ⟨z, hz⟩ : ∃ z, a[c0]? = some z :=
      ⟨_, List.getElem?_eq_getElem (by have := hclt c0 hc0mem; omega)⟩
    have := hval c0 hc0mem z hz
    omega
  refine ⟨v, ps, hvpos, hheap.1 v (List.mem_iff_getElem?.mpr ⟨_, hv⟩), hpath, ?_⟩
  intro m x hx
  have hmlt : m < a.length := (List.getElem?_eq_some_iff.mp hx).1
  by_cases hlast : m = n - 1
  · subst hlast
    rw [hv] at hx
    obtain rfl : x = v := by simpa using hx.symm
    simp [loB, hiB]
  have hmlast : m < n - 1 := by omega
  by_cases hzero : m = 0
  · subst hzero
    refine ⟨by simp [loB, hlast], ?_⟩
    rw [hiB, if_neg hlast, if_pos rfl]
    obtain ⟨z, hz⟩ : ∃ z, a[c0]? = some z :=
      ⟨_, List.getElem?_eq_getElem (by have := hclt c0 hc0mem; omega)⟩
    have h1 : x ≤ z := hheapc 0 x hx c0 (by omega) z hz
    have h2 : z < v := hval c0 hc0mem z hz
    omega
  obtain ⟨P, hP⟩ : ∃ P, a[(m - 1) / 2]? = some P := ⟨_, List.getElem?_eq_getElem (by omega)⟩
  have hPx : P ≤ x := hheapc _ P hP m (by omega) x hx
  constructor
  · unfold loB
    rw [if_neg hlast, if_neg hzero]
    split
    · rw [hP]; simpa using hPx
    split
    · rename_i hmm hsib
      obtain ⟨z, hz⟩ : ∃ z, a[m + 1]? = some z :=
        ⟨_, List.getElem?_eq_getElem (by have := hclt (m + 1) hsib.2; omega)⟩
      have hzx : z < x := hright (m + 1) hsib.2 (by omega) z x hz
        (by rw [show m + 1 - 1 = m by omega]; exact hx)
      have hPz : P ≤ z := hheapc _ P hP (m + 1) (by omega) z hz
      rw [hP]
      simp only [Option.getD_some]
      omega
    split
    · rename_i hmm hsib1 hsib2
      obtain ⟨S, hS⟩ : ∃ S, a[m - 1]? = some S := ⟨_, List.getElem?_eq_getElem (by omega)⟩
      have hSx : S ≤ x := hleft (m - 1) hsib2.2 (by omega) S x hS
        (by rw [show m - 1 + 1 = m by omega]; exact hx) (by omega)
      rw [hP, hS]
      simp only [Option.getD_some, max_le_iff]
      exact ⟨hPx, hSx⟩
    · rw [hP]; simpa using hPx
  · unfold hiB
    rw [if_neg hlast, if_neg hzero]
    split
    · rename_i hmm
      have hxv : x < v := hval m hmm x hx
      split
      · rename_i heven
        obtain ⟨S, hS⟩ : ∃ S, a[m - 1]? = some S := ⟨_, List.getElem?_eq_getElem (by omega)⟩
        have hxS : x < S := hright m hmm heven x S hx hS
        rw [hS]
        simp only [Option.getD_some, le_min_iff]
        omega
      · omega
    split
    · rename_i hmm hanc
      exact hheap.le_of_mem_ancestors (n - 1) m x v hanc hx hv
    · exact hheap.1 x (List.mem_iff_getElem?.mpr ⟨m, hx⟩)

/-! ## The generator -/

/-- An array of length `2 ^ k` never sifts the full `Nat.log 2 n` swaps: `dequeue` descends
`a.dropLast`, which is one level short. -/
theorem not_worst_case_of_length_pow_two {k : Nat} {a : List Nat} (hk : 1 ≤ k)
    (hlen : a.length = 2 ^ k) : (dequeue a).2 ≠ Nat.log 2 a.length := by
  intro hcon
  rw [hlen, Nat.log_pow (by norm_num)] at hcon
  have hpos : (1 : Nat) ≤ 2 ^ k := Nat.one_le_two_pow
  cases hg : a.getLast? with
  | none =>
    rw [List.getLast?_eq_none_iff] at hg
    rw [hg] at hlen
    simp at hlen
    omega
  | some last =>
    simp only [dequeue, hg] at hcon
    have hle : (siftDown a.length a.dropLast 0 last).2 ≤ k - 1 :=
      siftDown_snd_le (k - 1) a.length a.dropLast 0 last (by
        rw [List.length_dropLast, hlen, show k - 1 + 1 = k by omega]
        omega)
    omega

/-- The node counts that admit a worst-case heap at all: `dequeue` sifts through `a.dropLast`, so
a power of two above `1` is one level short of `Nat.log 2 n` swaps
(`not_worst_case_of_length_pow_two`), and every other count is realizable. -/
def Feasible (n : Nat) : Prop := n ≤ 1 ∨ 2 ^ Nat.log 2 n < n

instance (n : Nat) : Decidable (Feasible n) := by unfold Feasible; infer_instance

/-- The specialized structure: an `n`-node heap on which `dequeue` performs the worst-case
`Nat.log 2 n` sift-down swaps. -/
def IsWorstCase (n maxVal : Nat) (a : List Nat) : Prop :=
  a.length = n ∧ IsHeap maxVal a ∧ (dequeue a).2 = Nat.log 2 a.length

theorem not_worst_case_of_infeasible {n maxVal : Nat} {a : List Nat} (hn : 2 ≤ n)
    (hf : ¬ Feasible n) : ¬ IsWorstCase n maxVal a := by
  rintro ⟨hlen, -, hdeq⟩
  have hle : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 (by omega)
  have heq : n = 2 ^ Nat.log 2 n := by
    unfold Feasible at hf
    omega
  have hk : 1 ≤ Nat.log 2 n := by
    rcases Nat.eq_zero_or_pos (Nat.log 2 n) with h | h
    · rw [h] at heq; simp at heq; omega
    · exact h
  exact not_worst_case_of_length_pow_two hk (hlen.trans heq) hdeq

/-- Sifting a `1` into an array of zeros descends the leftmost path, one swap per level that
fits. -/
theorem siftDown_replicate : ∀ (d fuel i m : Nat), (i + 1) * 2 ^ d ≤ m →
    m < (i + 1) * 2 ^ (d + 1) → d ≤ fuel →
    (siftDown fuel (List.replicate m 0) i 1).2 = d := by
  intro d
  induction d with
  | zero =>
    intro fuel i m _ h2 _
    rw [pow_one] at h2
    refine siftDown_snd_of_none (minChild_none (List.getElem?_eq_none ?_))
    rw [List.length_replicate]
    omega
  | succ d ih =>
    intro fuel i m h1 h2 hf
    have hpow : (2 : Nat) ≤ 2 ^ (d + 1) := by
      calc (2 : Nat) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (d + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hlt : 2 * i + 1 < m := by
      have h3 : (i + 1) * 2 ≤ (i + 1) * 2 ^ (d + 1) := Nat.mul_le_mul_left _ hpow
      omega
    have hget : (List.replicate m 0)[2 * i + 1]? = some 0 := by
      rw [List.getElem?_eq_getElem (by rw [List.length_replicate]; omega)]
      simp
    have hmin : minChild (List.replicate m 0) i = some (2 * i + 1, 0) :=
      minChild_left hget (fun r _ => Nat.zero_le _)
    have h1' : (2 * i + 1 + 1) * 2 ^ d ≤ m := by
      calc (2 * i + 1 + 1) * 2 ^ d = (i + 1) * 2 ^ (d + 1) := by ring
        _ ≤ m := h1
    have h2' : m < (2 * i + 1 + 1) * 2 ^ (d + 1) := by
      calc m < (i + 1) * 2 ^ (d + 1 + 1) := h2
        _ = (2 * i + 1 + 1) * 2 ^ (d + 1) := by ring
    cases fuel with
    | zero => omega
    | succ f =>
      rw [siftDown_snd_succ hmin (by omega), ih f (2 * i + 1) m h1' h2' (by omega)]

/-- Zeros with a single `1` at the end are a worst-case heap of every feasible size. -/
theorem worst_case_replicate {n maxVal : Nat} (hm : 1 ≤ maxVal) (hn : 1 ≤ n) (hf : Feasible n) :
    IsWorstCase n maxVal (List.replicate (n - 1) 0 ++ [1]) := by
  have hlen : (List.replicate (n - 1) 0 ++ [1]).length = n := by simp; omega
  have hget : ∀ k, k < n - 1 → (List.replicate (n - 1) 0 ++ [1])[k]? = some 0 := by
    intro k hk
    rw [List.getElem?_append_left (by rw [List.length_replicate]; omega),
      List.getElem?_eq_getElem (by rw [List.length_replicate]; omega)]
    simp
  have hdrop : (List.replicate (n - 1) 0 ++ [1]).dropLast = List.replicate (n - 1) 0 := by simp
  have hlast : (List.replicate (n - 1) 0 ++ [1]).getLast? = some 1 := by simp
  have hLn : n < 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  refine ⟨hlen, ⟨?_, ?_⟩, ?_⟩
  · intro x hx
    simp only [List.mem_append, List.mem_replicate, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with ⟨-, rfl⟩ | rfl <;> omega
  · intro i p hp
    have hp' : (List.replicate (n - 1) 0 ++ [1])[i]? = some p := hp
    have key : ∀ k y, 2 * i + 1 ≤ k → (List.replicate (n - 1) 0 ++ [1])[k]? = some y → p ≤ y := by
      intro k y hk hy
      by_cases hi : i < n - 1
      · rw [hget i hi] at hp'
        obtain rfl : p = 0 := by simpa using hp'.symm
        exact Nat.zero_le _
      · have hilt := (List.getElem?_eq_some_iff.mp hp').1
        have hklt := (List.getElem?_eq_some_iff.mp hy).1
        omega
    exact ⟨fun l hl => key _ _ (by omega) hl, fun r hr => key _ _ (by omega) hr⟩
  · rw [hlen]
    simp only [dequeue, hlast, hdrop, hlen]
    rcases (show n = 1 ∨ 2 ^ Nat.log 2 n < n by unfold Feasible at hf; omega) with rfl | hL
    · rw [show Nat.log 2 1 = 0 by simp]
      exact siftDown_snd_of_none (minChild_none (List.getElem?_eq_none (by simp)))
    · refine siftDown_replicate (Nat.log 2 n) n 0 (n - 1) (by simpa using Nat.le_sub_one_of_lt hL)
        (by simpa using by omega) ?_
      have : Nat.log 2 n < 2 ^ Nat.log 2 n := Nat.lt_two_pow_self
      omega

/-- `Feasible` is exactly the set of node counts a worst-case heap can have. -/
theorem exists_worst_case_iff {n maxVal : Nat} (hm : 1 ≤ maxVal) :
    (∃ a, IsWorstCase n maxVal a) ↔ Feasible n := by
  constructor
  · rintro ⟨a, ha⟩
    by_contra hf
    rcases Nat.lt_or_ge n 2 with h | h
    · exact hf (Or.inl (by omega))
    · exact not_worst_case_of_infeasible h hf ha
  · intro hf
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact ⟨[], rfl, ⟨by simp, by simp⟩, by simp [dequeue]⟩
    · exact ⟨_, worst_case_replicate hm hn hf⟩

/-- Generates every worst-case heap of `n` nodes with values in `[0, maxVal]`: draw the sifted
value, then the descent path it will take, then fill the array in index order. The `Feasible`
argument rules out the sizes that have no worst-case heap to generate. -/
def genWorstCase [Gen G] (n maxVal : Nat) (hm : 1 ≤ maxVal) (hf : Feasible n) : G (List Nat) :=
  match n with
  | 0 => pure []
  | 1 => do
      let x ← chooseNat 0 maxVal (Nat.zero_le _)
      pure [x]
  | n + 2 => do
      let v ← chooseNat 1 maxVal hm
      let ps ← genPath (n + 1) 0 (Nat.log 2 (n + 2))
      genFill (n + 2) maxVal v ps (n + 2) []

theorem genWorstCase_mem_support {n maxVal : Nat} {hm : 1 ≤ maxVal} {hf : Feasible n}
    (a : List Nat) :
    a ∈ SPMF.support (genWorstCase n maxVal hm hf) ↔ IsWorstCase n maxVal a := by
  match n with
  | 0 =>
    rw [genWorstCase]
    support_simp
    constructor
    · rintro rfl
      exact ⟨rfl, ⟨by simp, by simp⟩, by simp [dequeue]⟩
    · rintro ⟨hlen, -, -⟩
      exact List.eq_nil_of_length_eq_zero hlen
  | 1 =>
    rw [genWorstCase]
    support_simp
    constructor
    · rintro ⟨x, ⟨-, hx⟩, rfl⟩
      refine ⟨rfl, ⟨fun y hy => by simp at hy; omega, fun i p hp => ⟨?_, ?_⟩⟩, ?_⟩
      · intro l hl
        rw [List.getElem?_eq_none (by simp)] at hl
        simp at hl
      · intro r hr
        rw [List.getElem?_eq_none (by simp)] at hr
        simp at hr
      · simp [dequeue, minChild, siftDown]
    · rintro ⟨hlen, hheap, -⟩
      obtain ⟨x, rfl⟩ : ∃ x, a = [x] := by
        match a, hlen with
        | [x], _ => exact ⟨x, rfl⟩
      exact ⟨x, ⟨Nat.zero_le _, hheap.1 x (by simp)⟩, rfl⟩
  | n + 2 =>
    have hL : 2 ^ Nat.log 2 (n + 2) < n + 2 := by
      unfold Feasible at hf
      omega
    have hLn : n + 2 < 2 ^ (Nat.log 2 (n + 2) + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
    have hlim : n + 2 - 1 = n + 1 := by omega
    rw [genWorstCase]
    support_simp [genPath_mem_support]
    constructor
    · rintro ⟨v, ⟨hv1, hv2⟩, ps, hps, hmem⟩
      rw [← hlim] at hps
      rw [genFill_mem_support hL hv1 hv2 hps _ [] a (by simp)] at hmem
      obtain ⟨hlen, -, hall⟩ := hmem
      simp only [List.length_nil, Nat.add_zero] at hlen hall
      have hcond : ∀ m, InB (n + 2) maxVal v ps a m := fun m => hall m (by omega)
      refine ⟨hlen, isHeap_of_cond (by omega) hv2 hlen hcond, ?_⟩
      rw [hlen]
      exact dequeue_snd_eq (by omega) hL hLn hv1 hps hlen hcond
    · rintro ⟨hlen, hheap, hdeq⟩
      rw [hlen] at hdeq
      obtain ⟨v, ps, hv1, hv2, hps, hcond⟩ :=
        cond_of_isHeap (by omega) hLn hlen hheap hdeq
      refine ⟨v, ⟨hv1, hv2⟩, ps, by rwa [hlim] at hps, ?_⟩
      rw [genFill_mem_support hL hv1 hv2 hps _ [] a (by simp)]
      exact ⟨by simpa using hlen, by simp, fun m _ => hcond m⟩

theorem genWorstCase.sound_complete {n maxVal : Nat} {hm : 1 ≤ maxVal} {hf : Feasible n} :
    IsSoundAndComplete (genWorstCase n maxVal hm hf) (IsWorstCase n maxVal) :=
  fun _ => genWorstCase_mem_support _

/-! ## Termination and cost -/

theorem genPath_isPMF {lim : Nat} : ∀ (d i : Nat), SPMF.IsPMF (genPath lim i d) := by
  intro d
  induction d with
  | zero => intro i; rw [genPath]; exact SPMF.IsPMF_pure _
  | succ d ih =>
    intro i
    have hb : ∀ (c j : Nat),
        SPMF.IsPMF (do let qs ← (genPath lim j d : SPMF (List Nat)); return c :: qs) :=
      fun c j => SPMF.IsPMF_bind_pure (ih j)
    rw [genPath]
    split
    · exact SPMF.IsPMF_pick (hb _ _) (hb _ _)
    · exact hb _ _

theorem genFill_isPMF {n maxVal v : Nat} {ps : List Nat} :
    ∀ (fuel : Nat) (pre : List Nat), SPMF.IsPMF (genFill n maxVal v ps fuel pre) := by
  intro fuel
  induction fuel with
  | zero => intro pre; rw [genFill]; exact SPMF.IsPMF_pure _
  | succ f ih =>
    intro pre
    rw [genFill]
    exact SPMF.IsPMF_bind (SPMF.IsPMF_chooseNat _ _ _) fun _ => ih _

theorem genWorstCase.terminates {n maxVal : Nat} {hm : 1 ≤ maxVal} {hf : Feasible n} :
    IsAlmostSurelyTerminating (genWorstCase n maxVal hm hf) := by
  match n with
  | 0 => rw [genWorstCase]; exact SPMF.IsPMF_pure _
  | 1 =>
    rw [genWorstCase]
    exact SPMF.IsPMF_bind (SPMF.IsPMF_chooseNat _ _ _) fun _ => SPMF.IsPMF_pure _
  | n + 2 =>
    rw [genWorstCase]
    exact SPMF.IsPMF_bind (SPMF.IsPMF_chooseNat _ _ _) fun _ =>
      SPMF.IsPMF_bind (genPath_isPMF _ _) fun _ => genFill_isPMF _ _

private theorem isBounded_chooseNat {lo hi : Nat} {h : lo ≤ hi} :
    IsBounded (chooseNat lo hi h : SPMF.Cost Nat) (fun _ => 1) := by
  unfold chooseNat
  exact IsBounded_map IsBounded_choose (fun _ _ => le_rfl)

theorem genPath_cost {lim : Nat} : ∀ (d i : Nat),
    IsBounded (genPath lim i d : SPMF.Cost (List Nat)) (fun _ => d) := by
  intro d
  induction d with
  | zero => intro i; rw [genPath]; exact IsBounded_mono IsBounded_pure (fun _ => Nat.zero_le _)
  | succ d ih =>
    intro i
    have hb : ∀ (c j : Nat),
        IsBounded (do let qs ← (genPath lim j d : SPMF.Cost (List Nat)); return c :: qs)
          (fun _ => d) :=
      fun c j => IsBounded_bind (cf := fun _ _ => 0) (ih j) (fun _ => IsBounded_pure)
        (fun _ _ _ _ => by omega)
    rw [genPath]
    split
    · exact IsBounded_mono (IsBounded_pick (hb _ _) (hb _ _)) (fun _ => by omega)
    · exact IsBounded_mono (hb _ _) (fun _ => by omega)

theorem genFill_cost {n maxVal v : Nat} {ps : List Nat} : ∀ (fuel : Nat) (pre : List Nat),
    IsBounded (genFill n maxVal v ps fuel pre : SPMF.Cost (List Nat)) (fun _ => fuel) := by
  intro fuel
  induction fuel with
  | zero => intro pre; rw [genFill]; exact IsBounded_mono IsBounded_pure (fun _ => Nat.zero_le _)
  | succ f ih =>
    intro pre
    rw [genFill]
    exact IsBounded_bind (cf := fun _ _ => f) isBounded_chooseNat (fun _ => ih _)
      (fun _ _ _ _ => by omega)

/-- One choice for the sifted value, one per level of the path, and one per array position. -/
theorem genWorstCase.cost_bounded {n maxVal : Nat} {hm : 1 ≤ maxVal} {hf : Feasible n} :
    IsCostBounded (genWorstCase n maxVal hm hf) (fun _ => n + Nat.log 2 n + 1) := by
  match n with
  | 0 => rw [genWorstCase]; exact IsBounded_mono IsBounded_pure (fun _ => Nat.zero_le _)
  | 1 =>
    rw [genWorstCase]
    exact IsBounded_bind (cf := fun _ _ => 0) isBounded_chooseNat (fun _ => IsBounded_pure)
      (fun _ _ _ _ => by omega)
  | n + 2 =>
    rw [genWorstCase]
    refine IsBounded_bind (cf := fun _ _ => Nat.log 2 (n + 2) + (n + 2)) isBounded_chooseNat
      (fun _ => IsBounded_bind (cf := fun _ _ => n + 2) (genPath_cost _ _)
        (fun _ => genFill_cost _ _) (fun _ _ _ _ => by omega)) (fun _ _ _ _ => by omega)

/-! ## Bounding the node count -/

/-- The sizes up to `maxSize` that admit a worst-case heap. -/
def feasibleSizes (maxSize : Nat) : List Nat :=
  (List.range (maxSize + 1)).filter (fun n => decide (Feasible n))

theorem mem_feasibleSizes {maxSize n : Nat} :
    n ∈ feasibleSizes maxSize ↔ n ≤ maxSize ∧ Feasible n := by
  simp only [feasibleSizes, List.mem_filter, List.mem_range, decide_eq_true_eq]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩

theorem feasibleSizes_ne_nil {maxSize : Nat} : feasibleSizes maxSize ≠ [] :=
  List.ne_nil_of_mem (mem_feasibleSizes.mpr ⟨Nat.zero_le _, Or.inl (Nat.zero_le _)⟩)

/-- A worst-case heap of at most `maxSize` nodes, the benchmark's bound for heaps. The infeasible
sizes are dropped from the draw rather than filtered out of the results. -/
def genWorstCaseUpTo [Gen G] (maxSize maxVal : Nat) (hm : 1 ≤ maxVal) : G (List Nat) := do
  let n ← elements (feasibleSizes maxSize) feasibleSizes_ne_nil
  if hf : Feasible n then genWorstCase n maxVal hm hf else pure []

/-- The value drawn by `elements`, read off the cost interpretation's support. -/
private theorem cost_elements_mem {xs : List Nat} {hne : xs ≠ []} {a c : Nat}
    (h : (a, c) ∈ SPMF.support (elements xs hne : SPMF.Cost Nat)) : a ∈ xs := by
  simp only [elements] at h
  cost_support_simp at h
  obtain ⟨⟨i, hi⟩, n1, n2, -, hmem, -⟩ := h
  split at hmem
  simp only [SPMF.Cost.mem_support_pure_iff] at hmem
  exact hmem.1 ▸ List.getElem_mem _

theorem genWorstCaseUpTo.terminates {maxSize maxVal : Nat} {hm : 1 ≤ maxVal} :
    IsAlmostSurelyTerminating (genWorstCaseUpTo maxSize maxVal hm) := by
  rw [genWorstCaseUpTo]
  refine SPMF.IsPMF_bind (SPMF.IsPMF_elements _ _) fun _ => ?_
  split
  · exact genWorstCase.terminates
  · exact SPMF.IsPMF_pure _

theorem genWorstCaseUpTo.cost_bounded {maxSize maxVal : Nat} {hm : 1 ≤ maxVal} :
    IsCostBounded (genWorstCaseUpTo maxSize maxVal hm)
      (fun _ => maxSize + Nat.log 2 maxSize + 2) := by
  rw [genWorstCaseUpTo]
  refine IsBounded_bind (cf := fun n _ => n + Nat.log 2 n + 1) (IsBounded_elements _)
    (fun _ => ?_) ?_
  · split
    · exact genWorstCase.cost_bounded
    · exact IsBounded_mono IsBounded_pure (fun _ => Nat.zero_le _)
  rintro ⟨n, c1⟩ hn ⟨a, c2⟩ -
  have hle : n ≤ maxSize := (mem_feasibleSizes.mp (cost_elements_mem hn)).1
  have hlog : Nat.log 2 n ≤ Nat.log 2 maxSize := Nat.log_mono_right hle
  simp only
  omega

theorem genWorstCaseUpTo.sound_complete {maxSize maxVal : Nat} {hm : 1 ≤ maxVal} :
    IsSoundAndComplete (genWorstCaseUpTo maxSize maxVal hm)
      (fun a => a.length ≤ maxSize ∧ IsWorstCase a.length maxVal a) := by
  intro a
  rw [genWorstCaseUpTo]
  support_simp [mem_feasibleSizes]
  constructor
  · rintro ⟨n, ⟨hle, hfe⟩, ⟨h, hmem⟩ | ⟨hnf, -⟩⟩
    · obtain ⟨hlen, hheap, hdeq⟩ := (genWorstCase_mem_support a).mp hmem
      exact ⟨by omega, rfl, hheap, hdeq⟩
    · exact absurd hfe hnf
  · rintro ⟨hle, -, hheap, hdeq⟩
    have hfe : Feasible a.length := (exists_worst_case_iff hm).mp ⟨a, rfl, hheap, hdeq⟩
    exact ⟨a.length, ⟨hle, hfe⟩,
      Or.inl ⟨hfe, (genWorstCase_mem_support a).mpr ⟨rfl, hheap, hdeq⟩⟩⟩

end BinaryHeap
