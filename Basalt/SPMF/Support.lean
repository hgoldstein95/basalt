/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt.SPMF.Core
import Basalt.Combinators

open Lean.Order RandomChoice NNReal ENNReal MeasureTheory

/-!
# SPMF Support

This file sets up basic definitions for working with the support of `SPMF`s.

## Main Definitions

- `SPMF.support` — Defines the set of values that have nonzero mass in the distribution.
-/

namespace SPMF

section support

/-- The support of an `SPMF` is the set of values that have nonzero mass. -/
def support (p : SPMF α) : Set α := Function.support p

theorem mem_support_iff (p : SPMF α) (a : α) : a ∈ p.support ↔ p a ≠ 0 := Iff.rfl

/-- `SPMF.bind` is the monad's `>>=`. -/
theorem bind_eq (x : SPMF α) (f : α → SPMF β) : x.bind f = x >>= f := rfl

/-- `SPMF.pure` is the monad's `pure`. -/
theorem pure_eq (a : α) : (SPMF.pure a : SPMF α) = Pure.pure a := rfl

@[simp]
theorem support_countable (p : SPMF α) : p.support.Countable :=
  Summable.countable_support_ennreal (tsum_coe_ne_top p)

theorem apply_eq_zero_iff (p : SPMF α) (a : α) : p a = 0 ↔ a ∉ p.support := by
  rw [mem_support_iff, Classical.not_not]

theorem apply_pos_iff (p : SPMF α) (a : α) : 0 < p a ↔ a ∈ p.support :=
  pos_iff_ne_zero.trans (p.mem_support_iff a).symm

@[simp]
theorem support_bind
    {x : SPMF α}
    {f : α → SPMF β} :
    (x >>= f).support = {b | ∃ a, a ∈ x.support ∧ b ∈ (f a).support} := by
  ext b
  simp only [support, Function.mem_support, Set.mem_setOf_eq]
  constructor
  · intro h
    by_contra hc
    push Not at hc
    have hzero : ∀ a, x a * f a b = 0 := fun a => by
      by_cases ha : x a = 0
      · simp [ha]
      · simp [hc a ha]
    apply h
    change (∑' a, x a * f a b) = 0
    simp only [hzero, tsum_zero]
  · intro ⟨a, ha, hb⟩
    apply ne_of_gt
    change 0 < (∑' a', x a' * f a' b)
    calc 0 < x a * f a b := ENNReal.mul_pos ha hb
      _ ≤ ∑' a, x a * f a b := ENNReal.le_tsum a

@[simp]
theorem mem_support_bind_iff
    {x : SPMF α}
    {f : α → SPMF β} :
    b ∈ (x >>= f).support ↔ ∃ a ∈ x.support, b ∈ (f a).support := by
  simp [support_bind]

@[simp]
theorem support_pure :
    (Pure.pure a : SPMF _).support = {a} := by
  classical
  ext x
  simp only [support, Function.mem_support, Set.mem_singleton_iff]
  constructor
  · intro h
    by_contra hne
    apply h
    show (if x = a then (1 : ℝ≥0∞) else 0) = 0
    simp [hne]
  · intro h
    show (if x = a then (1 : ℝ≥0∞) else 0) ≠ 0
    simp [h]

@[simp]
theorem mem_support_pure_iff :
    b ∈ (Pure.pure a : SPMF α).support ↔ b = a := by
  simp [support_pure]

@[simp]
theorem support_map
    {x : SPMF α}
    {f : α → β} :
    (f <$> x).support = {b | ∃ a, a ∈ x.support ∧ b = f a} := by
  rw [← LawfulMonad.bind_pure_comp]
  simp only [support_bind, support_pure]
  grind

@[simp]
theorem mem_support_map_iff
    {x : SPMF α}
    {f : α → β} :
    b ∈ (f <$> x).support ↔ ∃ a ∈ x.support, b = f a := by
  simp [support_map]

@[simp]
theorem mem_support_dite_iff {p : Prop} [Decidable p]
    {t : p → SPMF α} {e : ¬p → SPMF α} :
    a ∈ (dite p t e).support ↔ (∃ h : p, a ∈ (t h).support) ∨ (∃ h : ¬p, a ∈ (e h).support) := by
  by_cases hp : p <;> simp_all

@[simp]
theorem mem_support_ite_iff {p : Prop} [Decidable p]
    {t e : SPMF α} :
    a ∈ (ite p t e).support ↔ (p ∧ a ∈ t.support) ∨ (¬p ∧ a ∈ e.support) := by
  by_cases hp : p <;> simp_all

@[simp]
theorem support_choose :
    (choose lo hi h : SPMF (ULift {x : Nat // lo ≤ x ∧ x ≤ hi})).support = Set.univ := by
  ext a
  simp only [mem_support_iff, Set.mem_univ, iff_true]
  change (1 : ℝ≥0∞) / ((hi - lo + 1 : ℕ)) ≠ 0
  simp

@[simp]
theorem mem_support_choose_iff :
    a ∈ (choose lo hi h : SPMF (ULift {x : Nat // lo ≤ x ∧ x ≤ hi})).support ↔ True := by
  simp [support_choose]

@[simp]
theorem support_pick
    {x y : SPMF α} :
    (pick (fun () => x) (fun () => y)).support = x.support ∪ y.support := by
  simp only [pick, support_bind, support_choose]
  ext a
  simp only [Set.mem_univ, true_and, Set.mem_setOf_eq, Set.mem_union]
  constructor
  · rintro ⟨n, ha⟩
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp n.down.property.2 with h0 | h1
    · left; simpa [h0] using ha
    · right; simpa [h1] using ha
  · intro h
    cases h with
    | inl hx => exact ⟨⟨⟨0, by omega⟩⟩, by simpa using hx⟩
    | inr hy => exact ⟨⟨⟨1, by omega⟩⟩, by simpa using hy⟩

@[simp]
theorem mem_support_pick_iff
    {x y : SPMF α} :
    a ∈ (pick (fun () => x) (fun () => y)).support ↔ a ∈ x.support ∨ a ∈ y.support := by
  simp

@[simp]
theorem mem_support_chooseNat_iff {lo hi : Nat} {h : lo ≤ hi} {n : Nat} :
    n ∈ (chooseNat lo hi h : SPMF Nat).support ↔ lo ≤ n ∧ n ≤ hi := by
  unfold chooseNat
  simp only [mem_support_map_iff, mem_support_choose_iff, true_and]
  constructor
  · rintro ⟨a, rfl⟩
    exact a.down.property
  · rintro ⟨h1, h2⟩
    exact ⟨⟨⟨n, h1, h2⟩⟩, rfl⟩

/-- The support of `vectorOf n g` is the set of all length-`n` list where
    each element is in `g`'s support -/
theorem support_vectorOf
    {n : Nat}
    {g : SPMF α} :
    support (vectorOf n g) = { xs | List.length xs = n ∧ ∀ x ∈ xs, x ∈ g.support } := by
  induction n with
  | zero =>
    simp [vectorOf]
    ext a
    dsimp only [Set.mem_setOf_eq]
    constructor
    . intro h
      rw [Set.mem_singleton_iff] at h
      constructor
      . assumption
      . intro x hmem
        subst h
        contradiction
    . intro h
      obtain ⟨heq, hmem⟩ := h
      apply Set.mem_singleton_iff.mpr
      assumption
  | succ n' IH =>
    rw [vectorOf_succ]
    ext xs
    simp [Set.mem_setOf_eq]
    constructor
    . -- Forwards direction
      intro h
      obtain ⟨x, ⟨hmem, ⟨xs, ⟨hxs, hcons⟩⟩⟩⟩ := h
      subst hcons
      rw [IH] at hxs
      dsimp at hxs
      obtain ⟨hlen, hsupp⟩ := hxs
      constructor
      . simp
        assumption
      . -- ∀ y ∈ x :: xs, y ∈ g.support
        intro y hy
        rw [List.mem_cons] at hy
        obtain ⟨heq, hy⟩ := hy
        . assumption
        . apply hsupp
          assumption
    . -- Backwards direction
      intro ⟨hlen, hmem⟩
      -- Since we know `hlen: xs.length = n' + 1`,
      -- we must have `xs = y :: ys` for some `y, ys`
      obtain ⟨y, ys, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
      exists y
      constructor
      . apply hmem
        apply List.mem_cons_self
      . exists ys
        constructor
        . rw [IH]
          apply Set.mem_sep
          . simp at hlen
            assumption
          . intro x hx
            apply hmem
            apply List.mem_cons_of_mem
            assumption
        . rfl

/-- `xs` is in the support of `vectorOf n g` iff `xs` has length `n`
    and all elements of `xs` are in `g`'s support -/
@[simp]
theorem mem_support_vectorOf_iff
    {n : Nat}
    {g : SPMF α} :
    xs ∈ (vectorOf n g).support ↔ xs.length = n ∧ ∀ x ∈ xs, x ∈ g.support := by
  simp [support_vectorOf]


/-- The support of `listOfMaxLength n g` is the set of all lists with length
    at most `n`, where each element is in `g`'s support -/
theorem support_listOfMaxLength
    {n : Nat}
    {g : SPMF α} :
    support (listOfMaxLength n g) = { xs | List.length xs ≤ n ∧ ∀ x ∈ xs, x ∈ g.support } := by
  simp [listOfMaxLength]

@[simp]
theorem mem_support_listOfMaxLength_iff
    {n : Nat}
    {g : SPMF α} :
    xs ∈ (listOfMaxLength n g).support ↔ xs.length ≤ n ∧ ∀ x ∈ xs, x ∈ g.support := by
  simp [support_listOfMaxLength]

/-- The support of `listOf g` is the set of all lists where each element
    is in `g`'s support -/
theorem support_listOf
    {g : SPMF α} :
    support (listOf g) = { xs | ∀ x ∈ xs, x ∈ g.support } := by
  ext xs
  induction xs with
  | nil =>
    dsimp
    constructor
    . intro h x hvacuous
      contradiction
    . intro h
      unfold listOf
      simp [support_pick]
  | cons x xs' IH =>
    constructor
    . dsimp
      intro h y hy
      -- Case on y ∈ x :: xs' (whether y = x or y ∈ xs')
      cases hy with
      | head =>
        -- y = x
        unfold listOf at h
        simp [support_pick] at h
        obtain ⟨h1, _⟩ := h
        assumption
      | tail =>
        -- y ∈ xs'
        rename_i hy
        unfold listOf at h
        simp [support_pick] at h
        obtain ⟨_, h2⟩ := h
        rw [IH] at h2
        apply h2
        assumption
    . intro h
      rw [Set.mem_setOf_eq] at h
      unfold listOf
      simp [support_pick]
      constructor
      . apply h
        apply List.mem_cons_self
      . apply IH.mpr
        rw [Set.mem_setOf_eq]
        intro x hx
        apply h
        apply List.mem_cons_of_mem
        assumption

@[simp]
theorem mem_support_listOf
    {xs : List α}
    {g : SPMF α} :
    xs ∈ (listOf g).support ↔ xs ∈ {xs | ∀ x ∈ xs, x ∈ g.support} := by
  simp [support_listOf]

/-- The support of `elements xs` is exactly the set of all elements in `xs` -/
@[simp]
theorem support_elements
    {xs : List α}
    (hne : xs ≠ []) :
    support (elements xs hne) = { x | x ∈ xs } := by
  simp only [elements, support_bind, support_map, support_choose]
  ext a
  dsimp only [Set.mem_setOf_eq]
  constructor
  . -- (∃ i ≤ xs.length - 1, a = xs[i]?.getD default) → a ∈ xs
    intro h
    obtain ⟨ ⟨i, ⟨ hi_gt, hi_lt⟩⟩, h_idx, ha ⟩ := h
    obtain ⟨ ⟨ n, ⟨ hgt, hlt ⟩⟩, ⟨ h_lowerbound, h_upperbound ⟩, hi ⟩ := h_idx
    have h_pos : 0 < xs.length := by
      rw [List.length_pos_iff]
      assumption
    have h_lt : i < xs.length := by omega
    dsimp at ha
    simp only [mem_support_pure_iff] at ha
    apply List.mem_of_getElem (id (Eq.symm ha))
  . -- a ∈ xs → ∃ i ≤ xs.length - 1, a = xs[i]?.getD default
    intro hmem
    obtain ⟨ i, hlt, heq ⟩ := List.mem_iff_getElem.mp hmem
    have hle : i ≤ xs.length - 1 := by omega
    exists ⟨ i, ⟨by omega, hle⟩⟩
    constructor
    . exists ⟨ i, ⟨by omega, hle⟩⟩
    . have hidx : xs[i]? = some a := by
        rw [← heq]
        apply List.getElem?_eq_getElem hlt
      dsimp
      simp only [mem_support_pure_iff]
      apply (Eq.symm heq)

/-- `a` is in the support of `elements xs` if and only if `a ∈ xs` -/
@[simp]
theorem mem_support_elements_iff
    [Inhabited α]
    {xs : List α}
    (hne : xs ≠ []) :
    a ∈ support (elements xs hne) ↔ a ∈ xs := by
  simp [support_elements]

/-- The support of `oneOf gs` is exactly the union of all generators in `gs` -/
@[simp]
theorem support_oneOf
    {gs : List (Unit → SPMF α)}
    (hne : gs ≠ []) :
    support (oneOf gs hne) = {a | ∃ g ∈ gs, a ∈ (g ()).support} := by
  simp only [oneOf, Helpers.oneOfAux, support_bind, support_map, support_choose]
  ext a
  dsimp only [Set.mem_setOf_eq]
  constructor
  . -- ∃ i ∈ [0, gs.length -1], a ∈ (gs[i]! ()).support → ∃ g ∈ gs, a ∈ (g ()).support
    intro h
    obtain ⟨ ⟨i, ⟨ hi_gt, hi_lt⟩⟩, h_idx, ha ⟩ := h
    obtain ⟨ ⟨ n, ⟨ hgt, hlt ⟩⟩, ⟨ h_lowerbound, h_upperbound ⟩, hi ⟩ := h_idx
    have h_pos : 0 < gs.length := by
      rw [List.length_pos_iff]
      assumption
    have h_lt : i < gs.length := by omega
    refine ⟨ gs[i], ?_, ?_ ⟩
    . -- Goal: `gs[i] ∈ gs`
      apply List.getElem_mem
    . -- Goal: `a ∈ (gs[i] ()).support`
      -- To do this, rewrite `gs[i]!` in terms of `gs[i]`
      dsimp at ha
      assumption
  . -- ∃ g ∈ gs, a ∈ (g ()).support → ∃ i ∈ [0, gs.length - 1], a ∈ (gs[i]! ()).support
    intros h
    obtain ⟨ g, hg, ha ⟩ := h
    obtain ⟨ i, hi, heq ⟩ := List.mem_iff_getElem.mp hg
    have hge : 0 ≤ i := by
      apply Nat.zero_le
    have hle : i ≤ gs.length - 1 := by
      apply Nat.le_sub_one_of_lt
      assumption
    refine ⟨ ⟨i, hge, hle ⟩, ?_, ?_ ⟩
    . -- 0 ≤ i ≤ gs.length - 1
      exists ⟨ i, ⟨hge, hle⟩ ⟩
    . -- a ∈ (gs[i]! ()).support
      dsimp
      subst heq
      assumption

/-- Any element in the support of `oneOf gs` is in the support of some
    generator in `gs` -/
@[simp]
theorem mem_support_oneOf_iff
    {gs : List (Unit → SPMF α)}
    (hne : gs ≠ []) :
    a ∈ support (oneOf gs hne) ↔ ∃ g ∈ gs, a ∈ (g ()).support := by
  simp [support_oneOf]



/-- If `n < sum (fst <$> gs)`, then `frequencySelect gs n h` picks a sub-generator
    from `gs` that has non-zero weight `w`.

    Note: this lemma is parameterized over `Gen G`, not `SPMF`, as it is used
    for cost lemmas about `frequency` (i.e. `G` is instantiated with `SPMF.Cost`). -/
theorem frequencySelect_mem [Gen G]
    {gs : List (Nat × (Unit → G α))}
    {n : Nat}
    (h : n < (List.map Prod.fst gs).sum) :
    ∃ w g, ⟨ w, g ⟩ ∈ gs ∧ 0 < w ∧ Helpers.frequencySelect gs n h = g () := by
  induction gs generalizing n with
  | nil => simp at h
  | cons hd tl ih =>
    unfold Helpers.frequencySelect
    obtain ⟨ w, g ⟩ := hd
    split
    · -- n < w
      exists w, g
      constructor
      . -- (w, g) ∈ (w, g) :: tl
        apply List.Mem.head
      . -- 0 < w ∧ fst (w, g) () = g ()
        constructor
        . omega
        . rfl
    · -- n >= w
      have h_remaining_weight : n - w < List.sum (List.map Prod.fst tl) := by
        simp only [List.map_cons, List.sum_cons] at h
        omega
      obtain ⟨w', g', hwg_mem, hwg_pos, hwg_eq⟩ := ih h_remaining_weight
      exists w', g'
      constructor
      . -- (w', g') ∈ (w, g) :: tl
        apply List.mem_cons_of_mem
        assumption
      . -- 0 < w' ∧ frequencySelect tl (n - w) = g'
        constructor <;> assumption

/-- Summing `frequencySelect` over all values of the uniform draw counts each branch
    `(w, g)` exactly `w` times. -/
private theorem sum_frequencySelect_apply
    (gs : List (Nat × (Unit → SPMF α))) (a : α) :
    ∑ n ∈ Finset.range ((gs.map Prod.fst).sum),
        (if h : n < (gs.map Prod.fst).sum then Helpers.frequencySelect gs n h a else 0)
      = (gs.map fun p => (p.1 : ℝ≥0∞) * (p.2 ()) a).sum := by
  induction gs with
  | nil => simp
  | cons hd tl ih =>
    obtain ⟨k, g⟩ := hd
    have hS : ((((k, g) :: tl).map Prod.fst).sum) = k + (tl.map Prod.fst).sum := by simp
    -- Rewriting the summand to a total function of `n` first keeps the range split below
    -- from having to transport the `frequencySelect` proof arguments.
    have hsummand : ∀ n ∈ Finset.range ((((k, g) :: tl).map Prod.fst).sum),
        (if h : n < (((k, g) :: tl).map Prod.fst).sum
          then Helpers.frequencySelect ((k, g) :: tl) n h a else 0)
          = if n < k then g () a
            else (if h : n - k < (tl.map Prod.fst).sum
                  then Helpers.frequencySelect tl (n - k) h a else 0) := by
      intro n hn
      have hn' : n < (((k, g) :: tl).map Prod.fst).sum := Finset.mem_range.mp hn
      rw [dif_pos hn']
      simp only [Helpers.frequencySelect]
      by_cases hlt : n < k
      · rw [dif_pos hlt, if_pos hlt]
      · rw [dif_neg hlt, if_neg hlt, dif_pos (by omega)]
    rw [Finset.sum_congr rfl hsummand, hS]
    rw [Finset.range_eq_Ico,
      ← Finset.sum_Ico_consecutive _ (Nat.zero_le k) (Nat.le_add_right k _)]
    have hfirst : ∑ n ∈ Finset.Ico 0 k,
        (if n < k then g () a
          else (if h : n - k < (tl.map Prod.fst).sum
                then Helpers.frequencySelect tl (n - k) h a else 0))
          = (k : ℝ≥0∞) * g () a := by
      rw [Finset.sum_congr rfl (fun n hn => if_pos (Finset.mem_Ico.mp hn).2),
        Finset.sum_const, Nat.card_Ico, Nat.sub_zero, nsmul_eq_mul]
    have hsecond : ∑ n ∈ Finset.Ico k (k + (tl.map Prod.fst).sum),
        (if n < k then g () a
          else (if h : n - k < (tl.map Prod.fst).sum
                then Helpers.frequencySelect tl (n - k) h a else 0))
          = (tl.map fun p => (p.1 : ℝ≥0∞) * (p.2 ()) a).sum := by
      rw [Finset.sum_Ico_eq_sum_range,
        show k + (tl.map Prod.fst).sum - k = (tl.map Prod.fst).sum from by omega]
      have h2 : ∀ n ∈ Finset.range ((tl.map Prod.fst).sum),
          (if k + n < k then g () a
            else (if h : k + n - k < (tl.map Prod.fst).sum
                  then Helpers.frequencySelect tl (k + n - k) h a else 0))
            = (if h : n < (tl.map Prod.fst).sum
                then Helpers.frequencySelect tl n h a else 0) := by
        intro n _
        rw [if_neg (by omega)]
        simp only [Nat.add_sub_cancel_left]
      rw [Finset.sum_congr rfl h2]
      exact ih
    rw [hfirst, hsecond]
    simp

/-- Branch `j` of `frequency` fires with probability `wⱼ / Σᵢ wᵢ`.

    The sums are `List.sum`s, not `Finset` sums: duplicate `(weight, generator)` pairs are
    distinct branches, and a `Finset` sum would collapse them. -/
@[simp]
theorem frequency_apply
    (gs : List (Nat × (Unit → SPMF α))) (h : 0 < (gs.map Prod.fst).sum) (a : α) :
    frequency gs h a
      = (gs.map fun p => (p.1 : ℝ≥0∞) * (p.2 ()) a).sum / ((gs.map Prod.fst).sum : ℝ≥0∞) := by
  unfold frequency Helpers.frequencyAux
  rw [bind_map_left, bind_apply]
  simp only [choose_apply, apply_dite (fun p : SPMF α => p a), default_apply]
  trans (∑ n ∈ Finset.Icc 0 ((gs.map Prod.fst).sum - 1),
      (fun n : Nat => (1 / (((gs.map Prod.fst).sum - 1 - 0 + 1 : ℕ) : ℝ≥0∞)) *
        (if hn : n < (gs.map Prod.fst).sum
          then Helpers.frequencySelect gs n hn a else 0)) n)
  · exact tsum_subtype_Icc 0 ((gs.map Prod.fst).sum - 1)
      (fun n : Nat => (1 / (((gs.map Prod.fst).sum - 1 - 0 + 1 : ℕ) : ℝ≥0∞)) *
        (if hn : n < (gs.map Prod.fst).sum
          then Helpers.frequencySelect gs n hn a else 0))
  · have hIcc : Finset.Icc 0 ((gs.map Prod.fst).sum - 1)
        = Finset.range ((gs.map Prod.fst).sum) := by
      ext n
      simp only [Finset.mem_Icc, Finset.mem_range]
      omega
    have hT : (gs.map Prod.fst).sum - 1 - 0 + 1 = (gs.map Prod.fst).sum := by omega
    rw [hIcc, hT, ← Finset.mul_sum, sum_frequencySelect_apply, one_div,
      div_eq_mul_inv, mul_comm]

/-- If the sum of weights in `gs` is non-zero, then the support of `frequency gs`
    is exactly the union of the support of the generators in `gs` with non-zero weights -/
@[simp]
theorem support_frequency
    {gs : List (Nat × (Unit → SPMF α))}
    (h_pos : 0 < List.sum (List.map Prod.fst gs)) :
    support (frequency gs h_pos) = {a | ∃ w g, ⟨ w, g ⟩ ∈ gs ∧ 0 < w ∧ a ∈ (g ()).support} := by
  ext a
  rw [mem_support_iff, frequency_apply gs h_pos a, Set.mem_setOf_eq, ne_eq,
    ENNReal.div_eq_zero_iff]
  simp only [ENNReal.natCast_ne_top, or_false, List.sum_eq_zero_iff, List.forall_mem_map,
    mul_eq_zero, Nat.cast_eq_zero, not_forall, Prod.exists, mem_support_iff,
    Nat.pos_iff_ne_zero]
  grind

/-- Membership form of `support_frequency`. -/
@[simp]
theorem mem_support_frequency_iff
    {gs : List (Nat × (Unit → SPMF α))}
    (h_pos : 0 < List.sum (List.map Prod.fst gs)) :
    a ∈ (frequency gs h_pos).support ↔ ∃ w g, (w, g) ∈ gs ∧ 0 < w ∧ a ∈ (g ()).support := by
  simp [support_frequency]

theorem bind_congr_support
    {x : SPMF α}
    (h : ∀ a ∈ x.support, f a = g a) :
    bind x f = bind x g := by
  simp only [bind]
  ext a
  simp only [DFunLike.coe]
  congr
  funext v
  by_cases hsupport : v ∈ x.support
  · rw [h]; assumption
  · simp only [support, Function.notMem_support] at hsupport
    simp_all [DFunLike.coe]

private theorem csup_apply {c : SPMF α → Prop} (hc : chain c) (a : α) :
    (CCPO.csup hc) a = ⨆ f, ⨆ (_ : c f), f a := by
  have hge : ∀ b, ⨆ f, ⨆ (_ : c f), f b ≤ (CCPO.csup hc) b :=
    fun b => iSup₂_le (fun f hf => le_csup hc hf b)
  have hsum : ∑' b, ⨆ f, ⨆ (_ : c f), f b ≤ 1 :=
    (ENNReal.tsum_le_tsum hge).trans (tsum_coe _)
  exact le_antisymm
    ((csup_le hc (fun f hf b => le_iSup₂_of_le f hf le_rfl) :
        CCPO.csup hc ⊑ ⟨fun b => ⨆ f, ⨆ (_ : c f), f b, hsum⟩) a)
    (hge a)

theorem mem_support_csup {c : SPMF α → Prop} (hc : chain c) {a : α} :
    a ∈ (CCPO.csup hc).support ↔ ∃ f, c f ∧ a ∈ f.support := by
  simp only [mem_support_iff, csup_apply, ne_eq]
  constructor
  · intro h
    by_contra h'
    push Not at h'
    simp_all
  · rintro ⟨f, hcf, haf⟩ h
    simp_all

/-- Reweighting a uniform choice preserves its support. Replacing `oneOf gs` by a `frequency`
over the same branches leaves the set of reachable values unchanged, provided every weight is
positive. -/
theorem support_frequency_reweight
    {gs : List (Unit → SPMF α)} {gs' : List (Nat × (Unit → SPMF α))}
    (hsnd : gs'.map Prod.snd = gs) (hpos : ∀ p ∈ gs', 0 < p.1)
    (hne : gs ≠ []) (h_pos : 0 < List.sum (List.map Prod.fst gs')) :
    support (frequency gs' h_pos) = support (oneOf gs hne) := by
  subst hsnd
  rw [support_frequency, support_oneOf]
  ext a
  simp only [Set.mem_setOf_eq, List.mem_map]
  constructor
  · rintro ⟨w, g, hmem, _, ha⟩
    exact ⟨g, ⟨(w, g), hmem, rfl⟩, ha⟩
  · rintro ⟨g, ⟨⟨w, g'⟩, hmem, hg⟩, ha⟩
    cases hg
    exact ⟨w, g', hmem, hpos _ hmem, ha⟩

/-- The same, between two `frequency`s. This is the shape a tuning rewrite has: `tunable def`
replaces literal weights by `Tuning.weight θ i d` in place, so both sides are already `frequency`s
and only the weights differ. -/
theorem support_frequency_congr_weights
    {gs gs' : List (Nat × (Unit → SPMF α))}
    (hsnd : gs'.map Prod.snd = gs.map Prod.snd)
    (hpos : ∀ p ∈ gs', 0 < p.1) (hpos' : ∀ p ∈ gs, 0 < p.1)
    (h : 0 < List.sum (List.map Prod.fst gs)) (h' : 0 < List.sum (List.map Prod.fst gs')) :
    support (frequency gs' h') = support (frequency gs h) := by
  rw [support_frequency, support_frequency]
  ext a
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨w, g, hmem, _, ha⟩
    have : g ∈ gs.map Prod.snd := hsnd ▸ List.mem_map.mpr ⟨(w, g), hmem, rfl⟩
    obtain ⟨⟨w', g'⟩, hmem', hg⟩ := List.mem_map.mp this
    cases hg
    exact ⟨w', g', hmem', hpos' _ hmem', ha⟩
  · rintro ⟨w, g, hmem, _, ha⟩
    have : g ∈ gs'.map Prod.snd := hsnd ▸ List.mem_map.mpr ⟨(w, g), hmem, rfl⟩
    obtain ⟨⟨w', g'⟩, hmem', hg⟩ := List.mem_map.mp this
    cases hg
    exact ⟨w', g', hmem', hpos _ hmem', ha⟩

end support

end SPMF
