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
    b ∈ (bind x f).support ↔ ∃ a ∈ x.support, b ∈ (f a).support := by
  simp [support, Function.mem_support, SPMF.bind, DFunLike.coe]

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
    b ∈ (pure a).support ↔ b = a := by
  simp [support, Function.mem_support, SPMF.pure, DFunLike.coe]

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
    simp [Pure.pure] at ha
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
      simp [Pure.pure]
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
    from `gs` that has non-zero weight `w` -/
private theorem frequencySelect_mem
    {gs : List (Nat × (Unit → SPMF α))}
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
        dsimp only [List.map_cons, List.sum_cons] at h
        omega
      obtain ⟨w', g', hwg_mem, hwg_pos, hwg_eq⟩ := ih h_remaining_weight
      exists w', g'
      constructor
      . -- (w', g') ∈ (w, g) :: tl
        apply List.mem_cons_of_mem
        assumption
      . -- 0 < w' ∧ frequencySelect tl (n - w) = g'
        constructor <;> assumption

/-- If a weighted generator `(w, g) ∈ gs` where the weight `w` is non-zero,
    then there exists `n` with a proof `h : n < sum (fst <$> gs)` such that
    `frequencySelect gs n h = g ()` -/
private theorem frequencySelect_n_exists
    {gs : List (Nat × (Unit → SPMF α))}
    {w : Nat}
    {g : Unit → SPMF α}
    (hmem : (w, g) ∈ gs)
    (hnonzero : 0 < w) :
    ∃ n, ∃ h : n < List.sum (List.map Prod.fst gs), Helpers.frequencySelect gs n h = g () := by
  induction gs with
  | nil => contradiction
  | cons hd tl ih =>
    rcases List.mem_cons.mp hmem with rfl | h_tl
    · -- hd = (w, g)
      refine ⟨0, ?_, ?_⟩
      · dsimp only [List.map_cons, List.sum_cons]
        omega
      · unfold Helpers.frequencySelect
        simp [hnonzero]
    · -- (w, g) ∈ tl
      obtain ⟨n, h_n, h_eq⟩ := ih h_tl
      obtain ⟨ w', _ ⟩ := hd
      refine ⟨w' + n, ?_, ?_⟩
      · -- w' + n < (fst <$> gs).sum
        dsimp only [List.map_cons, List.sum_cons]
        omega
      · -- frequencySelect gs n h = g ()
        unfold Helpers.frequencySelect
        have hcontra : ¬ (w' + n < w') := by omega
        simp only [hcontra]
        simp only [show w' + n - w' = n from by omega]
        dsimp
        assumption

/-- If the sum of weights in `gs` is non-zero, then the support of `frequency gs`
    is exactly the union of the support of the generators in `gs` with non-zero weights -/
@[simp]
theorem support_frequency
    {gs : List (Nat × (Unit → SPMF α))}
    (h_pos : 0 < List.sum (List.map Prod.fst gs)) :
    support (frequency gs h_pos) = {a | ∃ w g, ⟨ w, g ⟩ ∈ gs ∧ 0 < w ∧ a ∈ (g ()).support} := by
  ext a
  dsimp only [Set.mem_setOf_eq]
  constructor
  · -- a ∈ support (frequency gs h_pos) -> ∃ w g, (w, g) ∈ gs ∧ 0 < w ∧ a ∈ (g ()).support
    intro h
    simp only [frequency, Helpers.frequencyAux, support_bind, support_map, support_choose,
      mem_support_dite_iff] at h
    obtain ⟨i, h_idx, (⟨hlt, hsupp⟩ | ⟨hn, _⟩)⟩ := h
    · -- i < sum of weights ∧ a ∈ frequencySelect.support
      obtain ⟨w, g, hwg, hwg_pos, heq⟩ := frequencySelect_mem hlt
      rw [heq] at hsupp
      exists w, g
    ·  -- ¬(i < sum of weights) ∧ a ∈ default.support
      -- Contradiction: We have `i ≤ total - 1` and also `¬(i < total)` as hypotheses
      obtain ⟨n, ⟨_, h_upper⟩, hi⟩ := h_idx
      rw [← hi] at *
      contradiction
  · -- ∃ w g, (w, g) ∈ gs ∧ 0 < w ∧ a ∈ (g ()).support -> a ∈ support (frequency gs h_pos)
    simp only [frequency, Helpers.frequencyAux, support_bind, support_map, support_choose,
      mem_support_dite_iff]
    intro ⟨w, g, hwg_mem, hwt, ha⟩
    obtain ⟨n, hlt, heq⟩ := frequencySelect_n_exists hwg_mem hwt
    have hle : n ≤ (List.map Prod.fst gs).sum - 1 := by omega
    refine ⟨⟨ n, ⟨ by omega, hle ⟩ ⟩, ?_, ?_⟩
    . dsimp
      refine ⟨ ⟨ n, ⟨ by omega, hle ⟩ ⟩, ?_, ?_ ⟩
      . -- 0 ≤ n ∧ n ≤ (fst <$> gs).sum - 1
        apply Set.mem_univ
      . rfl
    . -- Goal: `a ∈ frequencySelect.support ∨ a ∈ default.support`
      -- (We pick the left branch)
      left
      exists hlt
      rw [heq]
      assumption

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

end support

end SPMF
