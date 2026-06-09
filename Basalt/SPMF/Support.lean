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
    (choose lo hi h : SPMF (ULift Nat)).support = {a | lo ≤ ULift.down a ∧ ULift.down a ≤ hi} := by
  ext a
  rw [support, Function.mem_support, Set.mem_setOf_eq]
  simp only [RandomChoice.choose, DFunLike.coe]
  constructor
  · intro ha
    by_contra hc
    push Not at hc
    apply ha
    by_cases hlo : lo ≤ a <;> grind
  · intro ⟨hlo, hhi⟩
    simp only [hlo, hhi, and_self, ↓reduceIte, ne_eq, one_div]
    exact ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _)

@[simp]
theorem mem_support_choose_iff :
    a ∈ (choose lo hi h : SPMF (ULift Nat)).support ↔ lo ≤ a.down ∧ a.down ≤ hi := by
  simp [support_choose]

@[simp]
theorem support_pick
    {x y : SPMF α} :
    (pick (fun () => x) (fun () => y)).support = x.support ∪ y.support := by
  simp only [pick, support_bind, support_choose]
  ext a
  simp only [Set.mem_setOf_eq, Set.mem_union]
  constructor
  · intro ⟨n, ⟨_, hn1⟩, ha⟩
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hn1
    · left; grind
    · right; grind
  · intro h
    cases h with
    | inl hx =>
      refine ⟨0, ⟨Nat.zero_le _, Nat.zero_le _⟩, ?_⟩
      simpa using hx
    | inr hy =>
      refine ⟨1, ⟨Nat.zero_le _, le_refl _⟩, ?_⟩
      simpa using hy

@[simp]
theorem mem_support_pick_iff
    {x y : SPMF α} :
    a ∈ (pick (fun () => x) (fun () => y)).support ↔ a ∈ x.support ∨ a ∈ y.support := by
  simp

/-- The support of `oneOf gs` is exactly the union of all generators in `gs` -/
@[simp]
theorem support_oneOf
    {gs : List (Unit → SPMF α)}
    (hne : gs ≠ []) :
    support (oneOf gs) = {a | ∃ g ∈ gs, a ∈ (g ()).support} := by
  simp only [oneOf, support_bind, support_map, support_choose]
  ext a
  dsimp only [Set.mem_setOf_eq]
  constructor
  . -- ∃ i ∈ [0, gs.length -1], a ∈ (gs[i]! ()).support → ∃ g ∈ gs, a ∈ (g ()).support
    intro h
    obtain ⟨ i, h_idx, ha ⟩ := h
    obtain ⟨ n, ⟨ h_lowerbound, h_upperbound ⟩, hi ⟩ := h_idx
    have h_pos : 0 < gs.length := by
      rw [List.length_pos_iff]
      assumption
    have h_lt : i < gs.length := by omega
    refine ⟨ gs[i], ?_, ?_ ⟩
    . -- Goal: `gs[i] ∈ gs`
      apply List.getElem_mem
    . -- Goal: `a ∈ (gs[i] ()).support`
      -- To do this, rewrite `gs[i]!` in terms of `gs[i]`
      rw [getElem!_pos gs i h_lt] at ha
      assumption
  . -- ∃ g ∈ gs, a ∈ (g ()).support → ∃ i ∈ [0, gs.length - 1], a ∈ (gs[i]! ()).support
    intros h
    obtain ⟨ g, hg, ha ⟩ := h
    obtain ⟨ i, hi, heq ⟩ := List.mem_iff_getElem.mp hg
    refine ⟨ i, ?_, ?_ ⟩
    . -- 0 ≤ i ≤ gs.length - 1
      exists ⟨ i ⟩
      dsimp
      omega
    . -- a ∈ (gs[i]! ()).support
      rw [getElem!_pos gs i hi]
      subst heq
      assumption

/-- Any element in the support of `oneOf gs` is in the support of some
    generator in `gs` -/
@[simp]
theorem mem_support_oneOf_iff
    {gs : List (Unit → SPMF α)}
    (hne : gs ≠ []) :
    a ∈ support (oneOf gs) ↔ ∃ g ∈ gs, a ∈ (g ()).support := by
  rw [support_oneOf hne]
  simp only [Set.mem_setOf_eq]


/-- If `n < sum (fst <$> gs)`, then `frequencyAux default gs n` picks a sub-generator
    from `gs` that has non-zero weight `w` -/
private theorem frequencyAux_mem
    {gs : List (Nat × (Unit → SPMF α))}
    {n : Nat}
    (h : n < List.sum (List.map Prod.fst gs)) :
    ∃ w g, ⟨ w, g ⟩ ∈ gs ∧ 0 < w ∧ (frequencyAux default gs n).snd = g () := by
  induction gs generalizing n with
  | nil => contradiction
  | cons hd tl ih =>
    unfold frequencyAux
    obtain ⟨ w, g ⟩ := hd
    split
    . -- n < w
      exists w, g
      constructor
      . -- (w, g) ∈ (w, g) :: tl
        apply List.mem_cons_self
      . -- 0 < w ∧ ((w, g).2 ()) = g ()
        constructor
        . omega
        . rfl
    · -- n >= w
      -- Assert that the remaining weight `(n - w)` is less than the sum
      -- of the weights in the tail of the list
      have h_remaining_weight : n - w < List.sum (List.map Prod.fst tl) := by
        dsimp only [List.map_cons, List.sum_cons] at h
        omega
      obtain ⟨w, g, hwg_mem, hwg_pos, hwg_eq⟩ := ih h_remaining_weight
      exists w, g
      constructor
      . apply List.mem_cons_of_mem
        assumption
      . constructor <;> assumption

/-- If a weighted generator `(w, g) ∈ gs` where the weight `w` is non-zero,
    then `frequencyAux default gs n` produces `(w, g)` if `n < sum (fst <$> gs)` -/
private theorem frequencyAux_n_exists
    {gs : List (Nat × (Unit → SPMF α))}
    {w : Nat}
    {g : Unit → SPMF α}
    (hmem : (w, g) ∈ gs)
    (hnonzero : 0 < w) :
    ∃ n, n < List.sum (List.map Prod.fst gs) ∧
      (frequencyAux default gs n).snd = g () := by
  induction gs with
  | nil => contradiction
  | cons hd tl ih =>
    rcases List.mem_cons.mp hmem with rfl | h_tl
    · -- hd = (w, g)
      refine ⟨0, ?_, ?_⟩
      · dsimp only [List.map_cons, List.sum_cons]
        omega
      · unfold frequencyAux
        simp [hnonzero]
    · -- (w, g) ∈ tl
      obtain ⟨n, _, _⟩ := ih h_tl
      obtain ⟨ w', _ ⟩ := hd
      refine ⟨w' + n, ?_, ?_⟩
      · -- w' + n < sum (fst <$> gs)
        dsimp only [List.map_cons, List.sum_cons]
        omega
      · -- (frequencyAux default gs (w' + n)).snd = g ()
        -- We need to unfold the body of `frequencyAux` to reason about
        -- which branch of the `if`-expression is taken
        unfold frequencyAux
        have hcontra : ¬ (w' + n < w') := by omega
        simp [hcontra]
        assumption

-- TODO: investigate the proof below

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
    simp only [frequency, support_bind, support_map, support_choose] at h
    obtain ⟨i, h_idx, ha⟩ := h
    obtain ⟨n, ⟨_, _⟩, hi⟩ := h_idx
    have h_lt : i < List.sum (List.map Prod.fst gs) := by omega
    obtain ⟨w, g, _, _, heq⟩ := frequencyAux_mem h_lt
    rw [heq] at ha
    refine ⟨w, g, ?_, ?_, ?_⟩ <;> assumption
  · -- ∃ w g, (w, g) ∈ gs ∧ 0 < w ∧ a ∈ (g ()).support -> a ∈ support (frequency gs h_pos)
    simp only [frequency, support_bind, support_map, support_choose]
    intro ⟨w, g, hwg_mem, hwt, ha⟩
    obtain ⟨n, hn_lt, hn_eq⟩ := frequencyAux_n_exists hwg_mem hwt
    dsimp only [Set.mem_setOf_eq]
    apply Exists.intro n
    constructor
    · -- ∃ a, (0 ≤ a.down ∧ a.down ≤ total - 1) ∧ n = a.down
      apply Exists.intro (ULift.up n)
      constructor
      · -- 0 ≤ n ∧ n ≤ total - 1
        constructor
        · -- 0 ≤ n
          omega
        · -- n ≤ total - 1
          show n ≤ (List.map Prod.fst gs).sum - 1
          omega
      · -- n = (ULift.up n).down
        rfl
    · -- a ∈ (frequencyAux default gs n).snd.support
      rw [hn_eq]
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
