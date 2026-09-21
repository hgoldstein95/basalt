/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt.Obs.Spec
import Basalt.Obs.Combinators

/-!
# Presentations of a Choice in `Prop`

How a choice presents for each shape a combinator makes it in (a plain range, a binary choice, a
threshold, a list index, a weighted selection), demonically (`Mix.demonic`, a `∀`) and angelically
(`Mix.angelic`, an `∃`). These are facts about quantifiers over a range, not about combinators.
-/

namespace Mix

variable {lo hi : Nat}

/-! ## Demonic -/

theorem range_demonic (F : ULift.{u} {x : Nat // lo ≤ x ∧ x ≤ hi} → Prop) :
    Mix.demonic.mix lo hi F ↔ ∀ x (hx : lo ≤ x ∧ x ≤ hi), F ⟨⟨x, hx⟩⟩ :=
  ⟨fun h x hx => h ⟨⟨x, hx⟩⟩, fun h a => h a.down.val a.down.property⟩

theorem binary_demonic (F : ULift.{u} {x : Nat // 0 ≤ x ∧ x ≤ 1} → Prop) :
    Mix.demonic.mix 0 1 F ↔ F ⟨⟨0, by omega⟩⟩ ∧ F ⟨⟨1, by omega⟩⟩ := by
  refine ⟨fun h => ⟨h _, h _⟩, ?_⟩
  rintro ⟨h0, h1⟩ ⟨⟨x, hx⟩⟩
  obtain rfl | rfl : x = 0 ∨ x = 1 := by omega
  · exact h0
  · exact h1

theorem threshold_demonic {d : Nat} {k : Int} (hd : 0 < d) (t e : Prop) :
    Mix.demonic.mix 0 (d - 1)
        (fun a : ULift.{u} {x : Nat // 0 ≤ x ∧ x ≤ d - 1} => if (a.down.val : Int) < k then t else e)
      ↔ (0 < k → t) ∧ (k < d → e) := by
  constructor
  · intro h
    refine ⟨fun hk => ?_, fun hk => ?_⟩
    · simpa [hk] using h ⟨⟨0, by omega⟩⟩
    · have : if ((d - 1 : Nat) : Int) < k then t else e := h ⟨⟨d - 1, by omega⟩⟩
      rwa [if_neg (by omega)] at this
  · rintro ⟨ht, he⟩ ⟨⟨x, hx⟩⟩
    show if (x : Int) < k then t else e
    split
    · exact ht (by omega)
    · exact he (by omega)

theorem index_demonic {γ : Type v} (l : List γ) (hne : l ≠ []) (F : γ → Prop) :
    Mix.demonic.mix 0 (l.length - 1)
        (fun a : ULift.{u} {x : Nat // 0 ≤ x ∧ x ≤ l.length - 1} =>
          F (l[a.down.val]'(Obs.idx_lt hne a.down.property)))
      ↔ ∀ g ∈ l, F g := by
  have := List.length_pos_iff.mpr hne
  constructor
  · intro h g hg
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hg
    exact h ⟨⟨i, by omega⟩⟩
  · intro h a
    exact h _ (List.getElem_mem _)

private theorem selectD_forall (l : List (Nat × Prop)) (d : Prop) :
    (∀ n, n < (l.map Prod.fst).sum → Obs.selectD l n d) ↔ ∀ p ∈ l, 0 < p.1 → p.2 := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    obtain ⟨k, x⟩ := hd
    simp only [List.map_cons, List.sum_cons, Obs.selectD, List.forall_mem_cons, ← ih]
    constructor
    · intro h
      refine ⟨fun hk => by simpa [hk] using h 0 (by omega), fun n hn => ?_⟩
      have := h (k + n) (by omega)
      rwa [if_neg (by omega), Nat.add_sub_cancel_left] at this
    · rintro ⟨hx, htl⟩ n hn
      split
      · exact hx (by omega)
      · exact htl _ (by omega)

theorem select_demonic (l : List (Nat × Prop)) {T : Nat} (hT : T = (l.map Prod.fst).sum)
    (hpos : 0 < T) (d : Prop) :
    Mix.demonic.mix 0 (T - 1)
        (fun a : ULift.{u} {x : Nat // 0 ≤ x ∧ x ≤ T - 1} => Obs.selectD l a.down.val d)
      ↔ ∀ p ∈ l, 0 < p.1 → p.2 := by
  rw [← selectD_forall l d, ← hT]
  exact ⟨fun h n hn => h ⟨⟨n, by omega⟩⟩, fun h a => h _ (by have := a.down.property; omega)⟩

/-! ## Prop -/

theorem range_angelic (F : ULift.{u} {x : Nat // lo ≤ x ∧ x ≤ hi} → Prop) :
    Mix.angelic.mix lo hi F ↔ ∃ x, ∃ hx : lo ≤ x ∧ x ≤ hi, F ⟨⟨x, hx⟩⟩ :=
  ⟨fun ⟨a, h⟩ => ⟨a.down.val, a.down.property, h⟩, fun ⟨x, hx, h⟩ => ⟨⟨⟨x, hx⟩⟩, h⟩⟩

private theorem exists_binary (F : ULift.{u} {x : Nat // 0 ≤ x ∧ x ≤ 1} → Prop) :
    (∃ a, F a) ↔ F ⟨⟨0, by omega⟩⟩ ∨ F ⟨⟨1, by omega⟩⟩ := by
  constructor
  · rintro ⟨⟨⟨x, hx⟩⟩, h⟩
    obtain rfl | rfl : x = 0 ∨ x = 1 := by omega
    · exact Or.inl h
    · exact Or.inr h
  · rintro (h | h)
    · exact ⟨_, h⟩
    · exact ⟨_, h⟩

theorem binary_angelic (F : ULift.{u} {x : Nat // 0 ≤ x ∧ x ≤ 1} → Prop) :
    Mix.angelic.mix 0 1 F ↔ F ⟨⟨0, by omega⟩⟩ ∨ F ⟨⟨1, by omega⟩⟩ :=
  exists_binary F

private theorem exists_threshold {d : Nat} {k : Int} (hd : 0 < d) (t e : Prop) :
    (∃ a : ULift.{u} {x : Nat // 0 ≤ x ∧ x ≤ d - 1}, if (a.down.val : Int) < k then t else e)
      ↔ (0 < k ∧ t) ∨ (k < d ∧ e) := by
  constructor
  · rintro ⟨⟨⟨x, hx⟩⟩, h⟩
    have h : if (x : Int) < k then t else e := h
    split at h
    · exact Or.inl ⟨by omega, h⟩
    · exact Or.inr ⟨by omega, h⟩
  · rintro (⟨hk, h⟩ | ⟨hk, h⟩)
    · refine ⟨⟨⟨0, by omega⟩⟩, ?_⟩
      show if ((0 : Nat) : Int) < k then t else e
      rwa [if_pos (by omega)]
    · refine ⟨⟨⟨d - 1, by omega⟩⟩, ?_⟩
      show if ((d - 1 : Nat) : Int) < k then t else e
      rwa [if_neg (by omega)]

theorem threshold_angelic {d : Nat} {k : Int} (hd : 0 < d) (t e : Prop) :
    Mix.angelic.mix 0 (d - 1)
        (fun a : ULift.{u} {x : Nat // 0 ≤ x ∧ x ≤ d - 1} => if (a.down.val : Int) < k then t else e)
      ↔ (0 < k ∧ t) ∨ (k < d ∧ e) :=
  exists_threshold hd t e

theorem index_angelic {γ : Type v} (l : List γ) (hne : l ≠ []) (F : γ → Prop) :
    Mix.angelic.mix 0 (l.length - 1)
        (fun a : ULift.{u} {x : Nat // 0 ≤ x ∧ x ≤ l.length - 1} =>
          F (l[a.down.val]'(Obs.idx_lt hne a.down.property)))
      ↔ ∃ g ∈ l, F g := by
  have := List.length_pos_iff.mpr hne
  constructor
  · rintro ⟨a, h⟩
    exact ⟨_, List.getElem_mem _, h⟩
  · rintro ⟨g, hg, h⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hg
    exact ⟨⟨⟨i, by omega⟩⟩, h⟩

private theorem selectD_exists (l : List (Nat × Prop)) (d : Prop) :
    (∃ n, n < (l.map Prod.fst).sum ∧ Obs.selectD l n d) ↔ ∃ p ∈ l, 0 < p.1 ∧ p.2 := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    obtain ⟨k, x⟩ := hd
    simp only [List.map_cons, List.sum_cons, Obs.selectD]
    constructor
    · rintro ⟨n, hn, h⟩
      split at h
      · exact ⟨(k, x), List.mem_cons_self, by show 0 < k; omega, h⟩
      · obtain ⟨p, hp, hw, hp2⟩ := ih.mp ⟨n - k, by omega, h⟩
        exact ⟨p, List.mem_cons_of_mem _ hp, hw, hp2⟩
    · rintro ⟨p, hp, hw, hp2⟩
      rcases List.mem_cons.mp hp with rfl | hp
      · exact ⟨0, by omega, by rwa [if_pos hw]⟩
      · obtain ⟨n, hn, h⟩ := ih.mpr ⟨p, hp, hw, hp2⟩
        exact ⟨k + n, by omega, by rwa [if_neg (by omega), Nat.add_sub_cancel_left]⟩

private theorem exists_select (l : List (Nat × Prop)) {T : Nat} (hT : T = (l.map Prod.fst).sum)
    (hpos : 0 < T) (d : Prop) :
    (∃ a : ULift.{u} {x : Nat // 0 ≤ x ∧ x ≤ T - 1}, Obs.selectD l a.down.val d)
      ↔ ∃ p ∈ l, 0 < p.1 ∧ p.2 := by
  rw [← selectD_exists l d, ← hT]
  exact ⟨fun ⟨a, h⟩ => ⟨_, by have := a.down.property; omega, h⟩,
    fun ⟨n, hn, h⟩ => ⟨⟨⟨n, by omega⟩⟩, h⟩⟩

theorem select_angelic (l : List (Nat × Prop)) {T : Nat} (hT : T = (l.map Prod.fst).sum)
    (hpos : 0 < T) (d : Prop) :
    Mix.angelic.mix 0 (T - 1)
        (fun a : ULift.{u} {x : Nat // 0 ≤ x ∧ x ≤ T - 1} => Obs.selectD l a.down.val d)
      ↔ ∃ p ∈ l, 0 < p.1 ∧ p.2 :=
  exists_select l hT hpos d

end Mix
