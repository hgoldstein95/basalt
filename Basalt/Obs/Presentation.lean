/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Batteries.Data.List.Basic
import Basalt.Obs.Ordered

/-!
# Presentations of a Choice in `Prop`

How a choice presents for each shape a combinator makes it in (a plain range, a threshold, a list
index, a weighted selection), demonically (`Mix.demonic`, a `∀`) and angelically (`Mix.angelic`, an
`∃`), and the walker's lower-bound rules for each shape in the two algebras. A shape whose rule
splits the choice pointwise instead (`Mix.le_demonic_threshold`) has no demonic presentation. These
are facts about quantifiers over a range, not about combinators.
-/

namespace Mix

variable {lo hi : Nat}

/-! ## Demonic -/

theorem range_demonic (F : ULift.{u} {x : Nat // lo ≤ x ∧ x ≤ hi} → Prop) :
    Mix.demonic.mix lo hi F ↔ ∀ x (hx : lo ≤ x ∧ x ≤ hi), F ⟨⟨x, hx⟩⟩ :=
  ⟨fun h x hx => h ⟨⟨x, hx⟩⟩, fun h a => h a.down.val a.down.property⟩

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
      rwa [ite_eq_right (by omega), Nat.add_sub_cancel_left] at this
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

/-! ## Angelic -/

theorem range_angelic (F : ULift.{u} {x : Nat // lo ≤ x ∧ x ≤ hi} → Prop) :
    Mix.angelic.mix lo hi F ↔ ∃ x, ∃ hx : lo ≤ x ∧ x ≤ hi, F ⟨⟨x, hx⟩⟩ :=
  ⟨fun ⟨a, h⟩ => ⟨a.down.val, a.down.property, h⟩, fun ⟨x, hx, h⟩ => ⟨⟨⟨x, hx⟩⟩, h⟩⟩

theorem threshold_angelic {d : Nat} {k : Int} (hd : 0 < d) (t e : Prop) :
    Mix.angelic.mix 0 (d - 1)
        (fun a : ULift.{u} {x : Nat // 0 ≤ x ∧ x ≤ d - 1} => if (a.down.val : Int) < k then t else e)
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
      rwa [ite_eq_left (by omega)]
    · refine ⟨⟨⟨d - 1, by omega⟩⟩, ?_⟩
      show if ((d - 1 : Nat) : Int) < k then t else e
      rwa [ite_eq_right (by omega)]

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
      · exact ⟨0, by omega, by rwa [ite_eq_left hw]⟩
      · obtain ⟨n, hn, h⟩ := ih.mpr ⟨p, hp, hw, hp2⟩
        exact ⟨k + n, by omega, by rwa [ite_eq_right (by omega), Nat.add_sub_cancel_left]⟩

theorem select_angelic (l : List (Nat × Prop)) {T : Nat} (hT : T = (l.map Prod.fst).sum)
    (hpos : 0 < T) (d : Prop) :
    Mix.angelic.mix 0 (T - 1)
        (fun a : ULift.{u} {x : Nat // 0 ≤ x ∧ x ≤ T - 1} => Obs.selectD l a.down.val d)
      ↔ ∃ p ∈ l, 0 < p.1 ∧ p.2 := by
  rw [← selectD_exists l d, ← hT]
  exact ⟨fun ⟨a, h⟩ => ⟨_, by have := a.down.property; omega, h⟩,
    fun ⟨n, hn, h⟩ => ⟨⟨⟨n, by omega⟩⟩, h⟩⟩

/-! ## A choice holds when every outcome does -/

@[gen_rule]
theorem le_demonic_range {lo hi : Nat} {h : lo ≤ hi}
    {F : ULift.{u} {x : Nat // lo ≤ x ∧ x ≤ hi} → Prop}
    {d : (x : Nat) → lo ≤ x ∧ x ≤ hi → Prop} (hF : ∀ x hx, d x hx ≤ F ⟨⟨x, hx⟩⟩) :
    (∀ x hx, d x hx) ≤ Mix.demonic.range lo hi h F := fun hd _ => hF _ _ (hd _ _)

@[gen_rule]
theorem le_demonic_threshold {n : Nat} {k : Int} {t e c d : Prop} (ht : c ≤ t) (he : d ≤ e) :
    (c ∧ d) ≤ (Mix.demonic.{u}).threshold n k t e := by
  rintro ⟨hc, hd⟩ a
  show if _ then t else e
  split
  · exact ht hc
  · exact he hd

@[gen_rule]
theorem le_demonic_index {γ : Type v} {l : List γ} {hne : l ≠ []} {F : γ → Prop}
    {cs : List Prop} (h : List.Forall₂ (fun c g => c ≤ F g) cs l) :
    cs.foldr And True ≤ (Mix.demonic.{u}).index l hne F := by
  intro hcs
  have key : ∀ g ∈ l, F g := by
    clear hne
    induction h with
    | nil => simp
    | cons hc _ ih => exact List.forall_mem_cons.mpr ⟨hc hcs.1, ih hcs.2⟩
  exact (index_demonic l hne F).mpr key

@[gen_rule]
theorem le_demonic_element {γ : Type v} {l : List γ} {hne : l ≠ []} {F : γ → Prop} :
    (∀ a ∈ l, F a) ≤ (Mix.demonic.{u}).element l hne F := (index_demonic l hne F).mpr

@[gen_rule]
theorem le_demonic_select {γ : Type v} {l : List (Nat × γ)} {hpos : 0 < (l.map Prod.fst).sum}
    {F : γ → Prop} {d : Prop} {cs : List (Nat × Prop)} (h : Weighted (· ≥ ·) F cs l) :
    (cs.map Prod.snd).foldr And True ≤ (Mix.demonic.{u}).select l hpos F d := by
  intro hcs
  have key : ∀ q ∈ l, F q.2 := by
    clear hpos
    induction h with
    | nil => simp
    | cons hc _ ih => exact List.forall_mem_cons.mpr ⟨hc hcs.1, ih hcs.2⟩
  refine (select_demonic (l.map fun p => (p.1, F p.2)) (by simp [Function.comp_def]) hpos d).mpr ?_
  intro p hp _
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  exact key q hq

@[gen_rule]
theorem le_demonic_rangeInt {lo hi : Int} {h : lo ≤ hi} {F : Int → Prop}
    {d : (x : Int) → lo ≤ x ∧ x ≤ hi → Prop} (hF : ∀ x hx, d x hx ≤ F x) :
    (∀ x hx, d x hx) ≤ (Mix.demonic.{0}).rangeInt lo hi h F := by
  intro hd a
  have := a.down.property
  exact hF _ ⟨by omega, by omega⟩ (hd _ _)

/-! ## A choice holds when some outcome does

A weighted or threshold branch carries its reachability. -/

@[gen_rule]
theorem le_angelic_range {lo hi : Nat} {h : lo ≤ hi}
    {F : ULift.{u} {x : Nat // lo ≤ x ∧ x ≤ hi} → Prop}
    {d : (x : Nat) → lo ≤ x ∧ x ≤ hi → Prop} (hF : ∀ x hx, d x hx ≤ F ⟨⟨x, hx⟩⟩) :
    (∃ x hx, d x hx) ≤ Mix.angelic.range lo hi h F := fun ⟨x, hx, hd⟩ => ⟨_, hF x hx hd⟩

@[gen_rule]
theorem le_angelic_threshold {n : Nat} {k : Int} {t e c d : Prop} (hn : 0 < n)
    (ht : c ≤ t) (he : d ≤ e) :
    ((0 < k ∧ c) ∨ (k < n ∧ d)) ≤ (Mix.angelic.{u}).threshold n k t e := by
  intro h
  refine (threshold_angelic hn t e).mpr ?_
  exact h.imp (And.imp_right ht) (And.imp_right he)

@[gen_rule]
theorem le_angelic_index {γ : Type v} {l : List γ} {hne : l ≠ []} {F : γ → Prop}
    {cs : List Prop} (h : List.Forall₂ (fun c g => c ≤ F g) cs l) :
    cs.foldr Or False ≤ (Mix.angelic.{u}).index l hne F := by
  intro hcs
  refine (index_angelic l hne F).mpr ?_
  clear hne
  induction h with
  | nil => exact hcs.elim
  | cons hc _ ih =>
    rcases hcs with hcs | hcs
    · exact ⟨_, List.mem_cons_self, hc hcs⟩
    · obtain ⟨g, hg, hF⟩ := ih hcs
      exact ⟨g, List.mem_cons_of_mem _ hg, hF⟩

@[gen_rule]
theorem le_angelic_element {γ : Type v} {l : List γ} {hne : l ≠ []} {F : γ → Prop} :
    (∃ a ∈ l, F a) ≤ (Mix.angelic.{u}).element l hne F := (index_angelic l hne F).mpr

@[gen_rule]
theorem le_angelic_select {γ : Type v} {l : List (Nat × γ)} {hpos : 0 < (l.map Prod.fst).sum}
    {F : γ → Prop} {d : Prop} {cs : List (Nat × Prop)} (h : Weighted (· ≥ ·) F cs l) :
    (cs.map fun p => 0 < p.1 ∧ p.2).foldr Or False ≤ (Mix.angelic.{u}).select l hpos F d := by
  intro hcs
  refine (select_angelic (l.map fun p => (p.1, F p.2)) (by simp [Function.comp_def]) hpos d).mpr ?_
  clear hpos
  induction h with
  | nil => exact hcs.elim
  | cons hc _ ih =>
    rcases hcs with ⟨hw, hcs⟩ | hcs
    · exact ⟨_, List.mem_cons_self, hw, hc hcs⟩
    · obtain ⟨p, hp, hF⟩ := ih hcs
      exact ⟨p, List.mem_cons_of_mem _ hp, hF⟩

@[gen_rule]
theorem le_angelic_rangeInt {lo hi : Int} {h : lo ≤ hi} {F : Int → Prop}
    {d : (x : Int) → lo ≤ x ∧ x ≤ hi → Prop} (hF : ∀ x hx, d x hx ≤ F x) :
    (∃ x hx, d x hx) ≤ (Mix.angelic.{0}).rangeInt lo hi h F := by
  rintro ⟨x, hx, hd⟩
  refine ⟨⟨⟨(x - lo).toNat, by omega⟩⟩, ?_⟩
  have : lo + ((x - lo).toNat : Int) = x := by omega
  show F (lo + _)
  rw [this]
  exact hF x hx hd

end Mix
