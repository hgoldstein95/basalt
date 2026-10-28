/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Segev Elazar-Mittelman
-/
module

public import Basalt.Enum.Tabled
public import Basalt.Enum.FailLaws

/-!
# A Complete Tabled Run Is the Support

A recursion with no measure means its least fixpoint at `OptionT SPMF` (`PolyStep.lfp`), given the
monotonicity `partial_fixpoint` would ask for. `supports` agrees with it: once a round changes
nothing, every table entry is exactly the values the recursion succeeds with at that key
(`PolyStep.supports_eq`).

* **Soundness**, by induction on rounds: a table whose values are all producible stays so, because a
  key's new values come from one step run against it (`SetM.Sound`), and a step of the least
  fixpoint is the least fixpoint.
* **Completeness**, by fixpoint induction: a round that changed nothing ran every key's step against
  the final table, missed no key, and found nothing new, so the table is closed under a step
  (`SetM.Comp`), and so holds everything the least fixpoint produces.

Both relations are preserved by every construct, so a step's obligations are proved from them.
-/

@[expose] public section

open Lean.Order RandomChoice

namespace Basalt

variable {κ α β γ : Type} [BEq κ] [Hashable κ]

/-- Every value the table holds for a key is one `f` succeeds with there. -/
def TSound (f : κ → OptionT SPMF α) (t : Std.HashMap κ (List α)) : Prop :=
  ∀ k l, t[k]? = some l → ∀ a ∈ l, some a ∈ ((f k).run).support

/-- Every value `f` succeeds with at a key of the table, the table holds. -/
def TComp (f : κ → OptionT SPMF α) (t : Std.HashMap κ (List α)) : Prop :=
  ∀ k l, t[k]? = some l → ∀ a, some a ∈ ((f k).run).support → a ∈ l

/-! ## `OptionT SPMF`'s successes -/

namespace OptionTSPMF

theorem mem_pure {b c : β} : some c ∈ ((Pure.pure b : OptionT SPMF β).run).support ↔ c = b := by
  have : (Pure.pure b : OptionT SPMF β).run = (Pure.pure (some b) : SPMF _) := rfl
  rw [this, SPMF.mem_support_pure_iff, Option.some_inj]

theorem mem_bind {x : OptionT SPMF β} {k : β → OptionT SPMF γ} {b : γ} :
    some b ∈ ((x >>= k).run).support ↔ ∃ a, some a ∈ (x.run).support ∧ some b ∈ ((k a).run).support := by
  have : (x >>= k : OptionT SPMF γ).run = (x.run >>= fun o => match o with
      | some a => (k a).run
      | none => Pure.pure none : SPMF (Option γ)) := rfl
  rw [this, SPMF.mem_support_bind_iff]
  constructor
  · rintro ⟨o, ho, hb⟩
    cases o with
    | none => simp at hb
    | some a => exact ⟨a, ho, hb⟩
  · rintro ⟨a, ha, hb⟩
    exact ⟨some a, ha, hb⟩

theorem not_mem_fail {b : β} : some b ∉ ((Fail.fail : OptionT SPMF β).run).support := by
  have : (Fail.fail : OptionT SPMF β).run = (Pure.pure none : SPMF (Option β)) := rfl
  rw [this, SPMF.mem_support_pure_iff]
  exact fun h => by cases h

theorem mem_choose {lo hi : Nat} {h : lo ≤ hi} (m : ULift {x : Nat // lo ≤ x ∧ x ≤ hi}) :
    some m ∈ ((RandomChoice.choose lo hi h : OptionT SPMF _).run).support := by
  have : (RandomChoice.choose lo hi h : OptionT SPMF _).run =
      ((RandomChoice.choose lo hi h : SPMF _) >>= fun a => Pure.pure (some a)) := rfl
  rw [this, SPMF.mem_support_bind_iff]
  exact ⟨m, by simp, by simp⟩

end OptionTSPMF

/-! ## `SetM`'s values and misses -/

namespace SetM

theorem mem_bind {x : SetM κ α β} {g : β → SetM κ α γ} {t : Std.HashMap κ (List α)} {b : γ} :
    b ∈ ((x >>= g) t).1 ↔ ∃ a ∈ (x t).1, b ∈ (g a t).1 := by
  show b ∈ ((x t).1.map fun a => g a t).flatMap (·.1) ↔ _
  simp

theorem bind_misses {x : SetM κ α β} {g : β → SetM κ α γ} {t : Std.HashMap κ (List α)} :
    ((x >>= g) t).2 = [] ↔ (x t).2 = [] ∧ ∀ a ∈ (x t).1, (g a t).2 = [] := by
  show (x t).2 ++ ((x t).1.map fun a => g a t).flatMap (·.2) = [] ↔ _
  simp

theorem mem_choose {lo hi : Nat} {h : lo ≤ hi} {t : Std.HashMap κ (List α)}
    (m : ULift {x : Nat // lo ≤ x ∧ x ≤ hi}) : m ∈ ((RandomChoice.choose lo hi h : SetM κ α _) t).1 := by
  obtain ⟨⟨v, hv⟩⟩ := m
  show _ ∈ (List.range (hi - lo + 1)).attach.map _
  simp only [List.mem_map, List.mem_attach, true_and, Subtype.exists, List.mem_range]
  exact ⟨v - lo, by omega, by simp only [ULift.up.injEq, Subtype.mk.injEq]; omega⟩

/-! ### Soundness -/

/-- Against a table of producible values, every value `m` gives is one `x` succeeds with. -/
def Sound (f : κ → OptionT SPMF α) (m : SetM κ α β) (x : OptionT SPMF β) : Prop :=
  ∀ t, TSound f t → ∀ b ∈ (m t).1, some b ∈ (x.run).support

variable {f : κ → OptionT SPMF α}

theorem sound_pure (b : β) : Sound f (Pure.pure b) (Pure.pure b) := fun _ _ c hc => by
  change c ∈ [b] at hc
  exact OptionTSPMF.mem_pure.mpr (List.mem_singleton.mp hc)

theorem sound_bind {x : SetM κ α β} {y : OptionT SPMF β} {g : β → SetM κ α γ} {k : β → OptionT SPMF γ}
    (hk : ∀ a, Sound f (g a) (k a)) (hx : Sound f x y) : Sound f (x >>= g) (y >>= k) :=
  fun t ht b hb => by
    obtain ⟨a, ha, hb⟩ := mem_bind.mp hb
    exact OptionTSPMF.mem_bind.mpr ⟨a, hx t ht a ha, hk a t ht b hb⟩

theorem sound_map {x : SetM κ α β} {y : OptionT SPMF β} (h : β → γ) (hx : Sound f x y) :
    Sound f (h <$> x) (h <$> y) :=
  sound_bind (fun a => sound_pure (h a)) hx

theorem sound_seq {x : SetM κ α (β → γ)} {y : OptionT SPMF (β → γ)} {x' : SetM κ α β}
    {y' : OptionT SPMF β} (hx : Sound f x y) (hx' : Sound f x' y') : Sound f (x <*> x') (y <*> y') :=
  sound_bind (fun h => sound_map h hx') hx

theorem sound_choose (lo hi : Nat) (h : lo ≤ hi) :
    Sound f (RandomChoice.choose lo hi h) (RandomChoice.choose lo hi h) :=
  fun _ _ m _ => OptionTSPMF.mem_choose m

theorem sound_fail : Sound f (Fail.fail : SetM κ α β) Fail.fail := fun _ _ b hb => by
  change b ∈ [] at hb
  cases hb

theorem sound_ite {p : Prop} [Decidable p] {m₁ m₂ : SetM κ α β} {x₁ x₂ : OptionT SPMF β}
    (h₁ : p → Sound f m₁ x₁) (h₂ : ¬p → Sound f m₂ x₂) :
    Sound f (if p then m₁ else m₂) (if p then x₁ else x₂) := by
  split
  · exact h₁ ‹_›
  · exact h₂ ‹_›

theorem sound_lookup [BEq α] (k : κ) : Sound f (PolyStep.lookupSet k) (f k) := fun t ht a ha => by
  unfold PolyStep.lookupSet at ha
  split at ha
  · exact ht k _ ‹_› a ha
  · cases ha

/-! ### Completeness -/

/-- Against a table holding everything `f` produces at its keys, if `m` misses no key, every value
`x` succeeds with is one `m` gives. -/
def Comp (f : κ → OptionT SPMF α) (m : SetM κ α β) (x : OptionT SPMF β) : Prop :=
  ∀ t, (m t).2 = [] → TComp f t → ∀ b, some b ∈ (x.run).support → b ∈ (m t).1

theorem comp_pure (b : β) : Comp f (Pure.pure b) (Pure.pure b) := fun _ _ _ c hc => by
  change c ∈ [b]
  exact List.mem_singleton.mpr (OptionTSPMF.mem_pure.mp hc)

theorem comp_bind {x : SetM κ α β} {y : OptionT SPMF β} {g : β → SetM κ α γ} {k : β → OptionT SPMF γ}
    (hk : ∀ a, Comp f (g a) (k a)) (hx : Comp f x y) : Comp f (x >>= g) (y >>= k) :=
  fun t hms ht b hb => by
    obtain ⟨hx₀, hk₀⟩ := bind_misses.mp hms
    obtain ⟨a, ha, hb⟩ := OptionTSPMF.mem_bind.mp hb
    have ha' := hx t hx₀ ht a ha
    exact mem_bind.mpr ⟨a, ha', hk a t (hk₀ a ha') ht b hb⟩

theorem comp_map {x : SetM κ α β} {y : OptionT SPMF β} (h : β → γ) (hx : Comp f x y) :
    Comp f (h <$> x) (h <$> y) :=
  comp_bind (fun a => comp_pure (h a)) hx

theorem comp_seq {x : SetM κ α (β → γ)} {y : OptionT SPMF (β → γ)} {x' : SetM κ α β}
    {y' : OptionT SPMF β} (hx : Comp f x y) (hx' : Comp f x' y') : Comp f (x <*> x') (y <*> y') :=
  comp_bind (fun h => comp_map h hx') hx

theorem comp_choose (lo hi : Nat) (h : lo ≤ hi) :
    Comp f (RandomChoice.choose lo hi h) (RandomChoice.choose lo hi h) :=
  fun _ _ _ m _ => mem_choose m

theorem comp_fail : Comp f (Fail.fail : SetM κ α β) Fail.fail := fun _ _ _ _ hb =>
  absurd hb OptionTSPMF.not_mem_fail

theorem comp_ite {p : Prop} [Decidable p] {m₁ m₂ : SetM κ α β} {x₁ x₂ : OptionT SPMF β}
    (h₁ : p → Comp f m₁ x₁) (h₂ : ¬p → Comp f m₂ x₂) :
    Comp f (if p then m₁ else m₂) (if p then x₁ else x₂) := by
  split
  · exact h₁ ‹_›
  · exact h₂ ‹_›

theorem comp_lookup [BEq α] (k : κ) : Comp f (PolyStep.lookupSet k) (f k) := fun t hms ht a ha => by
  unfold PolyStep.lookupSet at hms ⊢
  split at hms
  · rename_i l hl
    exact ht k l hl a ha
  · cases hms

end SetM

/-! ## Rounds -/

namespace PolyStep

variable [LawfulBEq κ] [LawfulHashable κ] [BEq α] [LawfulBEq α]

/-- The meaning of a recursion with no measure: its least fixpoint at `OptionT SPMF`. -/
noncomputable def lfp (step : PolyStep κ α) (hmono : monotone (step (OptionT SPMF))) :
    κ → OptionT SPMF α :=
  Lean.Order.fix (step (OptionT SPMF)) hmono

omit [BEq κ] [Hashable κ] [LawfulBEq κ] [LawfulHashable κ] [BEq α] [LawfulBEq α] in
theorem lfp_eq (step : PolyStep κ α) (hmono : monotone (step (OptionT SPMF))) (k : κ) :
    step.lfp hmono k = step (OptionT SPMF) (step.lfp hmono) k :=
  congrFun (Lean.Order.fix_eq hmono) k

omit [LawfulBEq κ] [LawfulHashable κ] in
/-- An update that changed nothing left the table as it was, missed what its step missed, and found
nothing its key did not already hold. -/
theorem update_false {step : PolyStep κ α} {k : κ} {t t' : Std.HashMap κ (List α)} {ms : List κ}
    (h : update step k t = (t', false, ms)) :
    t' = t ∧ ms = (step (SetM κ α) lookupSet k t).2 ∧
      ∀ v ∈ (step (SetM κ α) lookupSet k t).1, v ∈ t.getD k [] := by
  unfold update at h
  generalize step (SetM κ α) lookupSet k t = r at h ⊢
  obtain ⟨vs, ms'⟩ := r
  dsimp only at h
  split at h
  · rename_i hall
    cases h
    refine ⟨rfl, rfl, fun v hv => ?_⟩
    have := List.all_eq_true.mp hall v hv
    simpa using this
  · cases h

omit [LawfulBEq κ] [LawfulHashable κ] in
/-- The updates of a round in which nothing changed: the table never changed, no key was missed,
and no key's step found anything new. -/
theorem foldl_update_false (step : PolyStep κ α) :
    ∀ (L : List κ) (t tR : Std.HashMap κ (List α)) (c₀ : Bool) (ms₀ : List κ),
      L.foldl (fun (t, changed, ms) k => let (t, c, m) := update step k t; (t, changed || c, ms ++ m))
          (t, c₀, ms₀) = (tR, false, []) →
        c₀ = false ∧ ms₀ = [] ∧ tR = t ∧
          ∀ k ∈ L, (step (SetM κ α) lookupSet k t).2 = [] ∧
            ∀ v ∈ (step (SetM κ α) lookupSet k t).1, v ∈ t.getD k [] := by
  intro L
  induction L with
  | nil =>
    intro t tR c₀ ms₀ h
    simp only [List.foldl_nil, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨rfl, rfl, rfl, fun _ hk => by cases hk⟩
  | cons k L ih =>
    intro t tR c₀ ms₀ h
    simp only [List.foldl_cons] at h
    generalize hu : update step k t = u at h
    obtain ⟨t₁, c₁, m₁⟩ := u
    obtain ⟨hc, hm, rfl, hL⟩ := ih t₁ tR _ _ h
    have hc₀ : c₀ = false := by cases c₀ <;> simp_all
    have hc₁ : c₁ = false := by cases c₁ <;> simp_all
    have hms₀ : ms₀ = [] := (List.append_eq_nil_iff.mp hm).1
    have hm₁ : m₁ = [] := (List.append_eq_nil_iff.mp hm).2
    subst hc₁
    obtain ⟨rfl, hms, hvs⟩ := update_false hu
    refine ⟨hc₀, hms₀, rfl, fun k' hk' => ?_⟩
    rcases List.mem_cons.mp hk' with rfl | hk'
    · exact ⟨hms ▸ hm₁, hvs⟩
    · exact hL k' hk'

omit [LawfulBEq κ] [LawfulHashable κ] in
/-- A round in which nothing changed left the table as it was, and ran every key's step against it,
missing nothing and finding nothing new. -/
theorem round_false {step : PolyStep κ α} {t t' : Std.HashMap κ (List α)}
    (h : round step t = (t', false)) :
    t' = t ∧ ∀ k ∈ t.keys, (step (SetM κ α) lookupSet k t).2 = [] ∧
      ∀ v ∈ (step (SetM κ α) lookupSet k t).1, v ∈ t.getD k [] := by
  unfold round at h
  generalize hf : t.keys.foldl _ (t, false, []) = r at h
  obtain ⟨t₁, ch, ms⟩ := r
  simp only [Prod.mk.injEq, Bool.or_eq_false_iff, Bool.not_eq_false', List.isEmpty_iff] at h
  obtain ⟨h₁, hch, rfl⟩ := h
  subst hch
  obtain ⟨-, -, rfl, hkeys⟩ := foldl_update_false step _ _ _ _ _ hf
  exact ⟨by simpa using h₁.symm, hkeys⟩

omit [LawfulBEq κ] [LawfulHashable κ] in
/-- A complete run ended with a round that changed nothing. -/
theorem rounds_true {step : PolyStep κ α} :
    ∀ (fuel n : Nat) (t T : Std.HashMap κ (List α)) (r : Nat),
      rounds step fuel n t = (T, true, r) → round step T = (T, false) := by
  intro fuel
  induction fuel with
  | zero => intro n t T r h; simp [rounds] at h
  | succ fuel ih =>
    intro n t T r h
    unfold rounds at h
    generalize hq : round step t = q at h
    obtain ⟨t', ch⟩ := q
    cases ch with
    | true => exact ih _ _ _ _ h
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, Prod.mk.injEq] at h
      obtain ⟨rfl, -, -⟩ := h
      have := (round_false hq).1
      subst this
      exact hq

/-! ### Soundness through rounds -/

omit [BEq α] [LawfulBEq α] in
theorem tsound_insert {f : κ → OptionT SPMF α} {t : Std.HashMap κ (List α)} {k : κ} {l : List α}
    (ht : TSound f t) (hl : ∀ a ∈ l, some a ∈ ((f k).run).support) : TSound f (t.insert k l) := by
  intro k' l' h a ha
  rw [Std.HashMap.getElem?_insert] at h
  split at h
  · rename_i heq
    cases h
    exact (beq_iff_eq.mp heq) ▸ hl a ha
  · exact ht k' l' h a ha

omit [BEq α] [LawfulBEq α] in
theorem tsound_getD {f : κ → OptionT SPMF α} {t : Std.HashMap κ (List α)} (ht : TSound f t) (k : κ) :
    ∀ a ∈ t.getD k [], some a ∈ ((f k).run).support := by
  intro a ha
  rw [Std.HashMap.getD_eq_getD_getElem?] at ha
  cases h : t[k]? with
  | none => simp [h] at ha
  | some l => simp only [h, Option.getD_some] at ha; exact ht k l h a ha

theorem tsound_update {step : PolyStep κ α} {f : κ → OptionT SPMF α} {k : κ}
    {t : Std.HashMap κ (List α)} (ht : TSound f t)
    (hstep : ∀ v ∈ (step (SetM κ α) lookupSet k t).1, some v ∈ ((f k).run).support) :
    TSound f (update step k t).1 := by
  unfold update
  generalize hr : step (SetM κ α) lookupSet k t = r at hstep
  obtain ⟨vs, ms⟩ := r
  dsimp only
  split
  · exact ht
  · refine tsound_insert ht fun a ha => ?_
    rcases List.mem_append.mp (List.mem_eraseDups.mp ha) with ha | ha
    · exact tsound_getD ht k a ha
    · exact hstep a ha

/-- A round keeps a table sound, every key's step being sound against it. -/
theorem tsound_round {step : PolyStep κ α} {f : κ → OptionT SPMF α}
    (hstep : ∀ t, TSound f t → ∀ k, ∀ v ∈ (step (SetM κ α) lookupSet k t).1, some v ∈ ((f k).run).support)
    {t : Std.HashMap κ (List α)} (ht : TSound f t) : TSound f (round step t).1 := by
  unfold round
  have hkeys : ∀ (L : List κ) (t : Std.HashMap κ (List α)) (c : Bool) (ms : List κ), TSound f t →
      TSound f (L.foldl (fun (t, changed, ms) k => let (t, c, m) := update step k t;
        (t, changed || c, ms ++ m)) (t, c, ms)).1 := by
    intro L
    induction L with
    | nil => intro t _ _ ht; exact ht
    | cons k L ih =>
      intro t c ms ht
      simp only [List.foldl_cons]
      generalize hu : update step k t = u
      obtain ⟨t₁, c₁, m₁⟩ := u
      have : TSound f t₁ := by
        have := tsound_update (step := step) ht (hstep t ht k)
        rw [hu] at this
        exact this
      exact ih _ _ _ this
  have hmiss : ∀ (ms : List κ) (t : Std.HashMap κ (List α)), TSound f t →
      TSound f (ms.foldl (fun t k => if t.contains k then t else t.insert k []) t) := by
    intro ms
    induction ms with
    | nil => intro t ht; exact ht
    | cons k ms ih =>
      intro t ht
      simp only [List.foldl_cons]
      apply ih
      split
      · exact ht
      · exact tsound_insert ht fun _ ha => by cases ha
  generalize hf : t.keys.foldl _ (t, false, []) = r
  obtain ⟨t₁, ch, ms⟩ := r
  have := hkeys t.keys t false [] ht
  rw [hf] at this
  exact hmiss ms t₁ this

theorem tsound_rounds {step : PolyStep κ α} {f : κ → OptionT SPMF α}
    (hstep : ∀ t, TSound f t → ∀ k, ∀ v ∈ (step (SetM κ α) lookupSet k t).1, some v ∈ ((f k).run).support) :
    ∀ (fuel n : Nat) (t : Std.HashMap κ (List α)), TSound f t → TSound f (rounds step fuel n t).1 := by
  intro fuel
  induction fuel with
  | zero => intro n t ht; exact ht
  | succ fuel ih =>
    intro n t ht
    unfold rounds
    generalize hq : round step t = q
    obtain ⟨t', ch⟩ := q
    have ht' : TSound f t' := by
      have := tsound_round hstep ht
      rw [hq] at this
      exact this
    cases ch with
    | true => exact ih _ _ ht'
    | false => exact ht'

/-! ## The theorem -/

/-- A complete run's table holds, at each of its keys, exactly the values the recursion succeeds with
there. `hsound` and `hcomp` are the step's obligations, proved from the `SetM.sound_*` and
`SetM.comp_*` lemmas. -/
theorem supports_eq (step : PolyStep κ α) (hmono : monotone (step (OptionT SPMF)))
    (hsound : ∀ (f : κ → OptionT SPMF α) k, SetM.Sound f (step (SetM κ α) lookupSet k)
      (step (OptionT SPMF) f k))
    (hcomp : ∀ (f : κ → OptionT SPMF α) k, SetM.Comp f (step (SetM κ α) lookupSet k)
      (step (OptionT SPMF) f k))
    (fuel : Nat) (ks : List κ) (h : (supports step fuel ks).complete = true)
    (k : κ) (l : List α) (hk : (supports step fuel ks).table[k]? = some l) (a : α) :
    a ∈ l ↔ some a ∈ ((step.lfp hmono k).run).support := by
  -- The run's final table, and the round that left it unchanged.
  unfold supports at h hk
  generalize ht0 : ks.foldl (fun t k => t.insert k []) ({} : Std.HashMap κ (List α)) = t0 at h hk
  rcases hrun : rounds step fuel 0 t0 with ⟨T, complete, r⟩
  simp only [hrun] at h hk
  subst h
  have hstable := round_false (rounds_true _ _ _ _ _ hrun)
  -- Soundness: the table only ever holds producible values.
  have hT : TSound (step.lfp hmono) T := by
    have h0 : TSound (step.lfp hmono) t0 := by
      subst ht0
      have : ∀ (ks : List κ) (t : Std.HashMap κ (List α)), TSound (step.lfp hmono) t →
          TSound (step.lfp hmono) (ks.foldl (fun t k => t.insert k []) t) := by
        intro ks
        induction ks with
        | nil => intro t ht; exact ht
        | cons k ks ih => intro t ht; exact ih _ (tsound_insert ht fun _ ha => by cases ha)
      exact this ks {} fun k l h => by simp at h
    have := tsound_rounds (step := step) (f := step.lfp hmono)
      (fun t ht k v hv => by
        rw [lfp_eq]
        exact hsound (step.lfp hmono) k t ht v hv) fuel 0 t0 h0
    rw [hrun] at this
    exact this
  constructor
  · exact hT k l hk a
  · -- Completeness: the least fixpoint produces nothing the stable table lacks.
    have hcomp_lfp : TComp (step.lfp hmono) T := by
      unfold lfp
      refine Lean.Order.fix_induct hmono (fun f => TComp f T) ?_ (fun f hf => ?_)
      · show Lean.Order.admissible fun f : κ → OptionT SPMF α =>
          ∀ k, (fun k (y : OptionT SPMF α) => ∀ l, T[k]? = some l → ∀ a,
            some a ∈ (y.run).support → a ∈ l) k (f k)
        refine admissible_pi_apply (β := fun _ => OptionT SPMF α)
          (fun k (y : OptionT SPMF α) => ∀ l, T[k]? = some l → ∀ a,
            some a ∈ (y.run).support → a ∈ l) fun k => ?_
        have heq : (fun y : OptionT SPMF α => ∀ l, T[k]? = some l → ∀ a,
            some a ∈ (y.run).support → a ∈ l) = fun y : SPMF (Option α) =>
              SPMF.alwaysObs.spec y fun o => ∀ l, T[k]? = some l → ∀ a, o = some a → a ∈ l := by
          funext y
          apply propext
          rw [← IsSoundFor.iff_obs]
          exact ⟨fun h o ho l hl a hoa => h l hl a (hoa ▸ ho), fun h l hl a ha => h _ ha l hl a rfl⟩
        rw [heq]
        exact SPMF.alwaysObs.admissible _
      · intro k' l' hk' a ha
        have hkeys : k' ∈ T.keys := by
          rw [Std.HashMap.mem_keys]
          exact Std.HashMap.mem_iff_isSome_getElem?.mpr (by simp [hk'])
        obtain ⟨hms, hvs⟩ := hstable.2 k' hkeys
        have hb := hcomp f k' T hms hf a ha
        have := hvs a hb
        rwa [Std.HashMap.getD_eq_getD_getElem?, hk', Option.getD_some] at this
    exact hcomp_lfp k l hk a

end PolyStep

end Basalt
