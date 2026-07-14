/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt.SPMF
import Basalt.RandomChoice

open RandomChoice

/-!
# Cost-Tracking SPMF

This file provides a modified interpretation of a `Gen` that ascribes cost to each choice a
generator makes. This allows us to prove things like "a list generator makes `O(|xs|)` choices when
generating a list `xs`."

## Main Definitions

- `SPMF.Cost` — A cost interpretation for a generator.
- `IsBounded` — A proposition that says a generator makes a bounded number of choices.
-/

namespace SPMF

/-- A cost-tracking SPMF: pairs each output with the number of random choices made. -/
abbrev Cost (α : Type u) : Type u := SPMF (α × Nat)

end SPMF

namespace SPMF.Cost

instance instInhabited : Inhabited (SPMF.Cost α) where
  default := @Bot.bot (SPMF (α × Nat)) _

noncomputable instance instMonad : Monad SPMF.Cost where
  pure a := (SPMF.pure (a, 0) : SPMF _)
  bind m f :=
    SPMF.bind m fun pair =>
      SPMF.bind (f pair.1) fun pair2 =>
        SPMF.pure (pair2.1, pair.2 + pair2.2)

section CCPO

open Lean.Order

instance instPartialOrder : Lean.Order.PartialOrder (SPMF.Cost α) where
  rel p q := @PartialOrder.rel (SPMF (α × Nat)) _ p q
  rel_refl := @PartialOrder.rel_refl (SPMF (α × Nat)) _
  rel_trans := @PartialOrder.rel_trans (SPMF (α × Nat)) _
  rel_antisymm := @PartialOrder.rel_antisymm (SPMF (α × Nat)) _

instance instCCPO : CCPO (SPMF.Cost α) where
  has_csup := by
    intros c hc
    exact @CCPO.has_csup (SPMF (α × Nat)) _ c hc

instance instMonoBind : MonoBind SPMF.Cost where
  bind_mono_left {α β} {m₁ m₂ : SPMF.Cost α} {f : α → SPMF.Cost β} (h : m₁ ⊑ m₂) := by
    intro pair
    simp only [Bind.bind, bind]
    unfold SPMF.bind
    apply ENNReal.tsum_le_tsum
    intro ⟨a, n₁⟩
    simp only [Lean.Order.PartialOrder.rel] at h
    gcongr
    exact h (a, n₁)
  bind_mono_right {α β} {m : SPMF.Cost α} {f₁ f₂ : α → SPMF.Cost β} (h : ∀ a, f₁ a ⊑ f₂ a) := by
    intro pair
    simp only [Bind.bind, bind]
    unfold SPMF.bind
    simp only [Lean.Order.PartialOrder.rel] at h ⊢
    apply ENNReal.tsum_le_tsum
    intro ⟨a, n₁⟩
    gcongr ?_ * ?_
    apply ENNReal.tsum_le_tsum
    intro i
    gcongr ?_ * ?_
    apply h

end CCPO

noncomputable instance instRandomChoice : RandomChoice SPMF.Cost where
  choose lo hi h := by
    exact SPMF.bind (choose lo hi h : SPMF (ULift {x : Nat // lo ≤ x ∧ x ≤ hi}))
      fun n => SPMF.pure (n, 1)

section support

@[simp]
theorem mem_support_pure_iff {a b : α} {n : Nat} :
    (b, n) ∈ (Pure.pure a : SPMF.Cost α).support ↔ b = a ∧ n = 0 := by
  have : (Pure.pure a : SPMF.Cost α) = (SPMF.pure (a, 0) : SPMF _) := rfl
  simp [this, SPMF.mem_support_pure_iff, Prod.mk.injEq]

@[simp]
theorem mem_support_bind_iff
    {m : SPMF.Cost α} {f : α → SPMF.Cost β} {b : β} {n : Nat} :
    (b, n) ∈ (m >>= f).support ↔
    ∃ a n1 n2, (a, n1) ∈ m.support ∧ (b, n2) ∈ (f a).support ∧ n = n1 + n2 := by
  have : (m >>= f : SPMF.Cost β) =
      SPMF.bind m fun pair =>
        SPMF.bind (f pair.1) fun pair2 =>
          (SPMF.pure (pair2.1, pair.2 + pair2.2) : SPMF _) := rfl
  rw [this]
  simp only [SPMF.mem_support_bind_iff, SPMF.mem_support_pure_iff, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨a, n1⟩, hmem1, ⟨b', n2⟩, hmem2, rfl, h_n⟩
    exact ⟨a, n1, n2, hmem1, hmem2, h_n⟩
  · rintro ⟨a, n1, n2, hmem1, hmem2, rfl⟩
    exact ⟨⟨a, n1⟩, hmem1, ⟨b, n2⟩, hmem2, rfl, rfl⟩

@[simp]
theorem mem_support_choose_iff
    {lo hi : Nat} {h : lo ≤ hi} {n : ULift {x : Nat // lo ≤ x ∧ x ≤ hi}} {c : Nat} :
    (n, c) ∈ (choose lo hi h : SPMF.Cost (ULift {x : Nat // lo ≤ x ∧ x ≤ hi})).support ↔ c = 1 := by
  have : (choose lo hi h : SPMF.Cost (ULift {x : Nat // lo ≤ x ∧ x ≤ hi})) =
      SPMF.bind (choose lo hi h : SPMF (ULift {x : Nat // lo ≤ x ∧ x ≤ hi}))
        fun k => (SPMF.pure (k, 1) : SPMF _) := rfl
  rw [this]
  simp only [SPMF.mem_support_bind_iff, SPMF.mem_support_choose_iff,
             SPMF.mem_support_pure_iff, Prod.mk.injEq, true_and]
  constructor
  · rintro ⟨k, rfl, rfl⟩
    rfl
  · rintro rfl
    exact ⟨n, rfl, rfl⟩

end support

end SPMF.Cost

open SPMF.Cost

/-- A cost-tracking generator `x` `IsBounded` by a cost function `f` if every output `a` it can
  produce is produced with at most `f a` random choices. -/
def IsBounded (x : SPMF.Cost α) (f : α → Nat) : Prop :=
  ∀ p ∈ SPMF.support x, p.2 ≤ f p.1

/-- `IsBounded`, unfolded to its definition. Useful with `rw` and `simp`. -/
theorem IsBounded_iff {x : SPMF.Cost α} {f : α → Nat} :
    IsBounded x f ↔
    ∀ p ∈ SPMF.support x, p.2 ≤ f p.1 := Iff.rfl

theorem IsBounded_pure : IsBounded (pure a) (fun _ => 0) := by
  rw [IsBounded_iff]
  rintro ⟨b, n⟩ hmem
  simp only [mem_support_pure_iff] at hmem
  omega

theorem IsBounded_choose : IsBounded (choose lo hi h) (fun _ => 1) := by
  rw [IsBounded_iff]
  rintro ⟨n, c⟩ hmem
  simp only [mem_support_choose_iff] at hmem
  omega

theorem IsBounded_bind
    {cx : α → Nat}
    {cf : α → β → Nat}
    {c : β → Nat}
    (hx : IsBounded x cx)
    (hf : ∀ a, IsBounded (f a) (cf a))
    (hg : ∀ p ∈ x.support, ∀ q ∈ (f p.1).support, cx p.1 + cf p.1 q.1 ≤ c q.1) :
    IsBounded (x >>= f) c := by
  simp_all only [IsBounded_iff]
  intro (b, nb) hb
  simp only [bind, SPMF.mem_support_bind_iff, SPMF.mem_support_pure_iff] at hb
  replace ⟨(a, na), ha, ⟨(b, nb), hb, h⟩⟩ := hb
  cases h
  simp_all
  grind

theorem IsBounded_mono
    (hc₁ : IsBounded x c₁)
    (h : ∀ a, c₁ a ≤ c₂ a) :
    IsBounded x c₂ := by
  simp_all only [IsBounded_iff]
  grind

theorem IsBounded_pick
    {fx fy : Unit → SPMF.Cost α}
    {cx cy : α → Nat}
    (hx : IsBounded (fx ()) cx)
    (hy : IsBounded (fy ()) cy) :
    IsBounded (pick fx fy) (fun a => 1 + max (cx a) (cy a)) := by
  unfold pick
  apply IsBounded_bind (cx := fun _ => 1)
      (cf := fun k a => if k.down.val == 0 then cx a else cy a)
      IsBounded_choose
  · intro k
    split_ifs
    · exact hx
    · exact hy
  · intro ⟨k, _⟩ _ ⟨a, _⟩ _
    simp only
    split_ifs <;> omega

open Lean.Order in
/-- `IsBounded` is an admissible relation.

  This is intended to be used in the construction of partial_fixpoint, and not meant to be used otherwise. -/
theorem admissible_IsBounded (f : α → Nat) :
    admissible (fun (x : SPMF.Cost α) => IsBounded x f) := by
  intro c hc ih
  simp only [IsBounded_iff] at *
  intro p hp
  rw [SPMF.mem_support_csup hc] at hp
  obtain ⟨x, hxc, hxp⟩ := hp
  exact ih x hxc p hxp
