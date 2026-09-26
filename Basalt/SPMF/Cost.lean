/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Mathlib.Data.ENat.Lattice
import Basalt.RandomChoice
import Basalt.SPMF.Support

/-!
# Cost-Tracking SPMF

`SPMF.Cost` interprets a generator as a distribution over (value, number of random choices) pairs.
Its observations land in `WPC`, whose `bind` and `choose` do the cost accounting, so a combinator's
lemma is its `Obs.map_*` read through one of them.
-/

open RandomChoice

namespace SPMF

/-- A cost-tracking SPMF: pairs each output with the number of random choices made. -/
abbrev Cost (α : Type u) : Type u := SPMF (α × Nat)

end SPMF

/-- A choice is as large as its largest outcome: the algebra the worst-case observation lands in.
`ℕ∞` and not `ℕ`, because the supremum over an unbounded generator's support has to exist for
`Obs.map_bind` to hold. -/
noncomputable def Mix.sup : Mix.{u} ℕ∞ where mix _ _ F := ⨆ a, F a

/-- Moves a cast out of a worst-case bound computed in `ℕ∞`, which the walker reads a cost bound off
with `norm_cast`; Mathlib's `Nat.cast_max` needs a linear ordered ring. -/
@[norm_cast]
theorem ENat.coe_max' (a b : ℕ) : ((max a b : ℕ) : ℕ∞) = max (a : ℕ∞) (b : ℕ∞) :=
  Nat.mono_cast.map_max

namespace SPMF.Cost

instance instInhabited : Inhabited (SPMF.Cost α) where
  -- default = ⊥, the empty-support SPMF
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
    · rfl
    · apply ENNReal.tsum_le_tsum
      intro i
      gcongr ?_ * ?_
      apply h
      rfl

end CCPO

noncomputable instance instRandomChoice : RandomChoice SPMF.Cost where
  choose lo hi h := by
    exact SPMF.bind (choose lo hi h : SPMF (ULift {x : Nat // lo ≤ x ∧ x ≤ hi}))
      fun n => SPMF.pure (n, 1)

instance instLawfulMonad : LawfulMonad SPMF.Cost := LawfulMonad.mk' _
  (id_map := fun x => by
    show SPMF.bind x (fun p => SPMF.bind (SPMF.pure (p.1, 0)) fun q => SPMF.pure (q.1, p.2 + q.2)) = x
    simp only [SPMF.pure_bind, Nat.add_zero]
    exact SPMF.bind_pure x)
  (pure_bind := fun a f => by
    show SPMF.bind (SPMF.pure (a, 0)) (fun p => SPMF.bind (f p.1) fun q => SPMF.pure (q.1, p.2 + q.2))
      = f a
    simp only [SPMF.pure_bind, Nat.zero_add]
    exact SPMF.bind_pure (f a))
  (bind_assoc := fun x f g => by
    show SPMF.bind (SPMF.bind x fun p => SPMF.bind (f p.1) fun q => SPMF.pure (q.1, p.2 + q.2))
        (fun r => SPMF.bind (g r.1) fun s => SPMF.pure (s.1, r.2 + s.2))
      = SPMF.bind x fun p =>
          SPMF.bind (SPMF.bind (f p.1) fun q => SPMF.bind (g q.1) fun s => SPMF.pure (s.1, q.2 + s.2))
            fun t => SPMF.pure (t.1, p.2 + t.2)
    simp only [SPMF.bind_assoc, SPMF.pure_bind, Nat.add_assoc])

section support

@[simp]
theorem mem_support_pure_iff {a b : α} {n : Nat} :
    (b, n) ∈ (Pure.pure a : SPMF.Cost α).support ↔ b = a ∧ n = 0 := by
  have : (Pure.pure a : SPMF.Cost α) = (Pure.pure (a, 0) : SPMF _) := rfl
  simp [this, Prod.mk.injEq]

@[simp]
theorem mem_support_bind_iff
    {m : SPMF.Cost α} {f : α → SPMF.Cost β} {b : β} {n : Nat} :
    (b, n) ∈ (m >>= f).support ↔
    ∃ a n1 n2, (a, n1) ∈ m.support ∧ (b, n2) ∈ (f a).support ∧ n = n1 + n2 := by
  have : (m >>= f : SPMF.Cost β) =
      SPMF.bind m fun pair =>
        SPMF.bind (f pair.1) fun pair2 =>
          SPMF.pure (pair2.1, pair.2 + pair2.2) := rfl
  rw [this]
  simp only [SPMF.bind_eq, SPMF.pure_eq, SPMF.mem_support_bind_iff, SPMF.mem_support_pure_iff,
    Prod.mk.injEq]
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
        fun k => SPMF.pure (k, 1) := rfl
  rw [this]
  simp only [SPMF.bind_eq, SPMF.pure_eq, SPMF.mem_support_bind_iff, SPMF.mem_support_choose_iff,
             SPMF.mem_support_pure_iff, Prod.mk.injEq, true_and]
  constructor
  · rintro ⟨k, rfl, rfl⟩
    rfl
  · rintro rfl
    exact ⟨n, rfl, rfl⟩

@[simp]
theorem mem_support_map_iff {m : SPMF.Cost α} {f : α → β} {b : β} {n : Nat} :
    (b, n) ∈ (f <$> m).support ↔ ∃ a, (a, n) ∈ m.support ∧ b = f a := by
  have : (f <$> m : SPMF.Cost β) = m >>= fun a => Pure.pure (f a) := rfl
  rw [this]
  simp only [mem_support_bind_iff, mem_support_pure_iff]
  constructor
  · rintro ⟨a, n1, n2, hmem, ⟨rfl, rfl⟩, rfl⟩
    exact ⟨a, by simpa using hmem, rfl⟩
  · rintro ⟨a, hmem, rfl⟩
    exact ⟨a, n, 0, hmem, ⟨rfl, rfl⟩, rfl⟩

end support

section observations

/-- The may observation. -/
def mayObs : Obs SPMF.Cost.{u} (WPC Mix.angelic) where
  spec g := fun Q => ∃ p ∈ SPMF.support g, Q p.1 p.2
  map_pure a := by
    funext Q; apply propext
    constructor
    · rintro ⟨⟨b, n⟩, hp, h⟩
      obtain ⟨rfl, rfl⟩ := mem_support_pure_iff.mp hp
      exact h
    · exact fun h => ⟨(a, 0), mem_support_pure_iff.mpr ⟨rfl, rfl⟩, h⟩
  map_bind x k := by
    funext Q; apply propext
    constructor
    · rintro ⟨⟨b, n⟩, hp, h⟩
      obtain ⟨a, n1, n2, h1, h2, rfl⟩ := mem_support_bind_iff.mp hp
      exact ⟨(a, n1), h1, (b, n2), h2, h⟩
    · rintro ⟨⟨a, n1⟩, h1, ⟨b, n2⟩, h2, h⟩
      exact ⟨(b, n1 + n2), mem_support_bind_iff.mpr ⟨a, n1, n2, h1, h2, rfl⟩, h⟩
  map_choose lo hi h := by
    funext Q; apply propext
    constructor
    · rintro ⟨⟨a, c⟩, hp, h⟩
      obtain rfl := mem_support_choose_iff.mp hp
      exact ⟨a, h⟩
    · exact fun ⟨a, h⟩ => ⟨(a, 1), mem_support_choose_iff.mpr rfl, h⟩

/-- The always observation. -/
def alwaysObs : Obs SPMF.Cost.{u} (WPC Mix.demonic) where
  spec g := fun Q => ∀ p ∈ SPMF.support g, Q p.1 p.2
  map_pure a := by
    funext Q; apply propext
    constructor
    · exact fun h => h (a, 0) (mem_support_pure_iff.mpr ⟨rfl, rfl⟩)
    · rintro h ⟨b, n⟩ hp
      obtain ⟨rfl, rfl⟩ := mem_support_pure_iff.mp hp
      exact h
  map_bind x k := by
    funext Q; apply propext
    constructor
    · rintro h ⟨a, n1⟩ h1 ⟨b, n2⟩ h2
      exact h (b, n1 + n2) (mem_support_bind_iff.mpr ⟨a, n1, n2, h1, h2, rfl⟩)
    · rintro h ⟨b, n⟩ hp
      obtain ⟨a, n1, n2, h1, h2, rfl⟩ := mem_support_bind_iff.mp hp
      exact h (a, n1) h1 (b, n2) h2
  map_choose lo hi h := by
    funext Q; apply propext
    constructor
    · exact fun hq a => hq (a, 1) (mem_support_choose_iff.mpr rfl)
    · rintro hq ⟨a, c⟩ hp
      obtain rfl := mem_support_choose_iff.mp hp
      exact hq a

/-- The worst-case observation: the most choices any run of the generator can make. -/
noncomputable def worstObs : Obs SPMF.Cost.{u} (WPC Mix.sup) where
  spec g := fun post => ⨆ p ∈ SPMF.support g, post p.1 p.2
  map_pure a := by
    funext post
    refine le_antisymm (iSup₂_le ?_)
      (le_iSup₂_of_le (a, 0) (mem_support_pure_iff.mpr ⟨rfl, rfl⟩) le_rfl)
    rintro ⟨b, n⟩ hp
    obtain ⟨rfl, rfl⟩ := mem_support_pure_iff.mp hp
    exact le_rfl
  map_bind x k := by
    funext post
    refine le_antisymm (iSup₂_le ?_) (iSup₂_le fun p hp => iSup₂_le fun q hq => ?_)
    · rintro ⟨b, n⟩ hp
      obtain ⟨a, n1, n2, h1, h2, rfl⟩ := mem_support_bind_iff.mp hp
      exact le_iSup₂_of_le (a, n1) h1 (le_iSup₂_of_le (b, n2) h2 le_rfl)
    · exact le_iSup₂_of_le (q.1, p.2 + q.2)
        (mem_support_bind_iff.mpr ⟨p.1, p.2, q.2, hp, hq, rfl⟩) le_rfl
  map_choose lo hi h := by
    funext post
    refine le_antisymm (iSup₂_le ?_) (iSup_le fun a => ?_)
    · rintro ⟨a, c⟩ hp
      obtain rfl := mem_support_choose_iff.mp hp
      exact le_iSup (fun a => post a 1) a
    · exact le_iSup₂_of_le (a, 1) (mem_support_choose_iff.mpr rfl) le_rfl


instance : mayObs.MonotoneC := ⟨fun _ _ _ h ⟨q, hq, hp⟩ => ⟨q, hq, h _ _ hp⟩⟩

instance : alwaysObs.MonotoneC := ⟨fun _ _ _ h hp _ ha => h _ _ (hp _ ha)⟩

instance : worstObs.MonotoneC := ⟨fun _ _ _ h => iSup₂_mono fun p _ => h p.1 p.2⟩

/-- Support membership, read through a specification the may observation equals. -/
theorem mem_support_of_may {g : SPMF.Cost α} {w : WPC Mix.angelic α} (h : mayObs.spec g = w)
    {a : α} {n : Nat} : (a, n) ∈ SPMF.support g ↔ w fun b m => b = a ∧ m = n := by
  refine Iff.trans ⟨fun h => ⟨(a, n), h, rfl, rfl⟩, ?_⟩ (iff_of_eq (congrFun h _))
  rintro ⟨⟨b, m⟩, hp, rfl, rfl⟩
  exact hp

/-- A run with its cost is the may observation at the postcondition `fun b m => b = a ∧ m = n`. -/
theorem mem_support_iff_may {g : SPMF.Cost α} {a : α} {n : Nat} :
    (a, n) ∈ SPMF.support g ↔ mayObs.spec g fun b m => b = a ∧ m = n :=
  mem_support_of_may rfl

end observations

end SPMF.Cost
