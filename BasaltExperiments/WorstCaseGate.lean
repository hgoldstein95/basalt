/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt
import Mathlib.Data.ENat.Lattice

/-!
# Worst-Case Cost as an Upper Bound in the `sup` Algebra, Prototyped

What the `isBounded_*` rules would become under `PLAN.md`'s Stage 2: the most choices any run makes
is the observation of `SPMF.Cost` into `ℕ∞` whose choice is a supremum, bounded above by the rules
of `Basalt/Obs/Ordered.lean`. `IsBounded g fun _ => k` reduces to it, and the computed `ℕ∞` bound is
turned back into `k` by moving its casts to the root.
-/

open RandomChoice

/-- A choice is as large as its largest outcome. -/
noncomputable def Mix.sup : Mix.{u} ℕ∞ where mix _ _ F := ⨆ a, F a

namespace SPMF.Cost

/-- The worst-case observation. -/
noncomputable def worstObs : Obs SPMF.Cost.{u} (WPC Mix.sup) where
  spec g := fun post => ⨆ p ∈ SPMF.support g, post p.1 p.2
  map_pure a := by
    funext post
    refine le_antisymm (iSup₂_le ?_) (le_iSup₂_of_le (a, 0) (mem_support_pure_iff.mpr ⟨rfl, rfl⟩) le_rfl)
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

instance : worstObs.MonotoneC :=
  ⟨fun _ _ _ h => iSup₂_mono fun p _ => h p.1 p.2⟩

/-- The number of choices. -/
def count (α : Type u) : α → Nat → ℕ∞ := fun _ n => n

/-- The judgment `IsBounded g fun _ => k`, with `k` to be found, as an upper bound on `worstObs`. -/
theorem isBounded_of_worst {g : SPMF.Cost α} {b : ℕ∞} {k : Nat}
    (h : worstObs.spec g (fun _ n => (n : ℕ∞)) ≤ b) (hb : b = (k : ℕ∞)) :
    IsBounded g fun _ => k := fun p hp =>
  Nat.cast_le.mp ((le_iSup₂_of_le p hp le_rfl).trans (h.trans hb.le))

theorem worst_le_add_of_le {x : SPMF.Cost α} {p : α → Nat → ℕ∞} {k B : ℕ∞}
    (hx : worstObs.spec x (fun _ n => (n : ℕ∞)) ≤ B) (hp : ∀ a n, p a n = k + (n : ℕ∞)) :
    worstObs.spec x p ≤ k + B :=
  iSup₂_le fun q hq => (hp q.1 q.2).le.trans
    (add_le_add le_rfl ((le_iSup₂_of_le q hq le_rfl).trans hx))

theorem worst_le_add_of_isBounded {x : SPMF.Cost α} {p : α → Nat → ℕ∞} {k : ℕ∞} {K : Nat}
    (hx : IsBounded x fun _ => K) (hp : ∀ a n, p a n = k + (n : ℕ∞)) :
    worstObs.spec x p ≤ k + (K : ℕ∞) :=
  worst_le_add_of_le (iSup₂_le fun q hq => Nat.cast_le.mpr (hx q hq)) hp

end SPMF.Cost

@[norm_cast] theorem ENat.coe_max' (a b : ℕ) : ((max a b : ℕ) : ℕ∞) = max (a : ℕ∞) (b : ℕ∞) :=
  Nat.mono_cast.map_max

@[norm_cast] theorem ENat.coe_ite' (p : Prop) [Decidable p] (a b : ℕ) :
    ((if p then a else b : ℕ) : ℕ∞) = if p then (a : ℕ∞) else (b : ℕ∞) := by split <;> rfl

namespace Mix

@[gen_rule] theorem sup_mix_le {lo hi : Nat} {F : ULift.{u} {x : Nat // lo ≤ x ∧ x ≤ hi} → ℕ∞}
    {d : ℕ∞} (h : ∀ x (hx : lo ≤ x ∧ x ≤ hi), F ⟨⟨x, hx⟩⟩ ≤ d) : Mix.sup.mix lo hi F ≤ d :=
  iSup_le fun a => h _ a.down.property

@[gen_rule] theorem sup_binary_le {t e c d : ℕ∞} (ht : t ≤ c) (he : e ≤ d) :
    (Mix.sup.{u}).binary t e ≤ max c d := by
  refine iSup_le fun a => ?_
  dsimp only
  split
  · exact ht.trans (le_max_left _ _)
  · exact he.trans (le_max_right _ _)

@[gen_rule] theorem sup_threshold_le {n : Nat} {k : ℤ} {t e c d : ℕ∞} (ht : t ≤ c) (he : e ≤ d) :
    (Mix.sup.{u}).threshold n k t e ≤ max c d := by
  refine iSup_le fun a => ?_
  dsimp only
  split
  · exact ht.trans (le_max_left _ _)
  · exact he.trans (le_max_right _ _)

private theorem le_foldr_max {γ : Type v} {F : γ → ℕ∞} {cs : List ℕ∞} {l : List γ}
    (h : List.Forall₂ (fun c g => F g ≤ c) cs l) : ∀ g ∈ l, F g ≤ cs.foldr max 0 := by
  induction h with
  | nil => simp
  | cons hc _ ih =>
    intro g hg
    rcases List.mem_cons.mp hg with rfl | hg
    · exact hc.trans (le_max_left _ _)
    · exact (ih g hg).trans (le_max_right _ _)

@[gen_rule] theorem sup_index_le {γ : Type v} {l : List γ} {hne : l ≠ []} {F : γ → ℕ∞}
    {cs : List ℕ∞} (h : List.Forall₂ (fun c g => F g ≤ c) cs l) :
    (Mix.sup.{u}).index l hne F ≤ cs.foldr max 0 :=
  iSup_le fun _ => le_foldr_max h _ (List.getElem_mem _)

@[gen_rule] theorem sup_index_le_mem {γ : Type v} {l : List γ} {hne : l ≠ []} {F : γ → ℕ∞}
    {d : ℕ∞} (h : ∀ g ∈ l, F g ≤ d) : (Mix.sup.{u}).index l hne F ≤ d :=
  iSup_le fun _ => h _ (List.getElem_mem _)

@[gen_branches]
inductive BranchesLE {γ : Type v} (F : γ → ℕ∞) : List ℕ∞ → List (Nat × γ) → Prop
  | nil : BranchesLE F [] []
  | cons {w : Nat} {c : ℕ∞} {g : γ} {cs gs} (h : F g ≤ c) (hs : BranchesLE F cs gs) :
      BranchesLE F (c :: cs) ((w, g) :: gs)

private theorem selectD_le {l : List (Nat × ℕ∞)} {b : ℕ∞} (h : ∀ p ∈ l, p.2 ≤ b) (d : ℕ∞) :
    ∀ n, n < (l.map Prod.fst).sum → Obs.selectD l n d ≤ b := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    obtain ⟨k, x⟩ := hd
    intro n hn
    simp only [Obs.selectD]
    split
    · exact h (k, x) List.mem_cons_self
    · exact ih (fun p hp => h p (List.mem_cons_of_mem _ hp)) _
        (by simp only [List.map_cons, List.sum_cons] at hn; omega)

@[gen_rule] theorem sup_select_le {γ : Type v} {l : List (Nat × γ)}
    {hpos : 0 < (l.map Prod.fst).sum} {F : γ → ℕ∞} {d : ℕ∞} {cs : List ℕ∞}
    (h : BranchesLE F cs l) : (Mix.sup.{u}).select l hpos F d ≤ cs.foldr max 0 := by
  have key : ∀ q ∈ l, F q.2 ≤ cs.foldr max 0 := by
    clear hpos
    induction h with
    | nil => simp
    | cons hc _ ih =>
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact hc.trans (le_max_left _ _)
      · exact (ih q hq).trans (le_max_right _ _)
  refine iSup_le fun a => selectD_le (fun p hp => ?_) d _ ?_
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    exact key q hq
  · have h1 := a.down.property.2
    have h2 : ((l.map fun p => (p.1, F p.2)).map Prod.fst).sum = (l.map Prod.fst).sum := by
      simp [Function.comp_def]
    omega

@[gen_rule] theorem sup_rangeInt_le {lo hi : ℤ} {h : lo ≤ hi} {F : ℤ → ℕ∞} {d : ℕ∞}
    (hF : ∀ x, lo ≤ x ∧ x ≤ hi → F x ≤ d) : (Mix.sup.{0}).rangeInt lo hi h F ≤ d := by
  refine iSup_le fun a => hF _ ⟨by omega, ?_⟩
  have := a.down.property
  omega

end Mix

namespace SPMF.Cost

/-! The recursive list combinators stay laws, bridged per judgment. -/

variable {α : Type} {g : SPMF.Cost α} {b k : ℕ∞} {p : List α → Nat → ℕ∞}

@[gen_rule] theorem worst_vectorOf_le {n : Nat} (hg : worstObs.spec g (fun _ m => (m : ℕ∞)) ≤ b)
    (hp : ∀ a m, p a m = k + (m : ℕ∞)) : worstObs.spec (vectorOf n g) p ≤ k + n * b := sorry

@[gen_rule] theorem worst_listOfMaxLength_le {n : Nat}
    (hg : worstObs.spec g (fun _ m => (m : ℕ∞)) ≤ b) (hp : ∀ a m, p a m = k + (m : ℕ∞)) :
    worstObs.spec (listOfMaxLength n g) p ≤ k + (1 + n * b) := sorry

end SPMF.Cost
