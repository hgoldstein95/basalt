/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt.GenRel
import Basalt.SPMF.Cost
import Basalt.Walk.Attr

/-!
# Erasing Costs

A generator run at `SPMF.Cost` and at `SPMF` should have one distribution once its costs are
dropped. That is a free theorem, so it is proved per generator, as the two inequalities fixpoint
induction can prove: `ErasedLe` by induction at `SPMF.Cost`, `LeErased` at `SPMF`.
-/

open RandomChoice ENNReal

namespace SPMF.Cost

variable {α β : Type}

/-- `y` with its costs dropped expects no more of any function than `x` does. -/
@[walk_rel]
def ErasedLe (y : SPMF.Cost α) (x : SPMF α) : Prop :=
  ∀ f : α → ℝ≥0∞, expectObs.spec y (fun a _ => f a) ≤ SPMF.expectObs.spec x f

/-- `x` expects no more of any function than `y` does with its costs dropped. -/
@[walk_rel]
def LeErased (x : SPMF α) (y : SPMF.Cost α) : Prop :=
  ∀ f : α → ℝ≥0∞, SPMF.expectObs.spec x f ≤ expectObs.spec y (fun a _ => f a)

section host

theorem expect_erased_pure (a : α) (f : α → ℝ≥0∞) :
    expectObs.spec (Pure.pure a : SPMF.Cost α) (fun a _ => f a)
      = SPMF.expectObs.spec (Pure.pure a : SPMF α) f :=
  (congrFun (expectObs.map_pure a) _).trans (congrFun (SPMF.expectObs.map_pure a) f).symm

theorem expect_erased_bind (y : SPMF.Cost α) (k : α → SPMF.Cost β) (f : β → ℝ≥0∞) :
    expectObs.spec (y >>= k) (fun b _ => f b)
      = expectObs.spec y fun a _ => expectObs.spec (k a) fun b _ => f b :=
  congrFun (expectObs.map_bind y k) _

theorem expect_erased_choose (lo hi : Nat) (h : lo ≤ hi)
    (f : ULift.{0} {x : Nat // lo ≤ x ∧ x ≤ hi} → ℝ≥0∞) :
    expectObs.spec (choose lo hi h : SPMF.Cost _) (fun a _ => f a)
      = SPMF.expectObs.spec (choose lo hi h : SPMF _) f :=
  (congrFun (expectObs.map_choose lo hi h) _).trans
    (congrFun (SPMF.expectObs.map_choose lo hi h) f).symm

end host

section erasedLe

@[gen_rule]
theorem erasedLe_pure (a : α) : ErasedLe (Pure.pure a) (Pure.pure a) := fun f =>
  (expect_erased_pure a f).le

@[gen_rule]
theorem erasedLe_bind {y : SPMF.Cost α} {x : SPMF α} {k' : α → SPMF.Cost β} {k : α → SPMF β}
    (hk : ∀ a, ErasedLe (k' a) (k a)) (hx : ErasedLe y x) : ErasedLe (y >>= k') (x >>= k) :=
  fun f => by
    rw [expect_erased_bind, congrFun (SPMF.expectObs.map_bind x k) f]
    exact (Obs.MonotoneC.spec_mono y fun a _ => hk a f).trans (hx _)

@[gen_rule]
theorem erasedLe_map {y : SPMF.Cost α} {x : SPMF α} (f : α → β) (hx : ErasedLe y x) :
    ErasedLe (f <$> y) (f <$> x) := by
  rw [← bind_pure_comp, ← bind_pure_comp]
  exact erasedLe_bind (fun a => erasedLe_pure (f a)) hx

@[gen_rule]
theorem erasedLe_ite {p : Prop} [Decidable p] {y₁ y₂ : SPMF.Cost α} {x₁ x₂ : SPMF α}
    (h₁ : p → ErasedLe y₁ x₁) (h₂ : ¬p → ErasedLe y₂ x₂) :
    ErasedLe (if p then y₁ else y₂) (if p then x₁ else x₂) :=
  GenRel.ite h₁ h₂

@[gen_rule]
theorem erasedLe_dite {p : Prop} [Decidable p] {y₁ : p → SPMF.Cost α} {y₂ : ¬p → SPMF.Cost α}
    {x₁ : p → SPMF α} {x₂ : ¬p → SPMF α}
    (h₁ : ∀ h, ErasedLe (y₁ h) (x₁ h)) (h₂ : ∀ h, ErasedLe (y₂ h) (x₂ h)) :
    ErasedLe (if h : p then y₁ h else y₂ h) (if h : p then x₁ h else x₂ h) :=
  GenRel.dite h₁ h₂

@[gen_rule]
theorem erasedLe_default (x : SPMF α) : ErasedLe default x := fun f => by
  show SPMF.expect (default : SPMF (α × Nat)) _ ≤ _
  simp [SPMF.expect, SPMF.default_apply]

@[gen_rule]
theorem erasedLe_choose (lo hi : Nat) (h : lo ≤ hi) :
    ErasedLe (choose lo hi h : SPMF.Cost _) (choose lo hi h) := fun f =>
  (expect_erased_choose lo hi h f).le

/-- Fixpoint induction on the `SPMF.Cost` side: `expect` is continuous. -/
theorem ErasedLe.admissible (x : SPMF α) :
    Lean.Order.admissible fun y : SPMF.Cost α => ErasedLe y x := by
  intro c hc ih f
  show SPMF.expect _ _ ≤ _
  rw [SPMF.expect_csup]
  exact iSup₂_le fun y hy => ih y hy f

end erasedLe

section leErased

@[gen_rule]
theorem leErased_pure (a : α) : LeErased (Pure.pure a) (Pure.pure a) := fun f =>
  (expect_erased_pure a f).ge

@[gen_rule]
theorem leErased_bind {x : SPMF α} {y : SPMF.Cost α} {k' : α → SPMF β} {k : α → SPMF.Cost β}
    (hk : ∀ a, LeErased (k' a) (k a)) (hx : LeErased x y) : LeErased (x >>= k') (y >>= k) :=
  fun f => by
    rw [expect_erased_bind, congrFun (SPMF.expectObs.map_bind x k') f]
    exact (Obs.Monotone.spec_mono x fun a => hk a f).trans (hx _)

@[gen_rule]
theorem leErased_map {x : SPMF α} {y : SPMF.Cost α} (f : α → β) (hx : LeErased x y) :
    LeErased (f <$> x) (f <$> y) := by
  rw [← bind_pure_comp, ← bind_pure_comp]
  exact leErased_bind (fun a => leErased_pure (f a)) hx

@[gen_rule]
theorem leErased_ite {p : Prop} [Decidable p] {x₁ x₂ : SPMF α} {y₁ y₂ : SPMF.Cost α}
    (h₁ : p → LeErased x₁ y₁) (h₂ : ¬p → LeErased x₂ y₂) :
    LeErased (if p then x₁ else x₂) (if p then y₁ else y₂) :=
  GenRel.ite h₁ h₂

@[gen_rule]
theorem leErased_dite {p : Prop} [Decidable p] {x₁ : p → SPMF α} {x₂ : ¬p → SPMF α}
    {y₁ : p → SPMF.Cost α} {y₂ : ¬p → SPMF.Cost α}
    (h₁ : ∀ h, LeErased (x₁ h) (y₁ h)) (h₂ : ∀ h, LeErased (x₂ h) (y₂ h)) :
    LeErased (if h : p then x₁ h else x₂ h) (if h : p then y₁ h else y₂ h) :=
  GenRel.dite h₁ h₂

@[gen_rule]
theorem leErased_default (y : SPMF.Cost α) : LeErased default y := fun f => by
  simp [SPMF.expectObs, SPMF.expect, SPMF.default_apply]

@[gen_rule]
theorem leErased_choose (lo hi : Nat) (h : lo ≤ hi) :
    LeErased (choose lo hi h : SPMF _) (choose lo hi h : SPMF.Cost _) := fun f =>
  (expect_erased_choose lo hi h f).ge

/-- Fixpoint induction on the `SPMF` side: `expect` is continuous. -/
theorem LeErased.admissible (y : SPMF.Cost α) :
    Lean.Order.admissible fun x : SPMF α => LeErased x y := by
  intro c hc ih f
  show SPMF.expect _ _ ≤ _
  rw [SPMF.expect_csup]
  exact iSup₂_le fun x hx => ih x hx f

end leErased

end SPMF.Cost
