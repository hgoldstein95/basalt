/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
module

public import Basalt.GenRel
public import Basalt.SPMF.Cost
public import Basalt.Walk.Attr

/-!
# Erasing Costs

A generator run at `SPMF.Cost` and at `SPMF` should have one distribution once its costs are
dropped. That is a free theorem, so it is proved per generator, as the two inequalities fixpoint
induction can prove: `ErasedLe` by induction at `SPMF.Cost`, `LeErased` at `SPMF`. `walk` proves
each through the relation's proof that it is a `GenRel`.
-/

@[expose] public section

open RandomChoice ENNReal

namespace SPMF.Cost

variable {α β : Type}

/-- `y` with its costs dropped expects no more of any function than `x` does. -/
def ErasedLe (y : SPMF.Cost α) (x : SPMF α) : Prop :=
  ∀ f : α → ℝ≥0∞, expectObs.spec y (fun a _ => f a) ≤ SPMF.expectObs.spec x f

/-- `x` expects no more of any function than `y` does with its costs dropped. -/
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

theorem erasedLe_pure (a : α) : ErasedLe (Pure.pure a) (Pure.pure a) := fun f =>
  (expect_erased_pure a f).le

theorem erasedLe_bind {y : SPMF.Cost α} {x : SPMF α} {k' : α → SPMF.Cost β} {k : α → SPMF β}
    (hk : ∀ a, ErasedLe (k' a) (k a)) (hx : ErasedLe y x) : ErasedLe (y >>= k') (x >>= k) :=
  fun f => by
    rw [expect_erased_bind, congrFun (SPMF.expectObs.map_bind x k) f]
    exact (Obs.MonotoneC.spec_mono y fun a _ => hk a f).trans (hx _)

theorem erasedLe_map {y : SPMF.Cost α} {x : SPMF α} (f : α → β) (hx : ErasedLe y x) :
    ErasedLe (f <$> y) (f <$> x) := by
  rw [← bind_pure_comp, ← bind_pure_comp]
  exact erasedLe_bind (fun a => erasedLe_pure (f a)) hx

theorem erasedLe_default (x : SPMF α) : ErasedLe default x := fun f => by
  show SPMF.expect (default : SPMF (α × Nat)) _ ≤ _
  simp [SPMF.expect, SPMF.default_apply]

theorem erasedLe_choose (lo hi : Nat) (h : lo ≤ hi) :
    ErasedLe (choose lo hi h : SPMF.Cost _) (choose lo hi h) := fun f =>
  (expect_erased_choose lo hi h f).le

/-- Fixpoint induction on the `SPMF.Cost` side: `expect` is continuous. -/
theorem ErasedLe.admissible (x : SPMF α) :
    Lean.Order.admissible fun y : SPMF.Cost α => ErasedLe y x :=
  Lean.Order.admissible_pi _ fun f => SPMF.admissible_expect_le (fun p : α × Nat => f p.1) _

@[walk_rel]
theorem genRel_erasedLe : GenRel SPMF.Cost SPMF @ErasedLe where
  pure := erasedLe_pure
  bind := erasedLe_bind
  map := erasedLe_map
  default := erasedLe_default
  choose := erasedLe_choose
  admissible := ErasedLe.admissible

end erasedLe

section leErased

theorem leErased_pure (a : α) : LeErased (Pure.pure a) (Pure.pure a) := fun f =>
  (expect_erased_pure a f).ge

theorem leErased_bind {x : SPMF α} {y : SPMF.Cost α} {k' : α → SPMF β} {k : α → SPMF.Cost β}
    (hk : ∀ a, LeErased (k' a) (k a)) (hx : LeErased x y) : LeErased (x >>= k') (y >>= k) :=
  fun f => by
    rw [expect_erased_bind, congrFun (SPMF.expectObs.map_bind x k') f]
    exact (Obs.Monotone.spec_mono x fun a => hk a f).trans (hx _)

theorem leErased_map {x : SPMF α} {y : SPMF.Cost α} (f : α → β) (hx : LeErased x y) :
    LeErased (f <$> x) (f <$> y) := by
  rw [← bind_pure_comp, ← bind_pure_comp]
  exact leErased_bind (fun a => leErased_pure (f a)) hx

theorem leErased_default (y : SPMF.Cost α) : LeErased default y := fun f => by
  simp [SPMF.expectObs, SPMF.expect, SPMF.default_apply]

theorem leErased_choose (lo hi : Nat) (h : lo ≤ hi) :
    LeErased (choose lo hi h : SPMF _) (choose lo hi h : SPMF.Cost _) := fun f =>
  (expect_erased_choose lo hi h f).ge

/-- Fixpoint induction on the `SPMF` side: `expect` is continuous. -/
theorem LeErased.admissible (y : SPMF.Cost α) :
    Lean.Order.admissible fun x : SPMF α => LeErased x y :=
  Lean.Order.admissible_pi _ fun f => SPMF.admissible_expect_le f _

@[walk_rel]
theorem genRel_leErased : GenRel SPMF SPMF.Cost @LeErased where
  pure := leErased_pure
  bind := leErased_bind
  map := leErased_map
  default := leErased_default
  choose := leErased_choose
  admissible := LeErased.admissible

end leErased

end SPMF.Cost
