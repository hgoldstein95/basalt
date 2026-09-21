/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt.RandomChoice

/-!
# Specification Monads

The targets of an observation: continuation monads over an algebra `Ω` whose one operation, `Mix.mix`,
says what a uniform choice means in `Ω`. `WP m` transforms a postcondition on values; `WPC m`
transforms one that also sees the number of choices made.
-/

/-- What a uniform choice over `[lo, hi]` means in `Ω`, given what each outcome means. A structure
rather than a class, because `Prop` carries two. -/
structure Mix.{u, w} (Ω : Type w) where
  mix : (lo hi : Nat) → (ULift.{u} {x : Nat // lo ≤ x ∧ x ≤ hi} → Ω) → Ω

/-- A choice holds when every outcome does. -/
def Mix.demonic : Mix.{u} Prop where mix _ _ F := ∀ x, F x

/-- A choice holds when some outcome does. -/
def Mix.angelic : Mix.{u} Prop where mix _ _ F := ∃ x, F x

/-- Transformers from a postcondition on values to an `Ω`. The algebra is a parameter only to select
the `RandomChoice` instance. -/
def WP {Ω : Type w} (_m : Mix.{u} Ω) (α : Type u) : Type (max u w) := (α → Ω) → Ω

namespace WP

variable {Ω : Type w} {m : Mix.{u} Ω}

instance : Monad (WP m) where
  pure a := fun post => post a
  bind m k := fun post => m fun a => k a post

instance : LawfulMonad (WP m) := LawfulMonad.mk' _
  (id_map := fun _ => rfl) (pure_bind := fun _ _ => rfl) (bind_assoc := fun _ _ _ => rfl)

instance : RandomChoice (WP m) where
  choose lo hi _ := fun post => m.mix lo hi post

theorem choose_bind_apply {lo hi : Nat} {h : lo ≤ hi}
    (k : ULift.{u} {x : Nat // lo ≤ x ∧ x ≤ hi} → WP m α) (post : α → Ω) :
    (RandomChoice.choose lo hi h >>= k) post = m.mix lo hi fun a => k a post := rfl

theorem map_choose_apply {lo hi : Nat} {h : lo ≤ hi}
    (f : ULift.{u} {x : Nat // lo ≤ x ∧ x ≤ hi} → α) (post : α → Ω) :
    (f <$> RandomChoice.choose lo hi h : WP m α) post = m.mix lo hi fun a => post (f a) := rfl

theorem ite_apply {p : Prop} [Decidable p] (x y : WP m α) (post : α → Ω) :
    (if p then x else y) post = if p then x post else y post := by
  split <;> rfl

end WP

/-- Transformers from a postcondition on values and choice counts to an `Ω`. -/
def WPC {Ω : Type w} (_m : Mix.{u} Ω) (α : Type u) : Type (max u w) := (α → Nat → Ω) → Ω

namespace WPC

variable {Ω : Type w} {m : Mix.{u} Ω}

instance : Monad (WPC m) where
  pure a := fun post => post a 0
  bind m k := fun post => m fun a n => k a fun b n' => post b (n + n')

instance : LawfulMonad (WPC m) := LawfulMonad.mk' _
  (id_map := fun _ => rfl)
  (pure_bind := fun _ _ => by funext post; simp [bind, pure])
  (bind_assoc := fun _ _ _ => by funext post; simp [bind, Nat.add_assoc])

instance : RandomChoice (WPC m) where
  choose lo hi _ := fun post => m.mix lo hi fun a => post a 1

theorem choose_bind_apply {lo hi : Nat} {h : lo ≤ hi}
    (k : ULift.{u} {x : Nat // lo ≤ x ∧ x ≤ hi} → WPC m α) (post : α → Nat → Ω) :
    (RandomChoice.choose lo hi h >>= k) post
      = m.mix lo hi fun a => k a fun b n => post b (1 + n) := rfl

theorem map_choose_apply {lo hi : Nat} {h : lo ≤ hi}
    (f : ULift.{u} {x : Nat // lo ≤ x ∧ x ≤ hi} → α) (post : α → Nat → Ω) :
    (f <$> RandomChoice.choose lo hi h : WPC m α) post = m.mix lo hi fun a => post (f a) 1 := rfl

theorem ite_apply {p : Prop} [Decidable p] (x y : WPC m α) (post : α → Nat → Ω) :
    (if p then x else y) post = if p then x post else y post := by
  split <;> rfl

end WPC
