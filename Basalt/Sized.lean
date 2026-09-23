/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt.Gen

open Lean.Order

/-!
# Size-Parameterized Generators

`Sized` gives a generator monad an ambient size parameter to branch on, and `WithSize G` adds a size
to any generator monad `G`. `MonoSized` is the side condition that lets `sized` and `resize` appear
in the body of a `partial_fixpoint`.
-/

/-- A monad with an ambient size parameter. -/
class Sized (g : Type u → Type v) where
  sized {α : Type u} : (Nat → g α) → g α
  resize {α : Type u} : Nat → g α → g α

def getSize [Monad m] [Sized m] : m Nat := Sized.sized (fun n => pure n)

/-- The monotonicity facts `sized` and `resize` must satisfy for a recursive generator that uses
them to be definable by `partial_fixpoint`; the analogue of `MonoBind` for `Sized`. -/
class MonoSized (g : Type u → Type v) [Sized g] [∀ α, PartialOrder (g α)] where
  sized_mono {α : Type u} {f₁ f₂ : Nat → g α} (h : ∀ n, f₁ n ⊑ f₂ n) :
    Sized.sized f₁ ⊑ Sized.sized f₂
  resize_mono {α : Type u} {n : Nat} {x y : g α} (h : x ⊑ y) :
    Sized.resize n x ⊑ Sized.resize n y

/-- Lemma allowing us to use `sized` in functions marked as `partial_fixpoint` (the `monotonicity`
tactic is used under the hood by `partial_fixpoint`). -/
@[partial_fixpoint_monotone]
theorem monotone_sized (g : Type u → Type v) [Sized g] [∀ α, PartialOrder (g α)] [MonoSized g]
    {α : Type u} {γ : Sort w} [PartialOrder γ]
    (f : γ → Nat → g α) (hmono : monotone f) :
    monotone (fun x => Sized.sized (f x)) :=
  fun x y hxy => MonoSized.sized_mono (hmono x y hxy)

/-- Lemma allowing us to use `resize` in functions marked as `partial_fixpoint` (the `monotonicity`
tactic is used under the hood by `partial_fixpoint`). -/
@[partial_fixpoint_monotone]
theorem monotone_resize (g : Type u → Type v) [Sized g] [∀ α, PartialOrder (g α)] [MonoSized g]
    {α : Type u} {γ : Sort w} [PartialOrder γ] (n : Nat)
    (f : γ → g α) (hmono : monotone f) :
    monotone (fun x => Sized.resize n (f x)) :=
  fun x y hxy => MonoSized.resize_mono (hmono x y hxy)

/-- `G` equipped with an ambient size parameter. -/
def WithSize (G : Type → Type v) (α : Type) : Type v := ReaderT Nat G α

/-- Close over the size parameter, recovering a plain generator. -/
def WithSize.run (g : WithSize G α) (n : Nat) : G α := ReaderT.run g n

/-- Run a size-agnostic generator at any size. -/
def WithSize.lift (g : G α) : WithSize G α := fun _ => g

instance instRandomChoiceWithSize [RandomChoice G] : RandomChoice (WithSize G) where
  choose lo hi h := fun _ => RandomChoice.choose lo hi h

instance instGenWithSize [Gen G] : Gen (WithSize G) where
  instInhabited := fun α => inferInstanceAs (Inhabited (Nat → G α))
  instMonad := inferInstanceAs (Monad (ReaderT Nat G))
  instRandomChoice := instRandomChoiceWithSize
  instCCPO := fun α => inferInstanceAs (CCPO (Nat → G α))
  instMonoBind := inferInstanceAs (MonoBind (ReaderT Nat G))

instance instSizedWithSize [Monad G] : Sized (WithSize G) where
  sized f := fun n => f n n
  resize n g := fun _ => g n

instance instMonoSizedWithSize [Gen G] : MonoSized (WithSize G) where
  sized_mono h := fun n => h n n
  resize_mono h := fun _ => h _
