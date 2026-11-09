/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt.Gen

/-!
# Tiered Enumeration

FEAT's enumeration as an interpretation: a `Finite` is a set presented by a cardinality and an
indexing function, and an `Enumerate` is the `Finite` set of values of each cost.
-/

open Lean.Order

/-- A monad that can do tiered enumeration. -/
class Enum (g : Type u → Type v) where
  /-- Add one to the tier of the enclosed generator. -/
  pay : g α → g α

/-- The monotonicity fact `pay` must satisfy for a recursive generator that uses it to be definable
by `partial_fixpoint`; the analogue of `MonoBind` for `Enum`. -/
class MonoEnum (g : Type u → Type v) [Enum g] [∀ α, PartialOrder (g α)] where
  pay_mono {α : Type u} {x₁ x₂ : g α} (h : x₁ ⊑ x₂) : Enum.pay x₁ ⊑ Enum.pay x₂

@[partial_fixpoint_monotone]
theorem monotone_pay (g : Type u → Type v) [Enum g] [∀ α, PartialOrder (g α)] [MonoEnum g]
    {α : Type u} {γ : Sort w} [PartialOrder γ]
    (f : γ → g α) (hmono : monotone f) :
    monotone (fun x => Enum.pay (f x)) :=
  fun x y hxy => MonoEnum.pay_mono (hmono x y hxy)

namespace Basalt

/-! ## Finite sets -/

/-- A set of `card` values, presented by an indexing function (since Lean does not allow infinite
lists).  -/
inductive Finite (α : Type u) : Type u where
  /-- The undefined set, the bottom of the flat order on `Finite`. -/
  | undef : Finite α
  /-- The set of the `card` values `index 0, …, index (card - 1)`. -/
  | mk (card : Nat) (index : Fin card → α) : Finite α

namespace Finite

/-- The empty set; distinct from `undef`, which is a set whose cardinality is unknown. -/
def empty : Finite α := .mk 0 Fin.elim0

/-- The one-element set. -/
def singleton (a : α) : Finite α := .mk 1 fun _ => a

/-- FEAT's `fCard`. -/
def card? : Finite α → Option Nat
  | .undef => none
  | .mk n _ => some n

/-- FEAT's `fIndex`, bounds-checked. -/
def get? : Finite α → Nat → Option α
  | .undef, _ => none
  | .mk n f, i => if h : i < n then some (f ⟨i, h⟩) else none

/-- The values of a defined set, in index order. -/
def toList? : Finite α → Option (List α)
  | .undef => none
  | .mk _ f => some (List.ofFn f)

/-- FEAT's `fPlus`: the disjoint union, indexing `x` before `y`. -/
def union : Finite α → Finite α → Finite α
  | .undef, _ => .undef
  | _, .undef => .undef
  | .mk m f, .mk n g =>
    .mk (m + n) fun i =>
      if h : i.val < m then f ⟨i.val, h⟩ else g ⟨i.val - m, by have := i.isLt; omega⟩

/-- The union of a list of sets, in order. -/
def flatten (xs : List (Finite α)) : Finite α := xs.foldr union empty

/-- The union of `f a` over the values `a` of `x`, indexed in the order `x` indexes them. -/
def bind (x : Finite α) (f : α → Finite β) : Finite β :=
  match x with
  | .undef => .undef
  | .mk _ index => flatten (List.ofFn fun i => f (index i))

/-- `fmap` reindexing, so the cardinality is untouched. -/
def map (f : α → β) : Finite α → Finite β
  | .undef => .undef
  | .mk n index => .mk n (f ∘ index)

instance : Monad Finite where
  pure := Finite.singleton
  bind := Finite.bind
  map := Finite.map

/-- `default` is `undef`: the bottom element, the least defined set. -/
instance : Inhabited (Finite α) where
  default := .undef

instance instPartialOrder : PartialOrder (Finite α) := FlatOrder.instOrder (b := .undef)

instance instCCPO : CCPO (Finite α) := FlatOrder.instCCPO (b := .undef)

theorem eq_undef_or_eq {x y : Finite α} (h : x ⊑ y) : x = .undef ∨ x = y := by
  cases h with
  | bot => exact .inl rfl
  | refl => exact .inr rfl

@[simp] theorem union_undef_left {y : Finite α} : union .undef y = .undef := rfl

@[simp] theorem union_undef_right {x : Finite α} : union x .undef = .undef := by cases x <;> rfl

theorem union_mono {x₁ x₂ y₁ y₂ : Finite α} (hx : x₁ ⊑ x₂) (hy : y₁ ⊑ y₂) :
    union x₁ y₁ ⊑ union x₂ y₂ := by
  rcases eq_undef_or_eq hx with rfl | rfl
  · rw [union_undef_left]
    exact FlatOrder.rel.bot
  · rcases eq_undef_or_eq hy with rfl | rfl
    · rw [union_undef_right]
      exact FlatOrder.rel.bot
    · exact FlatOrder.rel.refl

theorem flatten_eq_undef {xs : List (Finite α)} (h : Finite.undef ∈ xs) :
    flatten xs = .undef := by
  induction xs with
  | nil => cases h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with rfl | h
    · rfl
    · show union x (flatten xs) = .undef
      rw [ih h, union_undef_right]

theorem flatten_ofFn_mono {n : Nat} {f g : Fin n → Finite α} (h : ∀ i, f i ⊑ g i) :
    flatten (List.ofFn f) ⊑ flatten (List.ofFn g) := by
  induction n with
  | zero => exact FlatOrder.rel.refl
  | succ n ih =>
    rw [List.ofFn_succ, List.ofFn_succ]
    exact union_mono (h 0) (ih fun i => h i.succ)

instance : MonoBind Finite where
  bind_mono_left h := by
    rcases eq_undef_or_eq h with rfl | rfl
    · exact FlatOrder.rel.bot
    · exact FlatOrder.rel.refl
  bind_mono_right {_ _ x f₁ f₂} h := by
    cases x with
    | undef => exact FlatOrder.rel.refl
    | mk n index =>
      show Finite.bind (.mk n index) f₁ ⊑ Finite.bind (.mk n index) f₂
      by_cases hu : ∃ i, f₁ (index i) = .undef
      · obtain ⟨i, hi⟩ := hu
        rw [show Finite.bind (.mk n index) f₁ = .undef from
          flatten_eq_undef (List.mem_ofFn.mpr ⟨i, hi⟩)]
        exact FlatOrder.rel.bot
      · have heq : ∀ i, f₁ (index i) = f₂ (index i) := fun i =>
          (eq_undef_or_eq (h (index i))).resolve_left (fun hb => hu ⟨i, hb⟩)
        rw [show Finite.bind (.mk n index) f₁ = Finite.bind (.mk n index) f₂ from
          congrArg flatten (congrArg List.ofFn (funext heq))]
        exact FlatOrder.rel.refl

end Finite

/-! ## Tiered enumerations -/

/-- FEAT's `Enumerate`: the values of cost `0`, of cost `1`, … each a `Finite` set. A generator
interpreted here is the set of values it can produce, graded by how much its `pay`s cost. -/
def Enumerate (α : Type u) : Type u := Nat → Finite α

namespace Enumerate

/-- The values of cost exactly `n`. -/
def tier (x : Enumerate α) (n : Nat) : Finite α := x n

/-- The values of cost at most `n`, cheapest first. -/
def upTo (x : Enumerate α) (n : Nat) : Finite α :=
  Finite.flatten (List.ofFn fun k : Fin (n + 1) => x k)

/-- A finite set, all of it free. -/
def ofFinite (s : Finite α) : Enumerate α := fun n =>
  match n with
  | 0 => s
  | _ + 1 => .empty

/-- One value, free. -/
def pure (a : α) : Enumerate α := ofFinite (.singleton a)

/-- Reindex every tier; costs are untouched. -/
def map (f : α → β) (x : Enumerate α) : Enumerate β := fun n => (x n).map f

/-- The disjoint union, tier by tier. -/
def union (x y : Enumerate α) : Enumerate α := fun n => (x n).union (y n)

/-- FEAT's convolution: a result of cost `n` is a value of `x` of cost `k` followed by a value of
its continuation of cost `n - k`. -/
def bind (x : Enumerate α) (f : α → Enumerate β) : Enumerate β := fun n =>
  Finite.flatten (List.ofFn fun k : Fin (n + 1) => (x k).bind fun a => f a (n - k))

/-- Shift the tiers up by one: what cost `n` now costs `n + 1`, and nothing is free. Every tier of
`pay x` below `n` is settled without consulting tier `n` of `x`, which is what makes a recursive
enumeration productive. -/
def pay (x : Enumerate α) : Enumerate α := fun n =>
  match n with
  | 0 => .empty
  | n + 1 => x n

instance : Monad Enumerate where
  pure := Enumerate.pure
  bind := Enumerate.bind
  map := Enumerate.map

/-- `default` is the bottom element: no tier is defined. -/
instance : Inhabited (Enumerate α) where
  default := fun _ => .undef

instance instPartialOrder : PartialOrder (Enumerate α) :=
  inferInstanceAs (PartialOrder (Nat → Finite α))

instance instCCPO : CCPO (Enumerate α) := inferInstanceAs (CCPO (Nat → Finite α))

instance : MonoBind Enumerate where
  bind_mono_left h _ := Finite.flatten_ofFn_mono fun k => MonoBind.bind_mono_left (h k)
  bind_mono_right h _ := Finite.flatten_ofFn_mono fun _ => MonoBind.bind_mono_right fun a => h a _

/-- Every value of the range is enumerated once, in increasing order, and none of them costs
anything: a `pay` in the generator is the only thing that costs. -/
instance : RandomChoice Enumerate where
  choose lo hi h :=
    ofFinite (.mk (hi - lo + 1) fun i => .up ⟨lo + i.val, by have := i.isLt; omega⟩)

instance : Enum Enumerate where
  pay := Enumerate.pay

instance : MonoEnum Enumerate where
  pay_mono h n := by
    cases n with
    | zero => exact FlatOrder.rel.refl
    | succ n => exact h n

instance : Gen Enumerate where
  instInhabited := inferInstance
  instMonad := inferInstance
  instRandomChoice := inferInstance
  instCCPO := inferInstance
  instMonoBind := inferInstance

end Enumerate

end Basalt
