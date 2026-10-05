/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt.GenRel
import Basalt.Sized

/-!
# Generator Homomorphisms

A `GenHom G H` carries generators at `G` to generators at `H`, preserving what a generator is built
from. Every combinator is then natural in it (`GenHom.map_geometricListOf`, …): the two inequalities
are the combinator's `GenRel` lemma at the relations the homomorphism induces.
-/

open Lean.Order

/-- A `choose`-preserving monad morphism between generator monads that preserves `default` and
fixpoints. `Gen` has no monad laws, so `map_map` is not `map_bind`'s. -/
structure GenHom (G H : Type → Type) [Gen G] [Gen H] where
  map : ∀ {α : Type}, G α → H α
  map_pure : ∀ {α : Type} (a : α), map (Pure.pure a) = Pure.pure a
  map_bind : ∀ {α β : Type} (x : G α) (k : α → G β), map (x >>= k) = map x >>= fun a => map (k a)
  map_map : ∀ {α β : Type} (f : α → β) (x : G α), map (f <$> x) = f <$> map x
  map_default : ∀ {α : Type}, map (default : G α) = default
  map_choose : ∀ (lo hi : Nat) (h : lo ≤ hi),
    map (RandomChoice.choose lo hi h) = RandomChoice.choose lo hi h
  admissible : ∀ {α : Type} (x : H α), admissible fun y : G α => map y ⊑ x

namespace GenHom

attribute [size_erasure] map_pure map_bind map_map map_default map_choose

variable {G H : Type → Type} [Gen G] [Gen H] {α β : Type} (φ : GenHom G H)

@[size_erasure]
theorem map_ite (p : Prop) [Decidable p] (x y : G α) :
    φ.map (if p then x else y) = if p then φ.map x else φ.map y := by
  split <;> rfl

@[size_erasure]
theorem map_dite (p : Prop) [Decidable p] (x : p → G α) (y : ¬p → G α) :
    φ.map (if h : p then x h else y h) = if h : p then φ.map (x h) else φ.map (y h) := by
  split <;> rfl

@[size_erasure]
theorem map_coin (r : Rat) : φ.map (RandomChoice.coin r) = RandomChoice.coin r := by
  simp only [RandomChoice.coin, φ.map_bind, φ.map_choose, φ.map_ite, φ.map_pure]

@[size_erasure]
theorem map_chooseNat (lo hi : Nat) (h : lo ≤ hi) :
    φ.map (chooseNat lo hi h) = chooseNat lo hi h := by
  simp only [chooseNat, φ.map_map, φ.map_choose]

@[size_erasure]
theorem map_chooseInt (lo hi : Int) (h : lo ≤ hi) :
    φ.map (chooseInt lo hi h) = chooseInt lo hi h := by
  simp only [chooseInt, φ.map_bind, φ.map_chooseNat, φ.map_pure]

/-! ## Naturality

`φ.map y ⊑ x` and `x ⊑ φ.map y` are each a `GenRel`, so a combinator's `GenRel` lemma, read at both,
is its naturality. -/

section natural

theorem genRel_le : GenRel G H fun {_} y x => φ.map y ⊑ x where
  pure a := by rw [φ.map_pure]; exact PartialOrder.rel_refl
  bind hk hx := by
    rw [φ.map_bind]
    exact PartialOrder.rel_trans (MonoBind.bind_mono_left hx) (MonoBind.bind_mono_right hk)
  mapChoose lo hi h f := by rw [φ.map_map, φ.map_choose]; exact PartialOrder.rel_refl
  default := by intro α; rw [φ.map_default]; exact PartialOrder.rel_refl
  choose lo hi h := by rw [φ.map_choose]; exact PartialOrder.rel_refl
  admissible := φ.admissible

theorem genRel_ge : GenRel H G fun {_} x y => x ⊑ φ.map y where
  pure a := by rw [φ.map_pure]; exact PartialOrder.rel_refl
  bind hk hx := by
    rw [φ.map_bind]
    exact PartialOrder.rel_trans (MonoBind.bind_mono_left hx) (MonoBind.bind_mono_right hk)
  mapChoose lo hi h f := by rw [φ.map_map, φ.map_choose]; exact PartialOrder.rel_refl
  default := by intro α; rw [φ.map_default]; exact PartialOrder.rel_refl
  choose lo hi h := by rw [φ.map_choose]; exact PartialOrder.rel_refl
  admissible _ := fun _ hc h => csup_le hc h

@[size_erasure]
theorem map_elements (xs : List α) (hne : xs ≠ []) : φ.map (elements xs hne) = elements xs hne :=
  PartialOrder.rel_antisymm (φ.genRel_le.elements xs hne) (φ.genRel_ge.elements xs hne)

@[size_erasure]
theorem map_vectorOf (n : Nat) (g : G α) : φ.map (vectorOf n g) = vectorOf n (φ.map g) :=
  PartialOrder.rel_antisymm (φ.genRel_le.vectorOf n PartialOrder.rel_refl)
    (φ.genRel_ge.vectorOf n PartialOrder.rel_refl)

@[size_erasure]
theorem map_listOfMaxLength (n : Nat) (g : G α) :
    φ.map (listOfMaxLength n g) = listOfMaxLength n (φ.map g) :=
  PartialOrder.rel_antisymm (φ.genRel_le.listOfMaxLength n PartialOrder.rel_refl)
    (φ.genRel_ge.listOfMaxLength n PartialOrder.rel_refl)

@[size_erasure]
theorem map_permutationOf (xs : List α) : φ.map (permutationOf xs) = permutationOf xs :=
  PartialOrder.rel_antisymm (φ.genRel_le.permutationOf xs) (φ.genRel_ge.permutationOf xs)

/-- The branches of `gs`, each carried by `φ`. -/
@[size_erasure]
theorem map_oneOf (gs : List (Unit → G α)) (hne : gs ≠ []) :
    φ.map (oneOf gs hne) = oneOf (gs.map fun g u => φ.map (g u)) (by simpa using hne) :=
  PartialOrder.rel_antisymm
    (φ.genRel_le.oneOf (List.forall₂_map_right_iff.mpr
      (List.forall₂_same.mpr fun _ _ => PartialOrder.rel_refl)))
    (φ.genRel_ge.oneOf (List.forall₂_map_left_iff.mpr
      (List.forall₂_same.mpr fun _ _ => PartialOrder.rel_refl)))

@[size_erasure]
theorem map_oneOfWith (gs : List (Unit → G α)) (hne : gs ≠ []) (impl : G α)
    (h : impl = oneOf gs hne) :
    φ.map (oneOfWith gs hne impl h)
      = oneOf (gs.map fun g u => φ.map (g u)) (by simpa using hne) := by
  rw [oneOfWith_eq, map_oneOf]

/-- The branches of `gs`, each carried by `φ`, at their weights. -/
@[size_erasure]
theorem map_frequency (gs : List (Nat × (Unit → G α))) (h : 0 < (gs.map Prod.fst).sum) :
    φ.map (frequency gs h)
      = frequency (gs.map fun p => (p.1, fun u => φ.map (p.2 u)))
          (by simpa [Function.comp_def] using h) := by
  refine PartialOrder.rel_antisymm (φ.genRel_le.frequency ?_) (φ.genRel_ge.frequency ?_)
  all_goals
    clear h
    induction gs with
    | nil => exact .nil
    | cons p gs ih => exact .cons PartialOrder.rel_refl ih

@[size_erasure]
theorem map_frequencyWith (gs : List (Nat × (Unit → G α))) (h : 0 < (gs.map Prod.fst).sum)
    (impl : G α) (he : impl = frequency gs h) :
    φ.map (frequencyWith gs h impl he)
      = frequency (gs.map fun p => (p.1, fun u => φ.map (p.2 u)))
          (by simpa [Function.comp_def] using h) := by
  rw [frequencyWith_eq, map_frequency]

-- A literal list of branches is carried entry by entry.
attribute [size_erasure] List.map_cons List.map_nil

@[size_erasure]
theorem map_geometricListOf (g : G α) : φ.map (geometricListOf g) = geometricListOf (φ.map g) :=
  PartialOrder.rel_antisymm (φ.genRel_le.geometricListOf PartialOrder.rel_refl)
    (φ.genRel_ge.geometricListOf PartialOrder.rel_refl)

@[size_erasure]
theorem map_nonEmptyListOf (g : G α) : φ.map (nonEmptyListOf g) = nonEmptyListOf (φ.map g) :=
  PartialOrder.rel_antisymm (φ.genRel_le.nonEmptyListOf PartialOrder.rel_refl)
    (φ.genRel_ge.nonEmptyListOf PartialOrder.rel_refl)

@[size_erasure]
theorem map_rejectUntil (g : G α) (p : α → Bool) :
    φ.map (rejectUntil g p) = rejectUntil (φ.map g) p :=
  PartialOrder.rel_antisymm (φ.genRel_le.rejectUntil p PartialOrder.rel_refl)
    (φ.genRel_ge.rejectUntil p PartialOrder.rel_refl)


@[size_erasure]
theorem map_sublistOf (xs : List α) : φ.map (sublistOf xs) = sublistOf xs :=
  PartialOrder.rel_antisymm (φ.genRel_le.sublistOf xs) (φ.genRel_ge.sublistOf xs)

@[size_erasure]
theorem map_shuffle (xs : List α) : φ.map (shuffle xs) = shuffle xs :=
  PartialOrder.rel_antisymm (φ.genRel_le.shuffle xs) (φ.genRel_ge.shuffle xs)

/-- The family `gs`, carried by `φ` at each size. -/
@[size_erasure]
theorem map_trySizes (gs : Nat → G α) (f : α → Option β) (m k : Nat) :
    φ.map (trySizes gs f m k) = trySizes (fun j => φ.map (gs j)) f m k :=
  PartialOrder.rel_antisymm (φ.genRel_le.trySizes f m k fun _ => PartialOrder.rel_refl)
    (φ.genRel_ge.trySizes f m k fun _ => PartialOrder.rel_refl)

@[size_erasure, inherit_doc map_trySizes]
theorem map_suchThatFrom (gs : Nat → G α) (f : α → Option β) (n : Nat) :
    φ.map (suchThatFrom gs f n) = suchThatFrom (fun j => φ.map (gs j)) f n :=
  PartialOrder.rel_antisymm (φ.genRel_le.suchThatFrom f n fun _ => PartialOrder.rel_refl)
    (φ.genRel_ge.suchThatFrom f n fun _ => PartialOrder.rel_refl)

end natural

end GenHom
