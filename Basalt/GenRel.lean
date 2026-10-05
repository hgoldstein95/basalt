/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Mathlib.Data.List.Forall2
import Basalt.Combinators
import Basalt.Walk.Attr

/-!
# One Generator at Two Monads

`GenRel M N R` says the relation `R` between generators at `M` and at `N` is closed under the host
constructs, a draw, `default`, and fixpoint induction on the `M` side. Every combinator then
relates itself at the two monads (`GenRel.geometricListOf`, …), proved once for every such `R`: a
relational judgment's rules are instances of these.
-/

open Lean.Order

section host

variable {M N : Type → Type} {α : Type} {R : ∀ {α : Type}, M α → N α → Prop}

/-- A conditional needs nothing of `R`: both sides take the same branch. -/
theorem GenRel.ite {p : Prop} [Decidable p] {y₁ y₂ : M α} {x₁ x₂ : N α}
    (h₁ : p → R y₁ x₁) (h₂ : ¬p → R y₂ x₂) :
    R (if p then y₁ else y₂) (if p then x₁ else x₂) := by
  split
  · exact h₁ ‹_›
  · exact h₂ ‹_›

theorem GenRel.dite {p : Prop} [Decidable p] {y₁ : p → M α} {y₂ : ¬p → M α}
    {x₁ : p → N α} {x₂ : ¬p → N α} (h₁ : ∀ h, R (y₁ h) (x₁ h)) (h₂ : ∀ h, R (y₂ h) (x₂ h)) :
    R (if h : p then y₁ h else y₂ h) (if h : p then x₁ h else x₂ h) := by
  split
  · exact h₁ _
  · exact h₂ _

/-- The branches of `frequency` at the two monads, weight for weight, each pair related. -/
@[gen_branches]
inductive GenRel.Weighted (R : ∀ {α : Type}, M α → N α → Prop) :
    List (Nat × (Unit → M α)) → List (Nat × (Unit → N α)) → Prop
  | nil : Weighted @R [] []
  | cons {w : Nat} {g' : Unit → M α} {g : Unit → N α} {gs' gs} (h : R (g' ()) (g ()))
      (hs : Weighted @R gs' gs) : Weighted @R ((w, g') :: gs') ((w, g) :: gs)

theorem GenRel.Weighted.weights {gs' : List (Nat × (Unit → M α))}
    {gs : List (Nat × (Unit → N α))} (hs : Weighted @R gs' gs) :
    gs'.map Prod.fst = gs.map Prod.fst := by
  induction hs with
  | nil => rfl
  | cons _ _ ih => simp [ih]

end host

/-- `R` relates one generator at `M` and at `N` construct by construct. `admissible` is what
fixpoint induction on the `M` side asks, for a recursive combinator. -/
structure GenRel (M N : Type → Type) [Gen M] [Gen N] (R : ∀ {α : Type}, M α → N α → Prop) :
    Prop where
  pure : ∀ {α : Type} (a : α), R (Pure.pure a) (Pure.pure a)
  bind : ∀ {α β : Type} {y : M α} {x : N α} {k' : α → M β} {k : α → N β},
    (∀ a, R (k' a) (k a)) → R y x → R (y >>= k') (x >>= k)
  mapChoose : ∀ {β : Type} (lo hi : Nat) (h : lo ≤ hi)
    (f : ULift {x : Nat // lo ≤ x ∧ x ≤ hi} → β),
    R (f <$> RandomChoice.choose lo hi h) (f <$> RandomChoice.choose lo hi h)
  default : ∀ {α : Type}, R (Inhabited.default : M α) Inhabited.default
  choose : ∀ (lo hi : Nat) (h : lo ≤ hi),
    R (RandomChoice.choose lo hi h) (RandomChoice.choose lo hi h)
  admissible : ∀ {α : Type} (x : N α), Lean.Order.admissible fun y : M α => R y x

namespace GenRel

variable {M N : Type → Type} [Gen M] [Gen N] {α : Type} {R : ∀ {α : Type}, M α → N α → Prop}
  (h : GenRel M N @R)
include h

theorem chooseNat (lo hi : Nat) (hle : lo ≤ hi) : R (chooseNat lo hi hle) (chooseNat lo hi hle) :=
  h.mapChoose _ _ _ _

theorem elements (xs : List α) (hne : xs ≠ []) : R (elements xs hne) (elements xs hne) := by
  unfold _root_.elements
  exact h.bind (fun ⟨_, _, _⟩ => h.pure _) (h.mapChoose _ _ _ _)

theorem vectorOf {g' : M α} {g : N α} (n : Nat) (hg : R g' g) :
    R (vectorOf n g') (vectorOf n g) := by
  induction n with
  | zero => exact h.pure []
  | succ n ih =>
    rw [vectorOf_succ, vectorOf_succ]
    exact h.bind (fun _ => h.bind (fun _ => h.pure _) ih) hg

theorem listOfMaxLength {g' : M α} {g : N α} (n : Nat) (hg : R g' g) :
    R (listOfMaxLength n g') (listOfMaxLength n g) := by
  unfold _root_.listOfMaxLength
  exact h.bind (fun ⟨k, _⟩ => h.vectorOf k hg) (h.mapChoose _ _ _ _)

theorem oneOfChain {gs' : List (Unit → M α)} {gs : List (Unit → N α)}
    (hs : List.Forall₂ (fun g' g => R (g' ()) (g ())) gs' gs) (k i : Nat) :
    R (oneOfChain gs' k i) (oneOfChain gs k i) := by
  induction hs generalizing k with
  | nil => exact h.default
  | cons hg hs ih =>
    cases hs with
    | nil => exact hg
    | cons =>
      rw [_root_.oneOfChain.eq_3 _ _ _ _ (List.cons_ne_nil _ _),
        _root_.oneOfChain.eq_3 _ _ _ _ (List.cons_ne_nil _ _)]
      exact GenRel.ite (fun _ => hg) fun _ => ih _

theorem oneOf {gs' : List (Unit → M α)} {gs : List (Unit → N α)} {hne' : gs' ≠ []} {hne : gs ≠ []}
    (hs : List.Forall₂ (fun g' g => R (g' ()) (g ())) gs' gs) :
    R (oneOf gs' hne') (oneOf gs hne) := by
  rw [oneOf_eq_chain gs' hne' (gs.length - 1) (by rw [hs.length_eq]), oneOf_eq_chain gs hne _ rfl]
  exact h.bind (fun _ => h.oneOfChain hs 0 _) (h.choose _ _ _)

theorem geometricListOf {g' : M α} {g : N α} (hg : R g' g) :
    R (geometricListOf g') (geometricListOf g) := by
  refine _root_.geometricListOf.fixpoint_induct (G := M) g'
    (fun y => R y (_root_.geometricListOf g))
    (h.admissible _) fun z ih => ?_
  rw [_root_.geometricListOf]
  simp only [oneOfWith_eq]
  exact h.oneOf (.cons (h.pure _)
    (.cons (h.bind (fun _ => h.bind (fun _ => h.pure _) ih) hg) .nil))

theorem nonEmptyListOf {g' : M α} {g : N α} (hg : R g' g) :
    R (nonEmptyListOf g') (nonEmptyListOf g) := by
  refine _root_.nonEmptyListOf.fixpoint_induct (G := M) g' (fun y => R y (_root_.nonEmptyListOf g))
    (h.admissible _) fun z ih => ?_
  rw [_root_.nonEmptyListOf]
  simp only [oneOfWith_eq]
  exact h.oneOf (.cons (h.bind (fun _ => h.pure _) hg)
    (.cons (h.bind (fun _ => h.bind (fun _ => h.pure _) ih) hg) .nil))

theorem rejectUntil {g' : M α} {g : N α} (p : α → Bool) (hg : R g' g) :
    R (rejectUntil g' p) (rejectUntil g p) := by
  refine _root_.rejectUntil.fixpoint_induct (G := M) g' p (fun y => R y (_root_.rejectUntil g p))
    (h.admissible _) fun z ih => ?_
  rw [_root_.rejectUntil]
  exact h.bind (fun a => GenRel.ite (R := @R) (fun _ => h.pure a) fun _ => ih) hg

theorem permutationOf (xs : List α) : R (permutationOf xs) (permutationOf xs) := by
  induction xs with
  | nil => exact h.pure _
  | cons x xs ih =>
    unfold _root_.permutationOf
    exact h.bind (fun ⟨_, _⟩ => h.bind (fun ⟨_, _, _⟩ => h.pure _)
      (h.mapChoose _ _ _ _)) ih

theorem frequencyChain {gs' : List (Nat × (Unit → M α))} {gs : List (Nat × (Unit → N α))}
    (hs : Weighted @R gs' gs) (acc n : Nat) :
    R (frequencyChain gs' acc n) (frequencyChain gs acc n) := by
  induction hs generalizing acc with
  | nil => exact h.default
  | cons hg _ ih => exact GenRel.ite (fun _ => hg) fun _ => ih _

theorem frequency {gs' : List (Nat × (Unit → M α))} {gs : List (Nat × (Unit → N α))}
    {h' : 0 < (gs'.map Prod.fst).sum} {hw : 0 < (gs.map Prod.fst).sum}
    (hs : Weighted @R gs' gs) : R (frequency gs' h') (frequency gs hw) := by
  rw [frequency_eq_chain gs' h' ((gs.map Prod.fst).sum - 1) (by rw [hs.weights]),
    frequency_eq_chain gs hw _ rfl]
  exact h.bind (fun _ => h.frequencyChain hs 0 _) (h.chooseNat _ _ _)

theorem sublistOf (xs : List α) : R (_root_.sublistOf xs) (_root_.sublistOf xs) := by
  induction xs with
  | nil => exact h.pure []
  | cons x xs ih =>
    unfold _root_.sublistOf
    exact h.bind (fun _ => h.bind (fun _ => h.pure _) ih) (h.chooseNat _ _ _)

theorem shuffle (xs : List α) : R (_root_.shuffle xs) (_root_.shuffle xs) :=
  h.bind (fun _ => h.pure _) (h.vectorOf _ (h.chooseNat _ _ _))

theorem trySizes {β : Type} {gs' : Nat → M α} {gs : Nat → N α} (f : α → Option β) (m k : Nat)
    (hgs : ∀ j, R (gs' j) (gs j)) :
    R (_root_.trySizes gs' f m k) (_root_.trySizes gs f m k) := by
  induction k generalizing m with
  | zero => exact h.pure none
  | succ k ih =>
    exact h.bind (fun _ => GenRel.ite (R := @R) (fun _ => h.pure _) fun _ => ih _) (hgs m)

theorem suchThatFrom {β : Type} {gs' : Nat → M α} {gs : Nat → N α} (f : α → Option β) (n : Nat)
    (hgs : ∀ j, R (gs' j) (gs j)) :
    R (_root_.suchThatFrom gs' f n) (_root_.suchThatFrom gs f n) := by
  refine _root_.suchThatFrom.fixpoint_induct (G := M) gs' f
    (fun z => ∀ n, R (z n) (_root_.suchThatFrom gs f n))
    (admissible_pi_apply (fun n y => R y (_root_.suchThatFrom gs f n)) fun n =>
      h.admissible _) (fun z ih n => ?_) n
  rw [_root_.suchThatFrom]
  refine h.bind (fun o => ?_) (h.trySizes f n (n + 1) hgs)
  cases o with
  | none => exact ih _
  | some b => exact h.pure b

end GenRel
