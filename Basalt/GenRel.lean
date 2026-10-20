/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
module

public import Mathlib.Data.List.Forall2
public import Basalt.Combinators
public import Basalt.GenRel.Basic
public import Basalt.Walk.Attr

/-!
# One Generator at Two Monads

Every combinator relates itself at two monads under any relation that is a `GenRel`
(`Basalt/GenRel/Basic.lean`), proved once for every such relation (`GenRel.listOf`, …). These and
the host constructs, `GenRel`'s fields and a conditional, are the `@[gen_rel_rule]`s, which the
walker applies to each relation's `@[walk_rel]` proof.
-/

@[expose] public section

open Lean.Order

section weighted

variable {M N : Type → Type} {α : Type} {R : ∀ {α : Type}, M α → N α → Prop}

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

end weighted

namespace GenRel

variable {M N : Type → Type} [Gen M] [Gen N] {α : Type} {R : ∀ {α : Type}, M α → N α → Prop}
  (h : GenRel M N @R)
include h

/-! ## The host constructs

A `GenRel`'s fields relate the host constructs other than a conditional, and a draw. -/

attribute [gen_rel_rule] GenRel.pure GenRel.bind GenRel.map GenRel.default GenRel.choose

omit h in
/-- A conditional needs nothing of its `GenRel`: both sides take the same branch. -/
@[gen_rel_rule]
theorem ite (_ : GenRel M N @R) {p : Prop} [Decidable p] {y₁ y₂ : M α} {x₁ x₂ : N α}
    (h₁ : p → R y₁ x₁) (h₂ : ¬p → R y₂ x₂) :
    R (if p then y₁ else y₂) (if p then x₁ else x₂) := by
  split
  · exact h₁ ‹_›
  · exact h₂ ‹_›

omit h in
@[gen_rel_rule, inherit_doc ite]
theorem dite (_ : GenRel M N @R) {p : Prop} [Decidable p] {y₁ : p → M α} {y₂ : ¬p → M α}
    {x₁ : p → N α} {x₂ : ¬p → N α} (h₁ : ∀ h, R (y₁ h) (x₁ h)) (h₂ : ∀ h, R (y₂ h) (x₂ h)) :
    R (if h : p then y₁ h else y₂ h) (if h : p then x₁ h else x₂ h) := by
  split
  · exact h₁ _
  · exact h₂ _

/-! ## The combinators -/

@[gen_rel_rule]
theorem elements (xs : List α) (hne : xs ≠ []) : R (elements xs hne) (elements xs hne) := by
  unfold _root_.elements
  exact h.bind (fun ⟨_, _, _⟩ => h.pure _) (h.map _ (h.choose _ _ _))

@[gen_rel_rule]
theorem vectorOf {g' : M α} {g : N α} (n : Nat) (hg : R g' g) :
    R (vectorOf n g') (vectorOf n g) := by
  induction n with
  | zero => exact h.pure []
  | succ n ih =>
    rw [vectorOf_succ, vectorOf_succ]
    exact h.bind (fun _ => h.bind (fun _ => h.pure _) ih) hg

theorem oneOfChain {gs' : List (Unit → M α)} {gs : List (Unit → N α)}
    (hs : List.Forall₂ (fun g' g => R (g' ()) (g ())) gs' gs) (k i : Nat) :
    R (oneOfChain gs' k i) (oneOfChain gs k i) := by
  induction hs generalizing k with
  | nil => exact h.default _
  | cons hg hs ih =>
    cases hs with
    | nil => exact hg
    | cons =>
      rw [_root_.oneOfChain.eq_3 _ _ _ _ (List.cons_ne_nil _ _),
        _root_.oneOfChain.eq_3 _ _ _ _ (List.cons_ne_nil _ _)]
      exact h.ite (fun _ => hg) fun _ => ih _

@[gen_rel_rule]
theorem oneOf {gs' : List (Unit → M α)} {gs : List (Unit → N α)} {hne' : gs' ≠ []} {hne : gs ≠ []}
    (hs : List.Forall₂ (fun g' g => R (g' ()) (g ())) gs' gs) :
    R (oneOf gs' hne') (oneOf gs hne) := by
  rw [oneOf_eq_chain gs' hne' (gs.length - 1) (by rw [hs.length_eq]), oneOf_eq_chain gs hne _ rfl]
  exact h.bind (fun _ => h.oneOfChain hs 0 _) (h.choose _ _ _)

@[gen_rel_rule]
theorem listOf {g' : M α} {g : N α} (hg : R g' g) : R (listOf g') (listOf g) := by
  refine _root_.listOf.fixpoint_induct (G := M) g' (fun y => R y (_root_.listOf g))
    (h.admissible _) fun z ih => ?_
  rw [_root_.listOf]
  simp only [oneOfWith_eq]
  exact h.oneOf (.cons (h.pure _)
    (.cons (h.bind (fun _ => h.bind (fun _ => h.pure _) ih) hg) .nil))

@[gen_rel_rule]
theorem nonEmptyListOf {g' : M α} {g : N α} (hg : R g' g) :
    R (nonEmptyListOf g') (nonEmptyListOf g) := by
  refine _root_.nonEmptyListOf.fixpoint_induct (G := M) g' (fun y => R y (_root_.nonEmptyListOf g))
    (h.admissible _) fun z ih => ?_
  rw [_root_.nonEmptyListOf]
  simp only [oneOfWith_eq]
  exact h.oneOf (.cons (h.bind (fun _ => h.pure _) hg)
    (.cons (h.bind (fun _ => h.bind (fun _ => h.pure _) ih) hg) .nil))

@[gen_rel_rule]
theorem suchThat {g' : M α} {g : N α} (p : α → Bool) (hg : R g' g) :
    R (suchThat g' p) (suchThat g p) := by
  refine _root_.suchThat.fixpoint_induct (G := M) g' p (fun y => R y (_root_.suchThat g p))
    (h.admissible _) fun z ih => ?_
  rw [_root_.suchThat]
  exact h.bind (fun a => h.ite (fun _ => h.pure a) fun _ => ih) hg

@[gen_rel_rule]
theorem permutationOf (xs : List α) : R (permutationOf xs) (permutationOf xs) := by
  induction xs with
  | nil => exact h.pure _
  | cons x xs ih =>
    unfold _root_.permutationOf
    exact h.bind (fun ⟨_, _⟩ => h.bind (fun ⟨_, _, _⟩ => h.pure _)
      (h.map _ (h.choose _ _ _))) ih

theorem frequencyChain {gs' : List (Nat × (Unit → M α))} {gs : List (Nat × (Unit → N α))}
    (hs : Weighted @R gs' gs) (acc n : Nat) :
    R (frequencyChain gs' acc n) (frequencyChain gs acc n) := by
  induction hs generalizing acc with
  | nil => exact h.default _
  | cons hg _ ih => exact h.ite (fun _ => hg) fun _ => ih _

@[gen_rel_rule]
theorem frequency {gs' : List (Nat × (Unit → M α))} {gs : List (Nat × (Unit → N α))}
    {h' : 0 < (gs'.map Prod.fst).sum} {hw : 0 < (gs.map Prod.fst).sum}
    (hs : Weighted @R gs' gs) : R (frequency gs' h') (frequency gs hw) := by
  rw [frequency_eq_chain gs' h' ((gs.map Prod.fst).sum - 1) (by rw [hs.weights]),
    frequency_eq_chain gs hw _ rfl]
  unfold chooseNat
  exact h.bind (fun _ => h.frequencyChain hs 0 _) (h.map _ (h.choose _ _ _))

end GenRel
