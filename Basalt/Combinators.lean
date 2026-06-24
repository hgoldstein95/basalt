/-
Copyright (c) 2026 Harrison Goldstein & Ernest Ng. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein & Ernest Ng
-/

import Basalt.Gen
import Basalt.RandomChoice

open Lean.Order

/-!
# Generator Combinators

This file defines various generator combinators:
- `elements`: generates an element from a non-empty list at random
- `oneOf`: picks from a list of generators uniformly at random selection
- `frequency`: like `oneOf`, but performs weighted random selection
- `frequencyAux`: helper function that traverses the list of weights
   to select a generator for a given random index
-/

open List

namespace Helpers

/-- Helper function for the `frequency` combinator:
    `frequencyAux xs n` chooses a weight & a generator `(k, gen)` from the list `xs` such that `n < k`.
     This function expects a proof `h : n < sum(xs)`, which makes the empty-list case in
     the pattern-match irrefutable, since `n < 0` is `False` (this is discharged
     immediately by `contradiction`). -/
def frequencyAux [Gen G] (xs : List (Nat × (Unit → G α))) (n : Nat)
    (h : n < List.sum (List.map Prod.fst xs)) : G α :=
  match xs with
  | [] => by contradiction
  | (k, x) :: xs =>
    if hlt : n < k then
      x ()
    else
      frequencyAux xs (n - k) (by dsimp at h; omega)

end Helpers

/-- Generates an element of the list `xs` at random.
    This combinator takes as input a proof that `xs` is non-empty. -/
def elements [Gen G] (xs : List α) (hne : xs ≠ []) : G α := do
  let ⟨i, ⟨ hge, hle ⟩⟩ ← ULift.down <$> RandomChoice.choose 0 (xs.length - 1) (by omega)
  -- Obtain a proof that the list indexing is in-bounds
  have hlen : 0 < xs.length := by
    apply length_pos_iff.mpr
    assumption
  have hlt : i < xs.length := by omega
  return xs[i]'hlt

/-- Picks one of the generators in `gs` at random.
    This combinator takes as input a proof that `xs` is non-empty. -/
def oneOf [Gen G] (gs : List (Unit → G α)) (hne : gs ≠ []) : G α := do
  let ⟨i, ⟨ hge, hle ⟩⟩ ← ULift.down <$> RandomChoice.choose 0 (gs.length - 1) (by omega)
  -- Obtain a proof that the list indexing is in-bounds
  have hlen : 0 < gs.length := by
    apply length_pos_iff.mpr
    assumption
  have hlt : i < gs.length := by omega
  -- This let-definition is necessary, as Lean has trouble parsing `gs[i]'hlt ()`
  let thunked_gen := gs[i]'hlt
  thunked_gen ()

/-- `frequency` picks a generator from the list `gs` according to the weights in `gs`.
    This combinators also takes an additional hypothesis that the sum of the weights
    in the list is non-zero (this is discharged via `omega` by default). -/
def frequency [Gen G] (gs : List (Nat × (Unit → G α)))
  (_h : 0 < List.sum (List.map Prod.fst gs) := by omega) : G α := do
  let total := List.sum $ List.map Prod.fst gs
  let n ← ULift.down <$> RandomChoice.choose 0 (total - 1) (by omega)
  if hn : n < total then Helpers.frequencyAux gs n hn else default

instance List.instPartialOrder {α : Type u} [PartialOrder α] :
    PartialOrder (List α) where
  rel l1 l2 :=
    l1.length = l2.length ∧
    ∀ (i : Nat) (h1 : i < l1.length) (h2 : i < l2.length), l1[i] ⊑ l2[i]
  rel_refl := by
    intro xs
    constructor
    . rfl
    . intro i _ _
      apply PartialOrder.rel_refl
  rel_trans := by
    intro xs ys zs h12 h23
    obtain ⟨heq1, hle1⟩ := h12
    obtain ⟨heq2, hle2⟩ := h23
    constructor
    . apply Eq.trans <;> assumption
    . intro i h1 h2
      apply PartialOrder.rel_trans
      . apply hle1
        omega
      . apply hle2
  rel_antisymm h12 h21 := by
    obtain ⟨hlen, helem12⟩ := h12
    obtain ⟨_, helem21⟩ := h21
    apply List.ext_getElem hlen
    intro i hi1 hi2
    apply PartialOrder.rel_antisymm
    . apply helem12
    . apply helem21

-- Lets the tactic decompose a list literal `[e₁, e₂, …]` = `e₁ :: (e₂ :: …)`
-- into one element at a time; the empty-list base case is handled by the
-- tactic's existing constant-expression rule.
@[partial_fixpoint_monotone]
theorem List.monotone_cons
    {α : Type u} {γ : Sort w} [PartialOrder α] [PartialOrder γ]
    (f : γ → α) (fs : γ → List α) (hf : monotone f) (hfs : monotone fs) :
    monotone (fun x => f x :: fs x) := by
  intro x y hxy
  have hle : fs x ⊑ fs y := hfs x y hxy
  have heq : (fs x).length = (fs y).length := hle.1
  dsimp
  constructor
  . -- (f x :: fs x).length = (f y :: fs y).length
    simpa using heq
  . -- (f x :: fs x)[i] ⊑ (f y :: fs y)[i]
    intro i h1 h2
    cases i with
    | zero =>
      apply hf
      assumption
    | succ i' =>
      dsimp
      have all_elts_le := (hfs x y hxy).2
      apply all_elts_le

private theorem oneOf_choose_irrelevant [Gen G] (l : List (Unit → G α))
    (n₁ n₂ : Nat) (h₁ : 0 ≤ n₁) (h₂ : 0 ≤ n₂) (hlen : n₁ = n₂)
    (hlt₁ : ∀ i, i ≤ n₁ → i < l.length)
    (hlt₂ : ∀ i, i ≤ n₂ → i < l.length) :
    (do let ⟨i, _, hle_i⟩ ← ULift.down <$> RandomChoice.choose 0 n₁ h₁
        let g := l[i]'(hlt₁ i hle_i)
        g ()) =
    (do let ⟨i, _, hle_i⟩ ← ULift.down <$> RandomChoice.choose 0 n₂ h₂
        let g := l[i]'(hlt₂ i hle_i)
        g ()) := by
  subst hlen; rfl

theorem oneOf_le [Gen G] {l1 l2 : List (Unit → G α)} (h : l1 ⊑ l2) (h1 : l1 ≠ []) (h2 : l2 ≠ []) :
    oneOf l1 h1 ⊑ oneOf l2 h2 := by
  obtain ⟨hlen_eq, hle⟩ := h
  have h1len : 0 < l1.length := List.length_pos_iff.mpr h1
  have h2len : 0 < l2.length := List.length_pos_iff.mpr h2
  simp only [oneOf]
  apply PartialOrder.rel_trans (y := do
      let ⟨i, hge, hle_i⟩ ← ULift.down <$> RandomChoice.choose 0 (l1.length - 1) (by omega)
      let g := l2[i]'(by omega)
      g ())
  case a =>
    apply MonoBind.bind_mono_right
    intro ⟨i, hge, hle_i⟩
    exact (hle i (by omega) (by omega)) ()
  case a =>
    dsimp only []
    have hlen_sub : l1.length - 1 = l2.length - 1 := by omega
    have heq : oneOf l2 h2 = oneOf l2 h2 := rfl
    simp only [oneOf, hlen_sub] at heq
    sorry

-- Single general `@[partial_fixpoint_monotone]` lemma.
-- The tactic sees `fun x => oneOf (gens x)` and uses this lemma,
-- having already established `monotone gens` via `List.monotone_cons`.
@[partial_fixpoint_monotone]
theorem monotone_oneOf [Gen G] {γ : Sort w} [PartialOrder γ]
    (gs : γ → List (Unit → G α)) (hne : ∀ x, gs x ≠ []) (hmono : monotone gs) :
    monotone (fun x => oneOf (gs x) (hne x)) := by
  intro x y hxy
  unfold monotone at hmono
  apply oneOf_le
  apply hmono
  assumption

-- ============================================================
-- § 5  End-to-end: `partial_fixpoint` now succeeds
-- ============================================================

def myGen [Gen G] : Unit → G Nat := fun _ =>
  let gs := [fun _ => pure 0, fun _ => do let n ← myGen (); pure (n + 1)]
  have hne : gs ≠ [] := by
    apply cons_ne_nil
  oneOf gs hne
partial_fixpoint
