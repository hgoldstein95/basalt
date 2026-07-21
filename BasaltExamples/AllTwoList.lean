/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt

open RandomChoice

/-!
# Lists of All Twos

The minimal recursive generator: `genAllTwos` produces lists whose every element is `2`. Because the
element is fixed, this isolates the list-shape recursion (a subcritical branching process) from any
element generation, making it the simplest place to see the support / termination / cost recipe.
-/

namespace AllTwoList

/-- The validity predicate: every element of the list is `2`. -/
def AllTwos (l : List Nat) : Prop := ∀ x ∈ l, x = 2

/-- The cost bound: one random choice per element, plus the final choice that ends the list. -/
def AllTwos.cost (l : List Nat) : Nat := l.length + 1

/-- Generates a list of all `2`s: flip a coin to stop with `[]`, or prepend a `2` and recurse. -/
def genAllTwos [Gen G] : G (List Nat) :=
  pick
    (fun () => pure [])
    (fun () => do
      let xs ← genAllTwos
      return 2 :: xs)
partial_fixpoint

theorem genAllTwos.sound_complete : IsSoundAndComplete genAllTwos AllTwos := by
  intro a
  induction a with
  | nil =>
    rw [genAllTwos]
    simp [AllTwos]
  | cons x xs ih =>
    rw [genAllTwos]
    simp [ih, AllTwos, and_comm]

theorem genAllTwos.terminates : IsAlmostSurelyTerminating genAllTwos := by
  -- Static seed, mean offspring 1/2: subcritical.
  refine SPMF.IsPMF_of_subcritical_mass (m := 1 / 2) (by norm_num) ?_
  conv_rhs => rw [genAllTwos]
  simp

theorem genAllTwos.cost_bounded : IsCostBounded genAllTwos AllTwos.cost := by
  open Lean.Order in
  delta genAllTwos
  apply fix_induct (motive := fun (g : SPMF.Cost (List Nat)) =>
    IsBounded g AllTwos.cost) _ ?admissible ?step
  case admissible =>
    apply admissible_IsBounded
  case step =>
    intro genAllTwos_rec ih
    rw [IsBounded_iff]
    rintro ⟨xs, c⟩ hmem
    cost_support_simp at hmem
    obtain ⟨m, rfl, h | h⟩ := hmem
    · obtain ⟨rfl, rfl⟩ := h
      simp [AllTwos.cost]
    · obtain ⟨tl, n1, n2, htl, ⟨rfl, hn2⟩, hm⟩ := h
      have h1 : n1 ≤ AllTwos.cost tl := ih (tl, n1) htl
      show 1 + m ≤ AllTwos.cost (2 :: tl)
      simp only [AllTwos.cost, List.length_cons] at *
      omega

end AllTwoList
