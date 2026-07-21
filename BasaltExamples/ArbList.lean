/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt
import BasaltExamples.ArbNat

open RandomChoice ArbNat

/-!
# Arbitrary Lists

`List.arbitrary` generates an arbitrary `List Nat` with the same subcritical shape as `ArbNat`: flip
a coin to stop, otherwise draw a `Nat.arbitrary` head and recurse for the tail. A second definition,
`List.arbitrary'`, generates the same distribution via the `vectorOf` combinator (choose a length,
then fill it); it is exercised in `BasaltTest/IO.lean`, but the laws below are all stated about
`List.arbitrary`.
-/

namespace ArbList

/-- Generates an arbitrary `List Nat`: flip a coin to stop with `[]`, or draw a head and recurse. -/
def List.arbitrary [Gen G] : G (List Nat) := do
  pick
    (fun () => pure [])
    (fun () => do
      let x ← Nat.arbitrary
      let xs ← List.arbitrary
      return x :: xs)
partial_fixpoint

/-- A variant of `List.arbitrary` using the `vectorOf` combinator: choose a length `n` at random,
then generate a length-`n` list of `Nat`s. Same distribution; the proofs target `List.arbitrary`. -/
def List.arbitrary' [Gen G] : G (List Nat) := do
  let n ← Nat.arbitrary
  vectorOf n Nat.arbitrary

theorem List.arbitrary.sound_complete : IsSoundAndComplete List.arbitrary ⊤ := by
  intro xs
  simp only [Pi.top_apply]
  induction xs <;> rw [List.arbitrary]
  case _ => simp
  case _ x xs ih => simp [ih, Nat.arbitrary_mem_support]

theorem List.arbitrary.terminates : IsAlmostSurelyTerminating List.arbitrary := by
  -- Static seed, mean offspring 1/2: subcritical.
  refine SPMF.IsPMF_of_subcritical_mass (m := 1 / 2) (by norm_num) ?_
  conv_rhs => rw [List.arbitrary]
  simp only [SPMF.mass_pick, SPMF.mass_pure, mul_one]
  gcongr
  · simp_all
  · apply SPMF.mass_bind_ge_of_isPMF Nat.arbitrary.terminates
    intro x
    rw [SPMF.mass_bind_pure]

/-- Producing `xs` costs at most `2 * xs.length + xs.sum + 1` choices: one `pick` and one
`Nat.arbitrary` (bounded by the element plus one) per cons cell, plus the final `pick`. -/
theorem List.arbitrary.cost_bounded :
    IsCostBounded List.arbitrary (fun xs => 2 * xs.length + xs.sum + 1) := by
  open Lean.Order in
  delta arbitrary
  apply fix_induct (motive := fun (g : SPMF.Cost (List Nat)) =>
    IsBounded g (fun xs => 2 * xs.length + xs.sum + 1)) _ ?admissible ?step
  case admissible =>
    apply admissible_IsBounded
  case step =>
    intro arbitrary_rec ih
    rw [IsBounded_iff]
    rintro ⟨xs, c⟩ hmem
    cost_support_simp at hmem
    obtain ⟨m, rfl, h | h⟩ := hmem
    · obtain ⟨rfl, rfl⟩ := h
      simp
    · obtain ⟨x, n1, n2, hx, ⟨tl, n3, n4, htl, ⟨rfl, hn4⟩, hn2⟩, hm⟩ := h
      have hhead : n1 ≤ x + 1 := IsBounded_iff.mp Nat.arbitrary.cost_bounded (x, n1) hx
      have htail : n3 ≤ 2 * tl.length + tl.sum + 1 := ih (tl, n3) htl
      show 1 + m ≤ 2 * (x :: tl).length + (x :: tl).sum + 1
      simp only [List.length_cons, List.sum_cons]
      omega

end ArbList
