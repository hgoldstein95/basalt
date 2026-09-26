/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt
import BasaltExamples.ArbNat

/-!
# Arbitrary Lists

`List.arbitrary` generates an arbitrary `List Nat` with the same subcritical shape as `ArbNat`: flip
a coin to stop, otherwise draw a `Nat.arbitrary` head and recurse for the tail. A second definition,
`List.arbitrary'`, generates the same distribution via the `vectorOf` combinator (choose a length,
then fill it); it is exercised in `BasaltTest/IO.lean`, but the laws below are all stated about
`List.arbitrary`.
-/

open RandomChoice ArbNat

namespace ArbList

/-- Generates an arbitrary `List Nat`: flip a coin to stop with `[]`, or draw a head and recurse. -/
def List.arbitrary [Gen G] : G (List Nat) := do
  oneOf! [
    fun _ => pure [],
    fun _ => do
      let x ← Nat.arbitrary
      let xs ← List.arbitrary
      return x :: xs]
partial_fixpoint

/-- A variant of `List.arbitrary` using the `vectorOf` combinator: choose a length `n` at random,
then generate a length-`n` list of `Nat`s. Same distribution; the support and cost proofs target
`List.arbitrary`. -/
def List.arbitrary' [Gen G] : G (List Nat) := do
  let n ← Nat.arbitrary
  vectorOf n Nat.arbitrary

theorem List.arbitrary.sound_complete : IsSoundAndComplete List.arbitrary ⊤ := by
  refine .intro (fun _ _ => trivial) ?complete
  intro xs
  induction xs with
  | nil => intro _; rw [List.arbitrary]; complete_bound
  | cons x xs ih =>
    intro _
    rw [List.arbitrary]; complete_bound [Nat.arbitrary.sound_complete]
    exact ⟨x, xs, ih trivial, rfl⟩

theorem List.arbitrary.terminates : IsAlmostSurelyTerminating List.arbitrary := by
  mass_fixpoint [Nat.arbitrary.terminates] using SPMF.LfpIsOne.affine (m := 1 / 2) (by norm_num)
  simp [ENNReal.div_eq_inv_mul, mul_add]

/-- Producing `xs` costs at most `2 * xs.length + xs.sum + 1` choices: one `oneOf` and one
`Nat.arbitrary` (bounded by the element plus one) per cons cell, plus the final `oneOf`. -/
theorem List.arbitrary.cost_bounded :
    IsCostBounded List.arbitrary (fun xs => 2 * xs.length + xs.sum + 1) := by
  cost_fixpoint [Nat.arbitrary.cost_bounded]
  all_goals simp only [List.length_nil, List.sum_nil, List.length_cons, List.sum_cons]; omega

theorem List.arbitrary.faithful : IsFaithful List.arbitrary := by
  faithful_fixpoint [List.arbitrary.terminates, Nat.arbitrary.faithful]

theorem List.arbitrary'.terminates : IsAlmostSurelyTerminating List.arbitrary' := by
  mass_fixpoint [Nat.arbitrary.terminates] using SPMF.LfpIsOne.one
  simp

theorem List.arbitrary'.faithful : IsFaithful List.arbitrary' := by
  faithful_fixpoint [List.arbitrary'.terminates, Nat.arbitrary.faithful]

end ArbList
