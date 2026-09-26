/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt.Walk.Average

/-!
# Walking Expectation Bounds

What the walk needs of an upper bound `SPMF.expectObs.spec g f ≤ B`: how a fact about a
sub-generator closes a leaf, the rules of the list combinators, and the admissibility
`walk fixpoint` inducts with.
-/

open ENNReal RandomChoice

open Lean.Order in
theorem SPMF.expectObs.admissible_le (f : α → ℝ≥0∞) (B : ℝ≥0∞) :
    admissible fun x : SPMF α => SPMF.expectObs.spec x f ≤ B :=
  SPMF.admissible_expect_le f B

/-! ## Leaves

A fact bounds a sub-generator's expectation under its own postexpectation `h`; the walk arrives with
`k + h`, and the missing mass only helps. -/

@[obs_leaf]
theorem SPMF.expect_le_add_of_le {x : SPMF α} {h p : α → ℝ≥0∞} {k B : ℝ≥0∞}
    (hx : SPMF.expectObs.spec x h ≤ B) (hp : ∀ a, p a = k + h a) :
    SPMF.expectObs.spec x p ≤ k + B := by
  show SPMF.expect x p ≤ k + B
  rw [funext hp, SPMF.expect_add, SPMF.expect_const]
  exact add_le_add (mul_le_of_le_one_left' (SPMF.mass_le_one x)) hx

/-! ## The list combinators

A list combinator has no shape of choice for the walk to enter, so its rules here use only its
mass: exactly when the postexpectation is constant, and otherwise at its worst case over every
value, dually to `le_expect_iInf_of_le` on the mass side. -/

namespace SPMF

/-- What the missing mass buys: an expectation is at most its postexpectation's largest value,
whatever the generator. -/
theorem expect_le_of_const {x : SPMF α} {p : α → ℝ≥0∞} {d : ℝ≥0∞} (hp : ∀ a, p a = d) :
    SPMF.expectObs.spec x p ≤ d :=
  SPMF.expect_le_of_support fun a _ => (hp a).le

@[inherit_doc expect_le_of_const]
theorem expect_le_iSup {x : SPMF α} {p : α → ℝ≥0∞} : SPMF.expectObs.spec x p ≤ ⨆ a, p a :=
  SPMF.expect_le_of_support fun a _ => le_iSup p a

section listCombinators

variable {α : Type} {g : SPMF α} {p : List α → ℝ≥0∞} {d : ℝ≥0∞}

@[gen_rule] theorem expect_vectorOf_le_const {n : Nat} (hp : ∀ a, p a = d) :
    expectObs.spec (vectorOf n g) p ≤ d := expect_le_of_const hp

@[gen_rule] theorem expect_vectorOf_le_iSup {n : Nat} :
    expectObs.spec (vectorOf n g) p ≤ ⨆ a, p a := expect_le_iSup

@[gen_rule] theorem expect_listOfMaxLength_le_const {n : Nat} (hp : ∀ a, p a = d) :
    expectObs.spec (listOfMaxLength n g) p ≤ d := expect_le_of_const hp

@[gen_rule] theorem expect_listOfMaxLength_le_iSup {n : Nat} :
    expectObs.spec (listOfMaxLength n g) p ≤ ⨆ a, p a := expect_le_iSup

@[gen_rule] theorem expect_listOf_le_const (hp : ∀ a, p a = d) :
    expectObs.spec (listOf g) p ≤ d := expect_le_of_const hp

@[gen_rule] theorem expect_listOf_le_iSup : expectObs.spec (listOf g) p ≤ ⨆ a, p a :=
  expect_le_iSup

@[gen_rule] theorem expect_nonEmptyListOf_le_const (hp : ∀ a, p a = d) :
    expectObs.spec (nonEmptyListOf g) p ≤ d := expect_le_of_const hp

@[gen_rule] theorem expect_nonEmptyListOf_le_iSup :
    expectObs.spec (nonEmptyListOf g) p ≤ ⨆ a, p a := expect_le_iSup

end listCombinators

@[gen_rule] theorem expect_permutationOf_le_const {xs : List α}
    {p : { ys // xs.Perm ys } → ℝ≥0∞} {d : ℝ≥0∞} (hp : ∀ a, p a = d) :
    expectObs.spec (permutationOf xs) p ≤ d := expect_le_of_const hp

@[gen_rule] theorem expect_permutationOf_le_iSup {xs : List α}
    {p : { ys // xs.Perm ys } → ℝ≥0∞} : expectObs.spec (permutationOf xs) p ≤ ⨆ a, p a :=
  expect_le_iSup

end SPMF
