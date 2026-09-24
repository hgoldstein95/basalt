/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt

/-!
# Facts about the combinators

Concrete `frequency` branch probabilities, computed with `SPMF.frequency_apply` and friends and
pinned here as regression tests, plus a check that `oneOf`, and the deprecated `pick` defined by
it, work under `partial_fixpoint`.
-/

open NNReal ENNReal

namespace FrequencyExamples

open SPMF

example : (frequency [(1, fun _ => Pure.pure 0), (3, fun _ => Pure.pure 1)]
    (by simp) : SPMF Nat) 1 = 3 / 4 := by
  simp

-- Duplicate branches contribute separately: `frequency_apply`'s sums are `List.sum`s, and
-- a `Finset` sum would collapse these two branches and halve the probability.
example : (frequency [(1, fun _ => Pure.pure 0), (1, fun _ => Pure.pure 0)]
    (by simp) : SPMF Nat) 0 = 1 := by
  simp
  rw [one_add_one_eq_two, ENNReal.div_self (by norm_num) (by norm_num)]

-- Equal weights are genuinely uniform.
example : (frequency [(1, fun _ => Pure.pure 0), (1, fun _ => Pure.pure 1),
    (1, fun _ => Pure.pure 2), (1, fun _ => Pure.pure 3)]
    (by simp) : SPMF Nat) 2 = 1 / 4 := by
  simp

example : IsPMF (frequency [(2, fun _ => Pure.pure true), (3, fun _ => Pure.pure false)]
    (by simp) : SPMF Bool) := by
  refine IsPMF.of_one_le ?_
  mass_bound
  norm_num [ENNReal.div_self]

end FrequencyExamples

-- A tagged sum type `Nat + Float`
inductive NatOrFloat
  | Nat (n : Nat)
  | Float (f : Float)
deriving Repr

-- Generates either a `Nat` or a `Float` that's either 1,
-- a multiple of 2, or a multiple of 3
-- (This generator tests that we can use `oneOf` in functions marked as `partial_fixpoint`)
def myGen [Gen G] : G NatOrFloat :=
  oneOf [
    fun _ => oneOf
      [fun _ => pure (NatOrFloat.Nat 1),
       fun _ => pure (NatOrFloat.Float 1.0)],
    fun _ => do
      let natOrFloat ← myGen
      match natOrFloat with
      | .Nat n => pure (.Nat (n * 2))
      | .Float f => pure (.Float (f * 2)),
    fun _ => do
      let natOrFloat ← myGen
      match natOrFloat with
      | .Nat n => pure (.Nat (n * 3))
      | .Float f => pure (.Float (f * 3))

  ] (by simp)
partial_fixpoint

#guard_msgs(drop info) in
#eval (for _ in [0:10] do
  IO.println <| repr (← myGen) : IO Unit)

-- Sample `permutationOf`: each draw should be a permutation of `[1, 2, 3, 4, 5]`.
#guard_msgs(drop info) in
#eval (for _ in [0:10] do
  IO.println <| repr (← permutationOf [1, 2, 3, 4, 5]).val : IO Unit)

/-! The deprecated `pick` is `oneOf` of two branches: a recursive generator using it still
elaborates as a `partial_fixpoint`, and the walker proves its laws through `oneOf`. -/

namespace DeprecatedPick

set_option linter.deprecated false

open RandomChoice in
def natGen [Gen G] : G Nat :=
  pick (fun _ => pure 0) (fun _ => do let n ← natGen; pure (n + 1))
partial_fixpoint

theorem natGen.cost_bounded : IsCostBounded natGen (fun n => n + 1) := by
  cost_fixpoint
  all_goals omega

end DeprecatedPick
