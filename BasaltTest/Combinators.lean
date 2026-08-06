import Basalt

open NNReal ENNReal

/-!
# Facts about the combinators

Concrete `frequency` branch probabilities, computed with `SPMF.frequency_apply` and friends and
pinned here as regression tests, plus a check that `oneOf` works under `partial_fixpoint`.
-/

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
  apply IsPMF_frequency
  intro p hp _
  fin_cases hp <;> exact IsPMF_pure _

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
    fun _ => RandomChoice.pick
      (fun _ => pure (NatOrFloat.Nat 1))
      (fun _ => pure (NatOrFloat.Float 1.0)),
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
