import Basalt

open NNReal ENNReal

/-!
# Distribution facts about `frequency`

Concrete branch probabilities, computed with `SPMF.frequency_apply` and friends and pinned
here as regression tests.
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
