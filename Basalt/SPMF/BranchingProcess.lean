/-
Copyright (c) 2026 Harrison Goldstein & Ernest Ng. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Ernest Ng
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Basic.ENNReal.Operations
public import Mathlib.Data.Matrix.Mul

/-!
# Branching-Process Predictions

The multi-type branching process of a size-bounded generator for mutually recursive types (Mista,
Russo, and Hughes, "Branching Processes for QuickCheck Generators", Haskell '18), and its prediction
of each constructor's expected count. `predicted_succ` is the prediction's one-step equation, which
is what a walk over one unfolding of the generator meets.
-/

@[expose] public section

open scoped ENNReal

namespace BranchingProcess

/-- A generator for the types `ι`, read as a branching process: each constructor `κ` builds a value
of type `ty c`, is chosen with probability `prob c` when a value of that type is needed, and has
`args v c` arguments of type `v`. -/
structure Spec (ι κ : Type*) where
  ty : κ → ι
  prob : κ → ℝ≥0∞
  args : ι → κ → ℕ

namespace Spec

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] (S : Spec ι κ)

/-- A constructor with no recursive argument. -/
def terminal (c : κ) : Prop := ∀ v, S.args v c = 0

instance (c : κ) : Decidable (S.terminal c) := by unfold terminal; infer_instance

/-- The mean matrix of types (Prop. A.2): the expected number of placeholders of type `v` that one
of type `u` generates, `Σ_{c : u} args v c · prob c`. -/
noncomputable def meanTypes : Matrix ι ι ℝ≥0∞ :=
  fun u v => ∑ c, if S.ty c = u then (S.args v c : ℝ≥0∞) * S.prob c else 0

/-- The expected number of placeholders of each type at level `k`, from one of type `r`:
`E[G_k]ᵀ = E[G_0]ᵀ · M^k` (equation 7). -/
noncomputable def level (r : ι) (k : ℕ) : ι → ℝ≥0∞ :=
  Matrix.vecMul (Pi.single r 1) (S.meanTypes ^ k)

/-- The predicted expected number of `c`s at size `n` from a root of type `r`: the placeholders of
`c`'s type on the first `n` levels times `prob c` (Theorem 1), and for a terminal every placeholder
of its type on level `n`, where the size is exhausted (§5). -/
noncomputable def predicted (r : ι) (c : κ) (n : ℕ) : ℝ≥0∞ :=
  S.prob c * ∑ k ∈ Finset.range n, S.level r k (S.ty c) +
    if S.terminal c then S.level r n (S.ty c) else 0

theorem level_zero (r : ι) : S.level r 0 = Pi.single r 1 := by
  simp [level]

theorem level_apply (r : ι) (k : ℕ) (t : ι) : S.level r k t = (S.meanTypes ^ k) r t := by
  simp [level]

theorem level_succ (r : ι) (k : ℕ) (t : ι) :
    S.level r (k + 1) t = ∑ v, S.meanTypes r v * S.level v k t := by
  simp only [level_apply, pow_succ', Matrix.mul_apply]

theorem predicted_zero (r : ι) (c : κ) :
    S.predicted r c 0 = if S.terminal c ∧ S.ty c = r then 1 else 0 := by
  by_cases h : S.terminal c <;> by_cases h' : S.ty c = r <;>
    simp [predicted, level_zero, h, h']

/-- One level of the prediction: a root of type `r` is itself a `c` with probability `prob c`, and
its placeholders of type `v` predict as roots of type `v` one size down. -/
theorem predicted_succ (r : ι) (c : κ) (n : ℕ) :
    S.predicted r c (n + 1) =
      S.prob c * (if S.ty c = r then 1 else 0) + ∑ v, S.meanTypes r v * S.predicted v c n := by
  simp only [predicted, Finset.sum_range_succ', level_succ, level_zero, Pi.single_apply,
    mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  rw [Finset.sum_comm]
  split_ifs <;> simp only [mul_zero, Finset.sum_const_zero, add_zero, mul_left_comm (S.prob c)] <;>
    ring

end Spec

end BranchingProcess
