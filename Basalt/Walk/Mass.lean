/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
module

public import Basalt.SPMF.Mass
public import Basalt.Walk.Average
public import Basalt.Walk.Entry

/-!
# Walking Mass Bounds

What the walk needs of a lower bound `c ≤ SPMF.expectObs.spec g f`, which at `f = fun _ => 1` is a
bound on `g`'s mass and so the structural half of a termination proof: how a fact about a
sub-generator's mass closes a leaf, and the rules of the list combinators.
-/

@[expose] public section

open ENNReal RandomChoice

namespace SPMF

/-! ## Leaves

A fact bounds a sub-generator's mass; the walk arrives with the postexpectation its continuation
computed. A fact that the mass is `1` is tried first, for a bound free of the factor `1`. -/

/-- At the postexpectation `1`, which is where a generator's last draw is met. -/
@[obs_leaf]
theorem le_expect_one_of_le {x : SPMF α} {p : α → ℝ≥0∞} {c : ℝ≥0∞}
    (hx : c ≤ expectObs.spec x fun _ => 1) (hp : ∀ a, p a = 1) : c ≤ expectObs.spec x p := by
  rw [funext hp]
  exact hx

@[obs_leaf]
theorem le_expect_of_one_le {x : SPMF α} {p : α → ℝ≥0∞} {d : ℝ≥0∞}
    (hx : 1 ≤ expectObs.spec x fun _ => 1) (hp : ∀ a, p a = d) : d ≤ expectObs.spec x p := by
  show d ≤ expect x p
  rw [funext hp, expect_const]
  exact le_mul_of_one_le_left' (hx.trans_eq (expect_one x))

@[obs_leaf]
theorem le_expect_of_le {x : SPMF α} {p : α → ℝ≥0∞} {c d : ℝ≥0∞}
    (hx : c ≤ expectObs.spec x fun _ => 1) (hp : ∀ a, p a = d) : c * d ≤ expectObs.spec x p := by
  show c * d ≤ expect x p
  rw [funext hp, expect_const]
  gcongr
  exact hx.trans_eq (expect_one x)

/-- The fallback for a continuation whose bound depends on the value drawn: a fact about the mass
alone can only be used with the worst case over every value. -/
@[obs_leaf]
theorem le_expect_iInf_of_one_le {x : SPMF α} {p : α → ℝ≥0∞}
    (hx : 1 ≤ expectObs.spec x fun _ => 1) : ⨅ a, p a ≤ expectObs.spec x p :=
  (le_expect_of_one_le hx fun _ => rfl).trans (expect_mono fun a => iInf_le p a)

@[obs_leaf, inherit_doc le_expect_iInf_of_one_le]
theorem le_expect_iInf_of_le {x : SPMF α} {p : α → ℝ≥0∞} {c : ℝ≥0∞}
    (hx : c ≤ expectObs.spec x fun _ => 1) : c * ⨅ a, p a ≤ expectObs.spec x p :=
  (le_expect_of_le hx fun _ => rfl).trans (expect_mono fun a => iInf_le p a)

/-! ## Lower bounds on an expectation

A recursive occurrence is met under `k + h`, which a lower bound on its expectation of `h` bounds
only when its mass is `1`: `le_expect_add` states it that way. Fixpoint induction proves no lower
bound, so the fact comes from an induction on a seed that shrinks, as for `SPMF.Cost.le_expect_add`
(`Basalt/Walk/ExpectedCost.lean`). -/

/-- A lower bound `B` on `x`'s expectation of `h`, for use under any `k + h`, from `x`'s mass. -/
theorem le_expect_add {x : SPMF α} {h : α → ℝ≥0∞} {B : ℝ≥0∞}
    (hm : 1 ≤ expectObs.spec x fun _ => 1) (hx : B ≤ expectObs.spec x h) (k : ℝ≥0∞) :
    k + B ≤ expectObs.spec x fun a => k + h a := by
  show _ ≤ expect x fun a => k + h a
  rw [expect_add, expect_const]
  exact add_le_add (le_mul_of_one_le_left' (hm.trans_eq (expect_one x))) hx

@[obs_leaf]
theorem le_expect_of_add_le {x : SPMF α} {h p : α → ℝ≥0∞} {k B : ℝ≥0∞}
    (hx : ∀ k, k + B ≤ expectObs.spec x fun a => k + h a) (hp : ∀ a, p a = k + h a) :
    k + B ≤ expectObs.spec x p := by
  rw [funext hp]
  exact hx k

end SPMF

namespace SPMF

/-! ## The list combinators

They take a bound on their element generator's mass, and their own is used at the postexpectation
the walk arrives with: exactly when that is constant, and otherwise at its worst case over every
list, as `le_expect_iInf_of_le` does for a leaf. The unbounded-length ones (`le_expect_listOf`,
`le_expect_nonEmptyListOf`, in `MassFixpoint.lean`) only turn a terminating element generator into a
terminating list generator. -/

private theorem pow_le_vectorOf {n : Nat} {g : SPMF α} {c : ℝ≥0∞}
    (hg : c ≤ expectObs.spec g fun _ => 1) :
    c ^ n ≤ expectObs.spec (vectorOf n g : SPMF (List α)) fun _ => 1 := by
  induction n with
  | zero =>
    show c ^ 0 ≤ expect (Pure.pure [] : SPMF (List α)) fun _ => 1
    rw [expect_pure, pow_zero]
  | succ n ih =>
    rw [vectorOf_succ]
    walk
    rw [pow_succ']

@[gen_rule]
theorem le_expect_vectorOf {n : Nat} {g : SPMF α} {c d : ℝ≥0∞} {p : List α → ℝ≥0∞}
    (hg : c ≤ expectObs.spec g fun _ => 1) (hp : ∀ a, p a = d) :
    c ^ n * d ≤ expectObs.spec (vectorOf n g) p :=
  le_expect_of_le (pow_le_vectorOf hg) hp

/-- The fallback for a postexpectation that depends on the list drawn. -/
@[gen_rule]
theorem le_expect_vectorOf_iInf {n : Nat} {g : SPMF α} {c : ℝ≥0∞} {p : List α → ℝ≥0∞}
    (hg : c ≤ expectObs.spec g fun _ => 1) :
    c ^ n * ⨅ a, p a ≤ expectObs.spec (vectorOf n g) p :=
  le_expect_iInf_of_le (pow_le_vectorOf hg)

private theorem pow_le_listOfMaxLength {n : Nat} {g : SPMF α} {c : ℝ≥0∞}
    (hg : c ≤ expectObs.spec g fun _ => 1) :
    min 1 c ^ n ≤ expectObs.spec (listOfMaxLength n g : SPMF (List α)) fun _ => 1 := by
  show _ ≤ expect _ _
  unfold listOfMaxLength
  rw [expect_bind, expect_map]
  refine le_trans ?_ (Mix.le_average_range (h := Nat.zero_le n) (d := fun _ => min 1 c ^ n)
    fun k hk => ?_)
  · rw [Finset.sum_const, card_Icc_eq 0 n (Nat.zero_le n), nsmul_eq_mul, mul_comm,
      ENNReal.mul_div_cancel_right (by simp) (by simp)]
  · simp only [Function.comp_apply]
    exact (pow_le_pow_right_of_le_one' (min_le_left 1 c) hk.2).trans
      ((pow_le_pow_left' (min_le_right 1 c) k).trans (pow_le_vectorOf hg))

@[gen_rule]
theorem le_expect_listOfMaxLength {n : Nat} {g : SPMF α} {c d : ℝ≥0∞} {p : List α → ℝ≥0∞}
    (hg : c ≤ expectObs.spec g fun _ => 1) (hp : ∀ a, p a = d) :
    min 1 c ^ n * d ≤ expectObs.spec (listOfMaxLength n g) p :=
  le_expect_of_le (pow_le_listOfMaxLength hg) hp

@[gen_rule, inherit_doc le_expect_vectorOf_iInf]
theorem le_expect_listOfMaxLength_iInf {n : Nat} {g : SPMF α} {c : ℝ≥0∞} {p : List α → ℝ≥0∞}
    (hg : c ≤ expectObs.spec g fun _ => 1) :
    min 1 c ^ n * ⨅ a, p a ≤ expectObs.spec (listOfMaxLength n g) p :=
  le_expect_iInf_of_le (pow_le_listOfMaxLength hg)

private theorem one_le_mass_permutationOf {xs : List α} :
    1 ≤ (permutationOf xs : SPMF { ys // xs.Perm ys }).mass := by
  induction xs with
  | nil => exact (mass_pure _).ge
  | cons x xs ih =>
    rw [permutationOf]
    refine (one_mul (1 : ℝ≥0∞)).symm.le.trans (mass_bind_ge_mul ih fun _ => ?_)
    refine (one_mul (1 : ℝ≥0∞)).symm.le.trans
      (mass_bind_ge_mul (mass_map.trans (mass_choose _ _ _)).ge fun ⟨_, _, _⟩ => (mass_pure _).ge)

/-- `permutationOf` takes no generator and always succeeds. -/
@[gen_rule]
theorem le_expect_permutationOf {xs : List α} {d : ℝ≥0∞} {p : { ys // xs.Perm ys } → ℝ≥0∞}
    (hp : ∀ a, p a = d) : d ≤ expectObs.spec (permutationOf xs) p :=
  le_expect_of_one_le (one_le_mass_permutationOf.trans_eq (expect_one _).symm) hp

@[gen_rule, inherit_doc le_expect_vectorOf_iInf]
theorem le_expect_permutationOf_iInf {xs : List α} {p : { ys // xs.Perm ys } → ℝ≥0∞} :
    ⨅ a, p a ≤ expectObs.spec (permutationOf xs) p :=
  le_expect_iInf_of_one_le (one_le_mass_permutationOf.trans_eq (expect_one _).symm)

end SPMF
