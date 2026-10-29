/-
Copyright (c) 2026 Harrison Goldstein & Ernest Ng. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Ernest Ng
-/
module

public import BasaltExamples.UniformConstrained.Uniformity

/-!
# Bounded backtracking skews by at most a factor of `b + 1` (Section 5.1)

The paper states without proof that with backtracking bounded by `b`, "the probabilities of
generating any two values differ at most by a factor `b + 1`". This file proves it for a linear
model of the search, with the exact distribution `P(x) = w(x) / Σ w` (`backtrack_apply`).
-/

@[expose] public section

open ENNReal

namespace UniformConstrained.Backtracking

/-! ## The model

The values are the indices `0 … n - 1`, in indexing order, and `B` marks those satisfying the
predicate. The search draws a uniform start index, scans forward over at most `b` values failing
`B`, and returns the first satisfying one; if there is none it restarts with a fresh index.

This assumes `b` counts *values* skipped. An implementation that skips a whole pruned subspace as
one step skips many values at once, and then the bound below does not hold. -/

/-- The first index in `j … j + b` below `n` that satisfies `B`. -/
def scan (B : Nat → Bool) (n b j : Nat) : Option Nat :=
  (List.range' j (b + 1)).find? fun x => decide (x < n) && B x

section Def

variable {G : Type → Type} [Gen G]

/-- The search with backtracking bounded by `b`. -/
def backtrack (B : Nat → Bool) (n b : Nat) : G Nat := do
  let j ← chooseNat 0 (n - 1)
  match scan B n b j with
  | some x => pure x
  | none => backtrack B n b
partial_fixpoint

theorem backtrack_eq (B : Nat → Bool) (n b : Nat) :
    (backtrack B n b : G Nat)
      = (do
          let j ← chooseNat 0 (n - 1)
          match scan B n b j with
          | some x => pure x
          | none => backtrack B n b) := by
  conv_lhs => rw [backtrack]

end Def

variable {B : Nat → Bool} {n b : Nat}

/-- `scan` finds `x` from `j` exactly when `x` is within `b` of `j`, satisfies `B`, and nothing
between `j` and `x` does. -/
theorem scan_eq_some_iff {j x : Nat} :
    scan B n b j = some x ↔
      j ≤ x ∧ x ≤ j + b ∧ x < n ∧ B x = true ∧ ∀ y, j ≤ y → y < x → B y = false := by
  unfold scan
  induction b generalizing j with
  | zero =>
    simp only [Nat.zero_add, List.range'_one, List.find?_singleton, Bool.and_eq_true,
      decide_eq_true_eq]
    constructor
    · intro h
      split at h
      · rename_i hj
        cases h
        exact ⟨le_rfl, by omega, hj.1, hj.2, fun y h1 h2 => by omega⟩
      · cases h
    · rintro ⟨h1, h2, h3, h4, -⟩
      obtain rfl : j = x := by omega
      simp [h3, h4]
  | succ b ih =>
    rw [List.range'_succ, List.find?_cons]
    by_cases hj : j < n ∧ B j = true
    · simp only [hj, decide_true, Bool.and_self, Option.some.injEq]
      constructor
      · rintro rfl
        exact ⟨le_rfl, by omega, hj.1, hj.2, fun y h1 h2 => by omega⟩
      · rintro ⟨h1, -, -, -, h5⟩
        by_contra hne
        have := h5 j le_rfl (by omega)
        simp [hj.2] at this
    · have hj' : (decide (j < n) && B j) = false := by
        simpa [Bool.and_eq_true, decide_eq_true_eq] using hj
      simp only [hj']
      rw [ih]
      constructor
      · rintro ⟨h1, h2, h3, h4, h5⟩
        refine ⟨by omega, by omega, h3, h4, fun y hy1 hy2 => ?_⟩
        rcases Nat.eq_or_lt_of_le hy1 with rfl | hy1
        · by_contra hy
          exact hj ⟨by omega, by simpa using hy⟩
        · exact h5 y hy1 hy2
      · rintro ⟨h1, h2, h3, h4, h5⟩
        have hjx : j ≠ x := fun h => hj ⟨h ▸ h3, h ▸ h4⟩
        exact ⟨by omega, by omega, h3, h4, fun y hy1 hy2 => h5 y (by omega) hy2⟩

/-- The weight of `x`: the number of start indices from which the search finds `x`. -/
def weight (B : Nat → Bool) (n b x : Nat) : Nat :=
  ((Finset.range n).filter fun j => scan B n b j = some x).card

/-- The number of start indices from which the search finds anything. -/
def total (B : Nat → Bool) (n b : Nat) : Nat :=
  ((Finset.range n).filter fun j => (scan B n b j).isSome).card

/-! ## The distribution -/

/-- One round of the search: `x` is found directly from `weight x` of the `n` start indices, and
from the `n - total` others the search starts over. -/
theorem backtrack_apply_rec (hn : 0 < n) (x : Nat) :
    (backtrack B n b : SPMF Nat) x
      = ((weight B n b x : ℝ≥0∞) + ((n - total B n b : Nat) : ℝ≥0∞)
          * (backtrack B n b : SPMF Nat) x) / (n : ℝ≥0∞) := by
  classical
  conv_lhs => rw [backtrack_eq]
  rw [chooseNat_bind_apply hn]
  congr 1
  have hterm : ∀ j, (match scan B n b j with
        | some y => (pure y : SPMF Nat)
        | none => backtrack B n b) x
      = (if scan B n b j = some x then 1 else 0)
        + (if (scan B n b j).isSome then 0 else 1) * (backtrack B n b : SPMF Nat) x := by
    intro j
    rcases h : scan B n b j with _ | y
    · simp
    · simp [SPMF.pure_apply, eq_comm]
  rw [Finset.sum_congr rfl fun j _ => hterm j, Finset.sum_add_distrib, ← Finset.sum_mul,
    Finset.sum_boole, Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const,
    nsmul_eq_mul, mul_one]
  congr 2
  have h := Finset.card_filter_add_card_filter_not (s := Finset.range n)
    (fun j => (scan B n b j).isSome = true)
  rw [Finset.card_range] at h
  rw [total]
  congr 1
  omega

theorem total_le : total B n b ≤ n := by
  rw [total]
  exact (Finset.card_filter_le _ _).trans (Finset.card_range n).le

/-- **The exact distribution**: `P(x) = weight x / total`, whenever some value satisfies `B`. -/
theorem backtrack_apply (hW : 0 < total B n b) (x : Nat) :
    (backtrack B n b : SPMF Nat) x = (weight B n b x : ℝ≥0∞) / (total B n b : ℝ≥0∞) := by
  have hn : 0 < n := lt_of_lt_of_le hW total_le
  have hrec := backtrack_apply_rec (B := B) (b := b) hn x
  have hPtop := SPMF.apply_ne_top (backtrack B n b : SPMF Nat) x
  generalize (backtrack B n b : SPMF Nat) x = P at hrec hPtop ⊢
  have hle := total_le (B := B) (n := n) (b := b)
  generalize total B n b = W at hrec hW hle ⊢
  have hn0 : (n : ℝ≥0∞) ≠ 0 := by rw [Ne, Nat.cast_eq_zero]; omega
  have hW0 : (W : ℝ≥0∞) ≠ 0 := by rw [Ne, Nat.cast_eq_zero]; omega
  -- `n P = w + (n - W) P`, so `W P = w`.
  have h1 : (W : ℝ≥0∞) * P + ((n - W : Nat) : ℝ≥0∞) * P
      = (weight B n b x : ℝ≥0∞) + ((n - W : Nat) : ℝ≥0∞) * P := by
    rw [← add_mul, ← Nat.cast_add, Nat.add_sub_cancel' hle]
    nth_rewrite 1 [hrec]
    rw [ENNReal.mul_div_cancel hn0 (ENNReal.natCast_ne_top _)]
  have h2 : (W : ℝ≥0∞) * P = weight B n b x :=
    (ENNReal.add_left_inj (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hPtop)).mp h1
  rw [← h2, mul_comm, ENNReal.mul_div_cancel_right hW0 (ENNReal.natCast_ne_top _)]

/-! ## The bounds -/

/-- Every satisfying value is found from its own index. -/
theorem one_le_weight {x : Nat} (hx : x < n) (hB : B x = true) : 1 ≤ weight B n b x := by
  rw [weight, Nat.one_le_iff_ne_zero, Ne, Finset.card_eq_zero, ← Ne, ← Finset.nonempty_iff_ne_empty]
  exact ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hx,
    scan_eq_some_iff.mpr ⟨le_rfl, by omega, hx, hB, fun y h1 h2 => by omega⟩⟩⟩

/-- No value is found from more than `b + 1` start indices: they all lie in `x - b … x`. -/
theorem weight_le (x : Nat) : weight B n b x ≤ b + 1 := by
  rw [weight]
  calc _ ≤ (Finset.Icc (x - b) x).card := Finset.card_le_card fun j hj => by
          obtain ⟨-, hj⟩ := Finset.mem_filter.mp hj
          obtain ⟨h1, h2, -⟩ := scan_eq_some_iff.mp hj
          exact Finset.mem_Icc.mpr ⟨by omega, h1⟩
    _ ≤ b + 1 := by rw [Nat.card_Icc]; omega

/-- **Section 5.1: the probabilities of generating two satisfying values differ at most by a factor
`b + 1`.** -/
theorem backtrack_le_mul (hW : 0 < total B n b) (x : Nat) {y : Nat} (hy : y < n)
    (hB : B y = true) :
    (backtrack B n b : SPMF Nat) x ≤ (b + 1 : ℝ≥0∞) * (backtrack B n b : SPMF Nat) y := by
  rw [backtrack_apply hW, backtrack_apply hW, ← mul_div_assoc]
  refine ENNReal.div_le_div_right ?_ _
  calc (weight B n b x : ℝ≥0∞) ≤ ((b + 1 : Nat) : ℝ≥0∞) := Nat.cast_le.mpr (weight_le x)
    _ = (b + 1 : ℝ≥0∞) * ((1 : Nat) : ℝ≥0∞) := by push_cast; ring
    _ ≤ (b + 1 : ℝ≥0∞) * (weight B n b y : ℝ≥0∞) := by
        gcongr; exact Nat.cast_le.mpr (one_le_weight hy hB)

/-- Without a bound the skew is limited only by the failures: a value is found from its own index
or from one of the `n - m` failing ones. -/
theorem weight_le_failures (x : Nat) :
    weight B n b x ≤ 1 + ((Finset.range n).filter fun j => B j = false).card := by
  rw [weight]
  calc _ ≤ (insert x ((Finset.range n).filter fun j => B j = false)).card :=
        Finset.card_le_card fun j hj => by
          obtain ⟨hjn, hj⟩ := Finset.mem_filter.mp hj
          obtain ⟨h1, -, -, -, h5⟩ := scan_eq_some_iff.mp hj
          rcases Nat.eq_or_lt_of_le h1 with rfl | h1
          · exact Finset.mem_insert_self _ _
          · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hjn, h5 j le_rfl h1⟩)
    _ ≤ _ := by rw [add_comm]; exact Finset.card_insert_le _ _

/-- **Unbounded backtracking: the skew is at most `n - m + 1`**, where `n - m` values fail `B`. -/
theorem backtrack_le_mul_failures (hW : 0 < total B n b) (x : Nat) {y : Nat} (hy : y < n)
    (hB : B y = true) :
    (backtrack B n b : SPMF Nat) x
      ≤ ((1 + ((Finset.range n).filter fun j => B j = false).card : Nat) : ℝ≥0∞)
        * (backtrack B n b : SPMF Nat) y := by
  rw [backtrack_apply hW, backtrack_apply hW, ← mul_div_assoc]
  refine ENNReal.div_le_div_right ?_ _
  calc (weight B n b x : ℝ≥0∞)
      ≤ ((1 + ((Finset.range n).filter fun j => B j = false).card : Nat) : ℝ≥0∞) :=
        Nat.cast_le.mpr (weight_le_failures x)
    _ = _ * ((1 : Nat) : ℝ≥0∞) := by rw [Nat.cast_one, mul_one]
    _ ≤ _ := by gcongr; exact Nat.cast_le.mpr (one_le_weight hy hB)

/-- With `b = 0` the search is the rejection sampler: every satisfying value has weight 1, so the
distribution is uniform, as `Theorem1` says of `uniformFilter`. -/
theorem weight_zero (x : Nat) : weight B n 0 x = if x < n ∧ B x = true then 1 else 0 := by
  rw [weight]
  split
  · rename_i hx
    rw [Finset.card_eq_one]
    refine ⟨x, Finset.eq_singleton_iff_unique_mem.mpr ⟨Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr hx.1, scan_eq_some_iff.mpr ⟨le_rfl, by omega, hx.1, hx.2,
        fun y h1 h2 => by omega⟩⟩, fun j hj => ?_⟩⟩
    obtain ⟨h1, h2, -⟩ := scan_eq_some_iff.mp (Finset.mem_filter.mp hj).2
    omega
  · rename_i hx
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro j _ hj
    obtain ⟨-, -, h3, h4, -⟩ := scan_eq_some_iff.mp hj
    exact hx ⟨h3, h4⟩

theorem backtrack_zero_apply (hW : 0 < total B n 0) (x : Nat) :
    (backtrack B n 0 : SPMF Nat) x
      = (if x < n ∧ B x = true then 1 else 0) / (total B n 0 : ℝ≥0∞) := by
  rw [backtrack_apply hW, weight_zero]
  split <;> simp

/-! ## The bounds are tight

With `c` failing values followed by two satisfying ones and backtracking bound `b ≥ c`, the first
satisfying value is found from all `c + 1` indices up to it and the second only from its own. With
`b = c` that is the factor `b + 1`; with unbounded backtracking (`b ≥ n`) it is the factor
`n - m + 1`, here `m = 2`. -/

/-- `c` failures, then two satisfying values. -/
def tightB (c : Nat) (x : Nat) : Bool := decide (c ≤ x)

theorem weight_tight_first {c b : Nat} (hcb : c ≤ b) : weight (tightB c) (c + 2) b c = c + 1 := by
  rw [weight, ← Finset.card_range (c + 1)]
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_range, scan_eq_some_iff, tightB, decide_eq_true_eq,
    decide_eq_false_iff_not, not_le]
  constructor
  · rintro ⟨-, h1, -⟩; omega
  · intro hj; exact ⟨by omega, by omega, by omega, by omega, le_rfl, fun y h1 h2 => h2⟩

theorem weight_tight_second {c b : Nat} : weight (tightB c) (c + 2) b (c + 1) = 1 := by
  rw [weight, Finset.card_eq_one]
  refine ⟨c + 1, ?_⟩
  ext j
  simp only [Finset.mem_filter, Finset.mem_range, scan_eq_some_iff, tightB, decide_eq_true_eq,
    decide_eq_false_iff_not, not_le, Finset.mem_singleton]
  constructor
  · rintro ⟨-, h1, -, -, -, h5⟩
    by_contra hj
    have := h5 c (by omega) (by omega)
    omega
  · rintro rfl; exact ⟨by omega, le_rfl, by omega, by omega, by omega, fun y h1 h2 => by omega⟩

/-- **The factor is attained**: the first satisfying value is `c + 1` times as likely as the second,
for any backtracking bound `b ≥ c`. -/
theorem backtrack_tight {c b : Nat} (hcb : c ≤ b) :
    (backtrack (tightB c) (c + 2) b : SPMF Nat) c
      = ((c + 1 : Nat) : ℝ≥0∞) * (backtrack (tightB c) (c + 2) b : SPMF Nat) (c + 1) := by
  have hW : 0 < total (tightB c) (c + 2) b := by
    rw [total, Finset.card_pos]
    exact ⟨c, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), by
      rw [Option.isSome_iff_exists]
      exact ⟨c, scan_eq_some_iff.mpr ⟨le_rfl, by omega, by omega, by simp [tightB],
        fun y h1 h2 => by omega⟩⟩⟩⟩
  rw [backtrack_apply hW, backtrack_apply hW, weight_tight_first hcb, weight_tight_second,
    Nat.cast_one, ← mul_div_assoc, mul_one]

end UniformConstrained.Backtracking
