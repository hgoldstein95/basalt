/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt.SPMF.Termination

/-!
# Ranking-Function Termination

`SPMF.LfpIsOne.ranking`, the certificate for a generator whose seed shrinks: a ranking function
whose expected value drops by `ε` under a level operator `SPMF.LevelOp` forces the one-step mass
bound's least fixed point to `1`, and bounds the expected number of unfolding steps by `φ / ε`. The
union bounds that discharge its deficit condition live here too.
-/

open ENNReal

namespace SPMF

section level_op

variable {ι : Type*}

/-- A level operator abstracts one step of a recursive generator's unfolding: `A e i` is the
expected total of `e` over the child seeds spawned by one step at seed `i`. -/
structure LevelOp (A : (ι → ℝ≥0∞) → (ι → ℝ≥0∞)) : Prop where
  mono : ∀ e f, e ≤ f → A e ≤ A f
  add : ∀ e f, A (e + f) = A e + A f
  smul : ∀ (r : ℝ≥0∞) (e), A (fun i => r * e i) = fun i => r * A e i

namespace LevelOp

variable {A : (ι → ℝ≥0∞) → (ι → ℝ≥0∞)}

theorem map_zero (hA : LevelOp A) : A 0 = 0 := by
  have h := hA.smul 0 0
  simpa [Pi.zero_def] using h

theorem map_sum (hA : LevelOp A) {β : Type*} (s : Finset β) (f : β → ι → ℝ≥0∞) :
    A (∑ b ∈ s, f b) = ∑ b ∈ s, A (f b) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hA.map_zero
  | insert b s hb ih => rw [Finset.sum_insert hb, Finset.sum_insert hb, hA.add, ih]

/-- Division by `ε` commutes with a level operator. -/
theorem map_div (hA : LevelOp A) (φ : ι → ℝ≥0∞) (ε : ℝ≥0∞) :
    A (fun j => φ j / ε) = fun i => A φ i / ε := by
  have h := hA.smul ε⁻¹ φ
  calc A (fun j => φ j / ε)
      = A (fun j => ε⁻¹ * φ j) := by
        congr 1; funext j; rw [div_eq_mul_inv, mul_comm]
    _ = fun i => ε⁻¹ * A φ i := h
    _ = fun i => A φ i / ε := by
        funext i; rw [div_eq_mul_inv, mul_comm]

/-- The partial sums of the expected level sizes `A^[k] 1` are uniformly bounded by `φ/ε`: `φ/ε` is
a pre-fixed point of `X ↦ 1 + A X`, and the partial sums climb toward it from below. -/
theorem sum_iterate_le (hA : LevelOp A) (φ : ι → ℝ≥0∞) {ε : ℝ≥0∞}
    (hε0 : ε ≠ 0) (hε_top : ε ≠ ⊤) (hdrift : ∀ i, A φ i + ε ≤ φ i) (n : ℕ) :
    ∑ k ∈ Finset.range n, A^[k] (fun _ => 1) ≤ fun i => φ i / ε := by
  have hpre : ∀ i, A (fun j => φ j / ε) i + 1 ≤ φ i / ε := by
    intro i
    rw [congrFun (hA.map_div φ ε) i]
    calc A φ i / ε + 1
        = A φ i / ε + ε / ε := by rw [ENNReal.div_self hε0 hε_top]
      _ = (A φ i + ε) / ε := by rw [ENNReal.div_add_div_same]
      _ ≤ φ i / ε := by gcongr; exact hdrift i
  induction n with
  | zero => simp only [Finset.range_zero, Finset.sum_empty]; exact fun _ => zero_le _
  | succ n ih =>
    rw [Finset.sum_range_succ']
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
    rw [← hA.map_sum]
    intro i
    simp only [Pi.add_apply]
    calc A (∑ k ∈ Finset.range n, A^[k] fun _ => 1) i + 1
        ≤ A (fun j => φ j / ε) i + 1 := by gcongr; exact hA.mono _ _ ih i
      _ ≤ φ i / ε := hpre i

/-- **The expected-size bound.** `∑ₖ A^[k] 1 i` is the expected total number of unfolding steps
taken from seed `i` (level `k` contributes its expected number of seeds); an `ε`-drifting ranking
function bounds it by `φ i / ε`. -/
theorem tsum_iterate_le (hA : LevelOp A) (φ : ι → ℝ≥0∞) {ε : ℝ≥0∞}
    (hε0 : ε ≠ 0) (hε_top : ε ≠ ⊤) (hdrift : ∀ i, A φ i + ε ≤ φ i) (i : ι) :
    ∑' k, A^[k] (fun _ => 1) i ≤ φ i / ε := by
  rw [ENNReal.tsum_eq_iSup_nat]
  refine iSup_le fun n => ?_
  have h := hA.sum_iterate_le φ hε0 hε_top hdrift n i
  simpa [Finset.sum_apply] using h

/-- The expected total number of unfolding steps of a level operator from seed `i`: level `k`
contributes its expected number of seeds, `A^[k] 1 i`. -/
noncomputable def expectedSteps (A : (ι → ℝ≥0∞) → (ι → ℝ≥0∞)) (i : ι) : ℝ≥0∞ :=
  ∑' k, A^[k] (fun _ => 1) i

/-- The drift certificate bounds the expected number of unfolding steps by `φ/ε`. -/
theorem expectedSteps_le (hA : LevelOp A) (φ : ι → ℝ≥0∞) {ε : ℝ≥0∞}
    (hε0 : ε ≠ 0) (hε_top : ε ≠ ⊤) (hdrift : ∀ i, A φ i + ε ≤ φ i) (i : ι) :
    expectedSteps A i ≤ φ i / ε :=
  hA.tsum_iterate_le φ hε0 hε_top hdrift i

/-- For the static-seed operator with mean offspring `m`, the expected number of steps is the
geometric sum `1/(1-m)`. -/
theorem expectedSteps_const_mul (m : ℝ≥0∞) (i : ι) :
    expectedSteps (fun e j => m * e j) i = (1 - m)⁻¹ := by
  have hiter : ∀ k, (fun (e : ι → ℝ≥0∞) j => m * e j)^[k] (fun _ => 1) = fun _ => m ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ_apply', ih]
      funext j
      rw [pow_succ, mul_comm]
  unfold expectedSteps
  rw [tsum_congr fun k => congrFun (hiter k) i]
  exact ENNReal.tsum_geometric m

end LevelOp

/-- **Ranking-function certificate.** Let `A` be a level operator describing the expected child
seeds of one unfolding step, and `φ` a finite ranking function whose expected value drops by at
least `ε > 0` at every step. If the deficit of `T` is dominated by `A` (`hdef`), `T` has least fixed
point `1`: a sub-fixed point's deficit is bounded by every level `A^[k] 1`, whose sum is finite. -/
theorem LfpIsOne.ranking {T : (ι → ℝ≥0∞) → (ι → ℝ≥0∞)}
    {A : (ι → ℝ≥0∞) → (ι → ℝ≥0∞)} (hA : LevelOp A)
    (φ : ι → ℝ≥0∞) (hφ_top : ∀ i, φ i ≠ ⊤) {ε : ℝ≥0∞} (hε : 0 < ε)
    (hdrift : ∀ i, A φ i + ε ≤ φ i)
    (hdef : ∀ c ≤ 1, ∀ i, 1 - T c i ≤ A (fun j => 1 - c j) i) :
    LfpIsOne T := by
  intro c hc hTc
  funext i
  have hε_top : ε ≠ ⊤ := by
    intro htop
    apply hφ_top i
    have h := hdrift i
    rw [htop, add_top, top_le_iff] at h
    exact h
  set d : ι → ℝ≥0∞ := fun j => 1 - c j
  -- `d` is dominated by every level: `d ≤ A^[k] 1`.
  have hd_le : ∀ k, d ≤ A^[k] (fun _ => 1) := by
    intro k
    induction k with
    | zero => intro j; simpa using tsub_le_self
    | succ k ih =>
      intro j
      calc d j ≤ 1 - T c j := tsub_le_tsub_left (hTc j) 1
        _ ≤ A d j := hdef c hc j
        _ ≤ A (A^[k] fun _ => 1) j := hA.mono _ _ ih j
        _ = A^[k + 1] (fun _ => 1) j := by rw [Function.iterate_succ_apply']
  -- The series `∑ₖ A^[k] 1 i` is finite, so a constant lower bound on its terms must be zero.
  have hd0 : d i = 0 := by
    by_contra hne
    have hsum : (⊤ : ℝ≥0∞) ≤ φ i / ε := by
      calc (⊤ : ℝ≥0∞) = ∑' (_ : ℕ), d i := (ENNReal.tsum_const_eq_top_of_ne_zero hne).symm
        _ ≤ ∑' k, A^[k] (fun _ => 1) i := ENNReal.tsum_le_tsum fun k => hd_le k i
        _ ≤ φ i / ε := hA.tsum_iterate_le φ hε.ne' hε_top hdrift i
    exact (ENNReal.div_lt_top (hφ_top i) hε.ne').ne (top_le_iff.mp hsum)
  exact le_antisymm (hc i) (tsub_eq_zero_iff_le.mp hd0)

end level_op

end SPMF

namespace ENNReal

private theorem list_prod_le_one {xs : List ℝ≥0∞} (h : ∀ x ∈ xs, x ≤ 1) : xs.prod ≤ 1 := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    rw [List.prod_cons]
    exact mul_le_one' (h x List.mem_cons_self) (ih fun y hy => h y (List.mem_cons_of_mem x hy))

/-- **The union bound**: the chance that some element of a product falls short of 1 is at most the
sum of the individual shortfalls. Applied to generator masses: the chance that some child diverges
is at most the sum of the chances that each does. This is the only probabilistic idea in the
ranking-function development. -/
theorem one_sub_prod_le_sum_one_sub (xs : List ℝ≥0∞) (h : ∀ x ∈ xs, x ≤ 1) :
    1 - xs.prod ≤ (xs.map (1 - ·)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx : x ≤ 1 := h x List.mem_cons_self
    have hxs : ∀ y ∈ xs, y ≤ 1 := fun y hy => h y (List.mem_cons_of_mem x hy)
    simp only [List.prod_cons, List.map_cons, List.sum_cons]
    calc 1 - x * xs.prod
        ≤ (1 - x) + (x - x * xs.prod) := tsub_le_tsub_add_tsub
      _ = (1 - x) + x * (1 - xs.prod) := by
          congr 1
          rw [ENNReal.mul_sub fun _ _ => (lt_of_le_of_lt hx one_lt_top).ne, mul_one]
      _ ≤ (1 - x) + 1 * (1 - xs.prod) := by gcongr
      _ ≤ (1 - x) + (xs.map (1 - ·)).sum := by rw [one_mul]; gcongr; exact ih hxs

/-- Binary form of the union bound, for a branch making two recursive calls. -/
theorem one_sub_mul_le_add {a b : ℝ≥0∞} (ha : a ≤ 1) (hb : b ≤ 1) :
    1 - a * b ≤ (1 - a) + (1 - b) := by
  have h := one_sub_prod_le_sum_one_sub [a, b] (by simp [ha, hb])
  simpa using h

/-- **Deficit splitting** for one unfolding step: a bound of at least `w + m * X` — escape branches
carrying weight `w`, recursive continuation of bound `X` weighted `m`, with `w + m = 1` — falls
short of `1` by at most `m * (1 - X)`. This is the standard first move in the deficit condition of
`SPMF.LfpIsOne.ranking`. -/
theorem one_sub_le_mul_one_sub {g w m X : ℝ≥0∞} (hwm : w + m = 1) (hm : m ≠ ⊤)
    (hmass : w + m * X ≤ g) : 1 - g ≤ m * (1 - X) := by
  have h1w : 1 - w = m :=
    ENNReal.sub_eq_of_eq_add ((le_self_add.trans hwm.le).trans_lt ENNReal.one_lt_top).ne
      (by rw [← hwm, add_comm])
  calc 1 - g ≤ 1 - (w + m * X) := tsub_le_tsub_left hmass 1
    _ = 1 - w - m * X := by rw [tsub_add_eq_tsub_tsub]
    _ = m * 1 - m * X := by rw [h1w, mul_one]
    _ = m * (1 - X) := (ENNReal.mul_sub fun _ _ => hm).symm

/-- **Averaged union bound**: if a step draws one of `s.card ≥ n` continuations uniformly (each of
mass `m x ≤ 1`), the deficit of the average is at most the average of the deficits: the deficit condition's step
through a uniform pivot. -/
theorem one_sub_sum_div_le {β : Type*} {s : Finset β} {m : β → ℝ≥0∞} {n : ℝ≥0∞}
    (hn0 : n ≠ 0) (hntop : n ≠ ⊤) (hns : n ≤ s.card) (hm : ∀ x ∈ s, m x ≤ 1) :
    1 - (∑ x ∈ s, m x) / n ≤ (∑ x ∈ s, (1 - m x)) / n := by
  rw [tsub_le_iff_right, ENNReal.div_add_div_same]
  calc (1 : ℝ≥0∞) = n / n := (ENNReal.div_self hn0 hntop).symm
    _ ≤ (∑ x ∈ s, ((1 - m x) + m x)) / n := by
        gcongr
        calc n ≤ (s.card : ℝ≥0∞) := hns
          _ = ∑ _x ∈ s, (1 : ℝ≥0∞) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
          _ ≤ _ := Finset.sum_le_sum fun x hx => (tsub_add_cancel_of_le (hm x hx)).ge
    _ = _ := by rw [Finset.sum_add_distrib]

end ENNReal
