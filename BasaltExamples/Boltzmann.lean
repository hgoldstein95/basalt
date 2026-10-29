/-
Copyright (c) 2026 Ernest Ng. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Ernest Ng
-/
module

import Mathlib.Tactic.Basify
public import Basalt

/-!
# Boltzmann Sampling of Binary Trees

The Boltzmann sampler for binary trees (Duchon, Flajolet, Louchard and Schaeffer 2004, Example 2),
with its leaf probability `p = x / B(x)` as a parameter. Every tree of size `n` gets mass
`x ^ n / B(x)`, so the sampler is uniform within each size, before and after rejection to a size
window; its expected size `1 / (2p - 1)`, infinite at the critical `p = 1/2`, is proved by fixpoint
induction rather than from the generating function.
-/

@[expose] public section

open RandomChoice SPMF
open scoped ENNReal

namespace Boltzmann

/-- Binary trees: `B = Z + Z × B × B`. -/
inductive BTree where
  | leaf
  | node (l r : BTree)
deriving DecidableEq

/-- The number of internal nodes. -/
def BTree.internal : BTree → Nat
  | .leaf => 0
  | .node l r => l.internal + r.internal + 1

/-- The size of a tree: every node, internal or leaf, is one atom. -/
def BTree.size : BTree → Nat
  | .leaf => 1
  | .node l r => l.size + r.size + 1

theorem BTree.size_eq (t : BTree) : t.size = 2 * t.internal + 1 := by
  induction t with
  | leaf => rfl
  | node l r ihl ihr => simp only [BTree.size, BTree.internal, ihl, ihr]; omega

/-- The probability `coin p` lands `true`. -/
noncomputable def pr (p : Rat) : ℝ≥0∞ := (p.num.toNat : ℝ≥0∞) / (p.den : ℝ≥0∞)

/-- `Γ B(x)`, with `p = x / B(x)`: a leaf with probability `p`, else a node and two recursive calls. -/
def genB [Gen G] (p : Rat) : G BTree := do
  if ← coin p then return .leaf
  else return .node (← genB p) (← genB p)
partial_fixpoint

section coin

theorem pr_compl (p : Rat) : ((p.den - p.num.toNat : ℕ) : ℝ≥0∞) / p.den = 1 - pr p := by
  rw [ENNReal.natCast_sub, ENNReal.sub_div (fun _ _ => by simp),
    ENNReal.div_self (by simp) (by simp), pr]

theorem coin_true (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : (coin p : SPMF Bool) true = pr p :=
  coin_apply_true hp0 hp1

theorem coin_false (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : (coin p : SPMF Bool) false = 1 - pr p := by
  rw [coin_apply_false hp0 hp1, pr_compl]

theorem pr_le_one (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : pr p ≤ 1 := by
  rw [← coin_true hp0 hp1]; exact coe_le_one _ _

theorem pr_eq_ofReal (hp0 : 0 ≤ p) : pr p = ENNReal.ofReal (p : ℝ) := by
  have hnum : ((p.num.toNat : ℕ) : ℝ) = (p.num : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg (Rat.num_nonneg.2 hp0)
  rw [pr]
  conv_rhs => rw [← Rat.num_div_den p]
  push_cast
  rw [ENNReal.ofReal_div_of_pos (by positivity), ← hnum, ENNReal.ofReal_natCast,
    ENNReal.ofReal_natCast]

private theorem half_eq_ofReal : (1 / 2 : ℝ≥0∞) = ENNReal.ofReal (1 / 2) := by
  rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp

theorem half_le_pr (hp : 1/2 ≤ p) : 1/2 ≤ pr p := by
  rw [pr_eq_ofReal (le_trans (by norm_num) hp), half_eq_ofReal]
  exact ENNReal.ofReal_le_ofReal (by simpa using (Rat.cast_le (K := ℝ)).2 hp)

theorem half_lt_pr (hp : 1/2 < p) : 1/2 < pr p := by
  rw [pr_eq_ofReal (le_trans (by norm_num) hp.le), half_eq_ofReal]
  have h : ((1/2 : ℚ) : ℝ) < (p : ℝ) := (Rat.cast_lt (K := ℝ)).2 hp
  simp only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at h
  exact (ENNReal.ofReal_lt_ofReal_iff (lt_trans (by norm_num) h)).2 h

end coin

section mass

private theorem node_apply_leaf (μ : SPMF BTree) :
    (μ >>= fun a => μ >>= fun b => Pure.pure (BTree.node a b)) .leaf = 0 := by
  rw [bind_apply]
  refine ENNReal.tsum_eq_zero.2 fun a => ?_
  rw [bind_apply, ENNReal.tsum_eq_zero.2 fun b => by simp, mul_zero]

private theorem node_apply_node (μ : SPMF BTree) (l r : BTree) :
    (μ >>= fun a => μ >>= fun b => Pure.pure (BTree.node a b)) (.node l r) = μ l * μ r := by
  rw [bind_apply, tsum_eq_single l fun a ha => ?_, bind_apply,
    tsum_eq_single r fun b hb => by simp [Ne.symm hb]]
  · simp
  · rw [bind_apply, ENNReal.tsum_eq_zero.2 fun b => by simp [Ne.symm ha], mul_zero]

/-- A tree with `k` internal nodes, and so `k + 1` leaves, has mass `p ^ (k + 1) (1 - p) ^ k`. The
unfolding determines it by induction on the tree, with no appeal to the least fixed point. -/
theorem genB_apply (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (t : BTree) :
    (genB p : SPMF BTree) t = pr p ^ (t.internal + 1) * (1 - pr p) ^ t.internal := by
  induction t with
  | leaf =>
    rw [genB, bind_apply, tsum_bool]
    simp only [Bool.false_eq_true, ↓reduceIte, coin_false hp0 hp1, coin_true hp0 hp1]
    rw [node_apply_leaf]
    simp [BTree.internal]
  | node l r ihl ihr =>
    rw [genB, bind_apply, tsum_bool]
    simp only [Bool.false_eq_true, ↓reduceIte, coin_false hp0 hp1, coin_true hp0 hp1]
    rw [node_apply_node, ihl, ihr]
    simp [BTree.internal]
    ring

theorem genB_node (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (l r : BTree) :
    (genB p : SPMF BTree) (.node l r)
      = (1 - pr p) * ((genB p : SPMF BTree) l * (genB p : SPMF BTree) r) := by
  rw [genB_apply hp0 hp1, genB_apply hp0 hp1, genB_apply hp0 hp1]
  simp only [BTree.internal]
  ring

/-- Uniform within each size. -/
theorem genB_uniform (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {s t : BTree} (h : s.size = t.size) :
    (genB p : SPMF BTree) s = (genB p : SPMF BTree) t := by
  have : s.internal = t.internal := by rw [BTree.size_eq, BTree.size_eq] at h; omega
  rw [genB_apply hp0 hp1, genB_apply hp0 hp1, this]

/-- **The Boltzmann form.** Any `B` solving the specification's equation `B = x + x B²`, with
`p = x / B`, gives each tree mass `x ^ |t| / B`; no closed form for `B(x)` is needed. -/
theorem genB_boltzmann (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {x B : ℝ≥0∞}
    (hB : B = x + x * B ^ 2) (hB0 : B ≠ 0) (hBtop : B ≠ ⊤) (hpx : pr p = x / B) (t : BTree) :
    (genB p : SPMF BTree) t = x ^ t.size / B := by
  have hBB : B * B⁻¹ = 1 := ENNReal.mul_inv_cancel hB0 hBtop
  have h1 : x / B + x * B = 1 := by
    have h := congrArg (· * B⁻¹) hB
    simp only [add_mul, hBB] at h
    calc x / B + x * B = x * B⁻¹ + x * B ^ 2 * B⁻¹ := by
          rw [div_eq_mul_inv, show x * B ^ 2 * B⁻¹ = x * B * (B * B⁻¹) by ring, hBB, mul_one]
      _ = 1 := h.symm
  have hq : 1 - pr p = x * B := by
    rw [hpx, ← h1, ENNReal.add_sub_cancel_left]
    exact ne_top_of_le_ne_top ENNReal.one_ne_top (h1 ▸ le_self_add)
  rw [genB_apply hp0 hp1, hq, hpx, BTree.size_eq, div_eq_mul_inv, div_eq_mul_inv]
  calc (x * B⁻¹) ^ (t.internal + 1) * (x * B) ^ t.internal
      = x ^ (2 * t.internal + 1) * B⁻¹ * (B * B⁻¹) ^ t.internal := by ring
    _ = x ^ (2 * t.internal + 1) * B⁻¹ := by rw [hBB, one_pow, mul_one]

theorem genB_terminates (hp : 1/2 ≤ p) (hp1 : p ≤ 1) :
    IsAlmostSurelyTerminating (genB p : SPMF BTree) := by
  have hp0 : 0 ≤ p := le_trans (by norm_num) hp
  have hx := half_le_pr hp
  have hx1 := pr_le_one hp0 hp1
  mass_fixpoint using SPMF.LfpIsOne.quadratic (a := pr p) (b := 0) (d := 1 - pr p)
    (by rw [add_zero, add_tsub_cancel_of_le hx1])
    (by basify; rw [max_eq_left (by linarith)]; linarith) (lt_of_lt_of_le (by norm_num) hx)
  all_goals first
    | exact p.den_pos
    | exact (coin_num_bounds hp0 hp1).1
    | exact (coin_num_bounds hp0 hp1).2
    | rw [pr_compl, show ((p.num.toNat : ℕ) : ℝ≥0∞) / p.den = pr p from rfl]; simp [sq]

end mass

section rejection

/-- The approximate-size window `[lo, hi]`. -/
def window (lo hi : Nat) (t : BTree) : Bool := decide (lo ≤ t.size ∧ t.size ≤ hi)

/-- §6.1's guarantee: rejection to a window keeps two trees of the same size equally likely. -/
theorem rejection_uniform (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {s t : BTree} (h : s.size = t.size) :
    (suchThat (genB p) (window lo hi) : SPMF BTree) s
      = (suchThat (genB p) (window lo hi) : SPMF BTree) t := by
  rw [suchThat_apply, suchThat_apply, genB_uniform hp0 hp1 h, window, window, h]

private theorem pr_four_fifths : pr (4 / 5) = 4 / 5 := by
  rw [pr]; norm_num

/-- Footnote 6: the output is not uniform across the window. At `p = 4/5` and the window `[1, 3]`,
the leaf is more likely than the tree of size `3`. -/
theorem rejection_not_uniform_across :
    (suchThat (genB (4/5)) (window 1 3) : SPMF BTree) .leaf
      ≠ (suchThat (genB (4/5)) (window 1 3) : SPMF BTree) (.node .leaf .leaf) := by
  have h0 : (0 : ℚ) ≤ 4 / 5 := by norm_num
  have h1 : (4 / 5 : ℚ) ≤ 1 := by norm_num
  have hne : (4 / 5 : ℝ≥0∞) ≠ ⊤ := ENNReal.div_ne_top (by norm_num) (by norm_num)
  have hlt1 : (4 / 5 : ℝ≥0∞) < 1 := ENNReal.div_lt_of_lt_mul (by norm_num)
  rw [suchThat_apply, suchThat_apply]
  set R := prob (genB (4/5) : SPMF BTree) {b | window 1 3 b = false}
  have hleaf : (genB (4/5) : SPMF BTree) .leaf = 4 / 5 := by
    rw [genB_apply h0 h1, pr_four_fifths]; simp [BTree.internal]
  have hR : R < 1 := by
    have hacc : 4 / 5 ≤ prob (genB (4/5) : SPMF BTree) {b | window 1 3 b = true} := by
      classical
      rw [prob_eq_tsum_ite, ← hleaf]
      refine le_trans ?_ (ENNReal.le_tsum BTree.leaf)
      simp [window, BTree.size]
    have hsum := (prob_accept_add_reject (genB (4/5) : SPMF BTree) (window 1 3)).le.trans
      (mass_le_one _)
    have : R + 4 / 5 ≤ 1 := by rw [add_comm]; exact le_trans (by gcongr) hsum
    exact lt_of_le_of_lt (ENNReal.le_sub_of_add_le_right hne this)
      (ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero (by norm_num))
  have hD0 : 1 - R ≠ 0 := (tsub_pos_of_lt hR).ne'
  have hDtop : 1 - R ≠ ⊤ := ENNReal.sub_ne_top ENNReal.one_ne_top
  simp only [show window 1 3 .leaf = true by decide,
    show window 1 3 (.node .leaf .leaf) = true by decide, ↓reduceIte]
  intro h
  have h := congrArg (· * (1 - R)) h
  simp only [ENNReal.div_mul_cancel hD0 hDtop] at h
  rw [hleaf, genB_apply h0 h1, pr_four_fifths] at h
  simp only [BTree.internal] at h
  have hlt : (4 / 5 : ℝ≥0∞) ^ (0 + 0 + 1 + 1) * (1 - 4 / 5) ^ (0 + 0 + 1) < 4 / 5 := by
    calc _ ≤ (4 / 5 : ℝ≥0∞) ^ 2 * 1 := by gcongr; exact pow_le_one₀ (by simp) tsub_le_self
      _ < 4 / 5 := by
        rw [mul_one, pow_two]
        exact ENNReal.mul_lt_of_lt_div (by rw [ENNReal.div_self (by norm_num) hne]; exact hlt1)
  exact hlt.ne h.symm

end rejection

section size

private theorem expect_bool (μ : SPMF Bool) (F : Bool → ℝ≥0∞) :
    expect μ F = μ false * F false + μ true * F true := by
  unfold expect; exact tsum_bool _

/-- One unfolding of `genB`, with `z` for the recursive calls. -/
theorem expect_genB_step (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (z : SPMF BTree) (f : BTree → ℝ≥0∞) :
    expect (coin p >>= fun b => if b = true then Pure.pure BTree.leaf
        else (z >>= fun l => z >>= fun r => Pure.pure (BTree.node l r))) f
      = pr p * f .leaf + (1 - pr p) * expect z (fun l => expect z fun r => f (.node l r)) := by
  rw [expect_bind, expect_bool, coin_false hp0 hp1, coin_true hp0 hp1, add_comm]
  simp only [↓reduceIte, Bool.false_eq_true, expect_pure, expect_bind]

private theorem expect_add_const (μ : SPMF α) (f : α → ℝ≥0∞) (c : ℝ≥0∞) :
    expect μ (fun a => f a + c) = expect μ f + μ.mass * c := by
  rw [expect_add, expect_const]

/-- The expected size of a node whose subtrees are drawn from `μ`. -/
private theorem expect_node_size (μ : SPMF BTree) :
    expect μ (fun l => expect μ fun r => ((BTree.node l r).size : ℝ≥0∞))
      = expect μ (fun t => (t.size : ℝ≥0∞)) * μ.mass
        + μ.mass * (μ.mass + expect μ (fun t => (t.size : ℝ≥0∞))) := by
  simp only [BTree.size, Nat.cast_add, Nat.cast_one]
  have : ∀ l : BTree, expect μ (fun r => (l.size : ℝ≥0∞) + r.size + 1)
      = μ.mass * l.size + (μ.mass + expect μ (fun t => (t.size : ℝ≥0∞))) := by
    intro l
    rw [show (fun r : BTree => (l.size : ℝ≥0∞) + r.size + 1)
        = fun r => (r.size : ℝ≥0∞) + (l.size + 1) by funext r; ring, expect_add_const]
    ring
  simp only [this]
  rw [expect_add_const, expect_mul_left, mul_comm]

private theorem two_mul_sub_one_ne_zero {x : ℝ≥0∞} (hx : 1/2 < x) : 2 * x - 1 ≠ 0 := by
  refine (tsub_pos_of_lt ?_).ne'
  calc (1 : ℝ≥0∞) = 2 * (1 / 2) := by rw [ENNReal.mul_div_cancel (by norm_num) (by norm_num)]
    _ < 2 * x := by gcongr; norm_num

private theorem two_mul_sub_one_ne_top {x : ℝ≥0∞} (hx1 : x ≤ 1) : 2 * x - 1 ≠ ⊤ :=
  ENNReal.sub_ne_top (ENNReal.mul_ne_top (by norm_num) (ne_top_of_le_ne_top ENNReal.one_ne_top hx1))

private theorem two_mul_sub_one_add {x : ℝ≥0∞} (hx : 1/2 < x) (hx1 : x ≤ 1) :
    (2 * x - 1) + 2 * (1 - x) = 1 := by
  basify
  rw [max_eq_left (by linarith), max_eq_left (by linarith)]; ring

/-- `E₀ = 1 / (2x - 1)` solves `E = x + (1 - x)(2E + 1)`. -/
private theorem size_fixpoint {x : ℝ≥0∞} (hx : 1/2 < x) (hx1 : x ≤ 1) :
    x + (1 - x) * (1 / (2 * x - 1) + (1 + 1 / (2 * x - 1))) = 1 / (2 * x - 1) := by
  have h3 : 1 / (2 * x - 1) * (2 * x - 1) = 1 :=
    ENNReal.div_mul_cancel (two_mul_sub_one_ne_zero hx) (two_mul_sub_one_ne_top hx1)
  calc x + (1 - x) * (1 / (2 * x - 1) + (1 + 1 / (2 * x - 1)))
      = (x + (1 - x)) + 1 / (2 * x - 1) * (2 * (1 - x)) := by ring
    _ = 1 / (2 * x - 1) * (2 * x - 1) + 1 / (2 * x - 1) * (2 * (1 - x)) := by
        rw [add_tsub_cancel_of_le hx1, h3]
    _ = 1 / (2 * x - 1) := by rw [← mul_add, two_mul_sub_one_add hx hx1, mul_one]

/-- The upper bound, by fixpoint induction: `E₀` bounds every approximant. This is the step that
rules out the other solution of the unfolding, `E = ⊤`. -/
theorem genB_expected_size_le (hp : 1/2 < p) (hp1 : p ≤ 1) :
    expect (genB p : SPMF BTree) (fun t => (t.size : ℝ≥0∞)) ≤ 1 / (2 * pr p - 1) := by
  have hp0 : 0 ≤ p := le_trans (by norm_num) hp.le
  refine genB.fixpoint_induct (G := SPMF) p _ (admissible_expect_le _ _) fun z hz => ?_
  rw [expect_genB_step hp0 hp1, expect_node_size]
  have hm := mass_le_one z
  calc pr p * (BTree.leaf.size : ℝ≥0∞) + (1 - pr p) * (expect z (fun t => (t.size : ℝ≥0∞))
        * z.mass + z.mass * (z.mass + expect z (fun t => (t.size : ℝ≥0∞))))
      ≤ pr p * 1 + (1 - pr p) * (1 / (2 * pr p - 1) * 1 + 1 * (1 + 1 / (2 * pr p - 1))) := by
        simp only [BTree.size, Nat.cast_one]; gcongr
    _ = 1 / (2 * pr p - 1) := by
        simp only [mul_one, one_mul]; exact size_fixpoint (half_lt_pr hp) (pr_le_one hp0 hp1)

/-- Unfolded once, with the subtrees terminating: `E = x + (1 - x)(2E + 1)`. -/
theorem genB_expected_size_step (hp : 1/2 ≤ p) (hp1 : p ≤ 1) :
    expect (genB p : SPMF BTree) (fun t => (t.size : ℝ≥0∞))
      = pr p + (1 - pr p) * (expect (genB p : SPMF BTree) (fun t => (t.size : ℝ≥0∞))
        + (1 + expect (genB p : SPMF BTree) (fun t => (t.size : ℝ≥0∞)))) := by
  have hp0 : 0 ≤ p := le_trans (by norm_num) hp
  have hm : (genB p : SPMF BTree).mass = 1 := genB_terminates hp hp1
  conv_lhs => rw [genB]
  rw [expect_genB_step hp0 hp1, expect_node_size, hm]
  simp [BTree.size]

/-- **Proposition 2.1, for binary trees**: the expected size is `x B'(x) / B(x) = 1 / (2p - 1)`. -/
theorem genB_expected_size (hp : 1/2 < p) (hp1 : p ≤ 1) :
    expect (genB p : SPMF BTree) (fun t => (t.size : ℝ≥0∞)) = 1 / (2 * pr p - 1) := by
  have hx := half_lt_pr hp
  have hx1 := pr_le_one (le_trans (by norm_num) hp.le) hp1
  have hstep := genB_expected_size_step hp.le hp1
  have hle := genB_expected_size_le hp hp1
  set E := expect (genB p : SPMF BTree) (fun t => (t.size : ℝ≥0∞))
  set x := pr p
  have hD0 := two_mul_sub_one_ne_zero hx
  have hE : E ≠ ⊤ := ne_top_of_le_ne_top (ENNReal.div_ne_top ENNReal.one_ne_top hD0) hle
  rw [ENNReal.eq_div_iff hD0 (two_mul_sub_one_ne_top hx1)]
  have hc : 2 * (1 - x) * E ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) (ENNReal.sub_ne_top ENNReal.one_ne_top)) hE
  refine (ENNReal.add_left_inj hc).1 ?_
  calc (2 * x - 1) * E + 2 * (1 - x) * E = E := by
        rw [← add_mul, two_mul_sub_one_add hx hx1, one_mul]
    _ = (x + (1 - x)) + 2 * (1 - x) * E := by
        conv_lhs => rw [hstep]
        ring
    _ = 1 + 2 * (1 - x) * E := by rw [add_tsub_cancel_of_le hx1]

/-- The critical case: the sampler terminates almost surely, but its expected size is infinite. -/
theorem genB_expected_size_critical :
    expect (genB (1/2) : SPMF BTree) (fun t => (t.size : ℝ≥0∞)) = ⊤ := by
  have hstep := genB_expected_size_step (p := 1/2) le_rfl (by norm_num)
  have hhalf : pr (1/2) = 1/2 := by rw [pr]; norm_num
  rw [hhalf, show (1 : ℝ≥0∞) - 1 / 2 = 1 / 2 by rw [one_div, ENNReal.one_sub_inv_two]] at hstep
  set E := expect (genB (1/2) : SPMF BTree) (fun t => (t.size : ℝ≥0∞))
  by_contra hE
  have h : E + 0 = E + 1 :=
    calc E + 0 = 1 / 2 + 1 / 2 * (E + (1 + E)) := by rw [add_zero]; exact hstep
      _ = E * (1 / 2 + 1 / 2) + (1 / 2 + 1 / 2) := by ring
      _ = E + 1 := by rw [ENNReal.add_halves, mul_one]
  exact zero_ne_one ((ENNReal.add_right_inj hE).1 h)

end size

end Boltzmann
