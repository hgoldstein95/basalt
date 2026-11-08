/-
Copyright (c) 2026 Ernest Ng. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Ernest Ng
-/
module

import Mathlib.Tactic.Basify
public import Basalt

/-!
# Boltzmann Samplers

Duchon, Flajolet, Louchard and Schaeffer, "Boltzmann Samplers for the Random Generation of
Combinatorial Structures" (CPC 2004): the ordinary Boltzmann model (§2), and the sampler for binary
trees (Example 2) with its leaf probability `p = x / B(x)` as a parameter. Every tree of size `n`
gets mass `x ^ n / B(x)`, so the sampler is uniform within each size; its expected size
`1 / (2p - 1)` above the critical `p = 1/2`, and its mass `p / (1 - p)` below it, are proved by
fixpoint induction rather than from the generating function.
-/

@[expose] public section

open RandomChoice SPMF
open scoped ENNReal

namespace Boltzmann

section model

variable {α β : Type}

/-- **The ordinary Boltzmann model** of parameter `x` (§2): each object `γ` of a class with size
function `size` and generating function value `C = C(x)` has mass `x ^ |γ| / C`. -/
def IsBoltzmann (μ : SPMF α) (size : α → ℕ) (x C : ℝ≥0∞) : Prop :=
  ∀ a, μ a = x ^ size a / C

/-- Uniform within each size, the model's point. -/
theorem IsBoltzmann.uniform {μ : SPMF α} {size : α → ℕ} {x C : ℝ≥0∞} (h : IsBoltzmann μ size x C)
    {a b : α} (hab : size a = size b) : μ a = μ b := by
  rw [h, h, hab]

end model

section reject

variable {α : Type}

/-- Retrying a round that may fail (`none`) until it succeeds, as rejection sampling: its law is the
round's, renormalized by the rounds that fail. -/
theorem getD_suchThat_isSome_apply (h : SPMF (Option α)) (d a : α) :
    ((fun o => o.getD d) <$> suchThat h Option.isSome : SPMF α) a = h (some a) / (1 - h none) := by
  classical
  have hrej : prob h {o | o.isSome = false} = h none := by
    rw [show {o : Option α | o.isSome = false} = {none} by ext o; cases o <;> simp, prob_singleton]
  rw [map_eq_pure_bind, bind_apply, tsum_option, suchThat_apply, hrej,
    tsum_eq_single a fun b hb => by simp [Ne.symm hb]]
  simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, zero_mul, zero_add,
    Option.getD_some, pure_apply, mul_one]
  rw [suchThat_apply, hrej]
  simp

end reject

/-- Binary trees: `B = Z + Z × B × B`. -/
inductive BinaryTree where
  | leaf
  | node (l r : BinaryTree)
deriving DecidableEq

/-- The number of internal nodes. -/
def BinaryTree.internal : BinaryTree → Nat
  | .leaf => 0
  | .node l r => l.internal + r.internal + 1

/-- The size of a tree: every node, internal or leaf, is one atom. -/
def BinaryTree.size : BinaryTree → Nat
  | .leaf => 1
  | .node l r => l.size + r.size + 1

theorem BinaryTree.size_eq (t : BinaryTree) : t.size = 2 * t.internal + 1 := by
  induction t with
  | leaf => rfl
  | node l r ihl ihr => simp only [BinaryTree.size, BinaryTree.internal, ihl, ihr]; omega

/-- The probability `coin p` lands `true`. -/
noncomputable def pr (p : Rat) : ℝ≥0∞ := (p.num.toNat : ℝ≥0∞) / (p.den : ℝ≥0∞)

/-- `Γ B(x)`, with `p = x / B(x)`: a leaf with probability `p`, else a node and two recursive
calls. -/
def genBinaryTree [Gen G] (p : Rat) : G BinaryTree := do
  if ← coin p then return .leaf
  else return .node (← genBinaryTree p) (← genBinaryTree p)
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

theorem pr_mono (hq : 0 ≤ q) (h : q ≤ p) : pr q ≤ pr p := by
  rw [pr_eq_ofReal hq, pr_eq_ofReal (hq.trans h)]
  exact ENNReal.ofReal_le_ofReal (by exact_mod_cast h)

theorem pr_strictMono (hq : 0 ≤ q) (h : q < p) : pr q < pr p := by
  rw [pr_eq_ofReal hq, pr_eq_ofReal (hq.trans h.le)]
  exact (ENNReal.ofReal_lt_ofReal_iff (by exact_mod_cast hq.trans_lt h)).2 (by exact_mod_cast h)

theorem pr_half : pr (1/2) = 1/2 := by rw [pr]; norm_num

theorem half_le_pr (hp : 1/2 ≤ p) : 1/2 ≤ pr p := pr_half ▸ pr_mono (by norm_num) hp

theorem half_lt_pr (hp : 1/2 < p) : 1/2 < pr p := pr_half ▸ pr_strictMono (by norm_num) hp

theorem pr_lt_half (hp0 : 0 ≤ p) (hp : p < 1/2) : pr p < 1/2 := pr_half ▸ pr_strictMono hp0 hp

/-- Closes the side goals `mass_fixpoint` leaves about a draw from `coin p`, given `0 ≤ p` and
`p ≤ 1`, and states the coin's two probabilities as `pr p` and `1 - pr p` in the goal it leaves. -/
macro "coin_goals " p:term:max hp0:term:max hp1:term:max : tactic =>
  `(tactic| all_goals first
    | exact ($p).den_pos
    | exact (coin_num_bounds $hp0 $hp1).1
    | exact (coin_num_bounds $hp0 $hp1).2
    | rw [pr_compl, show ((($p).num.toNat : ℕ) : ℝ≥0∞) / ($p).den = pr $p from rfl])

end coin

section mass

/-- A tree with `k` internal nodes, and so `k + 1` leaves, has mass `p ^ (k + 1) (1 - p) ^ k`. The
unfolding determines it by induction on the tree, with no appeal to the least fixed point. -/
theorem genBinaryTree_apply (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (t : BinaryTree) :
    (genBinaryTree p : SPMF BinaryTree) t = pr p ^ (t.internal + 1) * (1 - pr p) ^ t.internal := by
  induction t with
  | leaf =>
    rw [genBinaryTree, bind_apply, tsum_bool]
    simp only [Bool.false_eq_true, ↓reduceIte, coin_false hp0 hp1, coin_true hp0 hp1]
    rw [(apply_eq_zero_iff _ BinaryTree.leaf).2 (by simp)]
    simp [BinaryTree.internal]
  | node l r ihl ihr =>
    rw [genBinaryTree, bind_apply, tsum_bool]
    simp only [Bool.false_eq_true, ↓reduceIte, coin_false hp0 hp1, coin_true hp0 hp1]
    rw [bind_apply_of_unique l (by simp), bind_apply_of_unique r (by simp), ihl, ihr]
    simp [BinaryTree.internal]
    ring

/-- Uniform within each size. -/
theorem genBinaryTree_uniform (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {s t : BinaryTree} (h : s.size = t.size) :
    (genBinaryTree p : SPMF BinaryTree) s = (genBinaryTree p : SPMF BinaryTree) t := by
  have : s.internal = t.internal := by rw [BinaryTree.size_eq, BinaryTree.size_eq] at h; omega
  rw [genBinaryTree_apply hp0 hp1, genBinaryTree_apply hp0 hp1, this]

/-- **The Boltzmann form.** Any `B` solving the specification's equation `B = x + x B²`, with
`p = x / B`, gives each tree mass `x ^ |t| / B`; no closed form for `B(x)` is needed. -/
theorem genBinaryTree_boltzmann (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {x B : ℝ≥0∞}
    (hB : B = x + x * B ^ 2) (hB0 : B ≠ 0) (hBtop : B ≠ ⊤) (hpx : pr p = x / B) (t : BinaryTree) :
    (genBinaryTree p : SPMF BinaryTree) t = x ^ t.size / B := by
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
  rw [genBinaryTree_apply hp0 hp1, hq, hpx, BinaryTree.size_eq, div_eq_mul_inv, div_eq_mul_inv]
  calc (x * B⁻¹) ^ (t.internal + 1) * (x * B) ^ t.internal
      = x ^ (2 * t.internal + 1) * B⁻¹ * (B * B⁻¹) ^ t.internal := by ring
    _ = x ^ (2 * t.internal + 1) * B⁻¹ := by rw [hBB, one_pow, mul_one]

theorem genBinaryTree_terminates (hp : 1/2 ≤ p) (hp1 : p ≤ 1) :
    IsAlmostSurelyTerminating (genBinaryTree p : SPMF BinaryTree) := by
  have hp0 : 0 ≤ p := le_trans (by norm_num) hp
  have hx := half_le_pr hp
  have hx1 := pr_le_one hp0 hp1
  mass_fixpoint using SPMF.LfpIsOne.quadratic (a := pr p) (b := 0) (d := 1 - pr p)
    (by rw [add_zero, add_tsub_cancel_of_le hx1])
    (by basify; rw [max_eq_left (by linarith)]; linarith) (lt_of_lt_of_le (by norm_num) hx)
  coin_goals p hp0 hp1
  simp [sq]

end mass

section size

theorem expect_bool (μ : SPMF Bool) (F : Bool → ℝ≥0∞) :
    expect μ F = μ false * F false + μ true * F true := by
  unfold expect; exact tsum_bool _

/-- One unfolding of `genBinaryTree`, with `z` for the recursive calls. -/
theorem expect_genBinaryTree_step (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (z : SPMF BinaryTree)
    (f : BinaryTree → ℝ≥0∞) :
    expect (coin p >>= fun b => if b = true then Pure.pure BinaryTree.leaf
        else (z >>= fun l => z >>= fun r => Pure.pure (BinaryTree.node l r))) f
      = pr p * f .leaf + (1 - pr p) * expect z (fun l => expect z fun r => f (.node l r)) := by
  rw [expect_bind, expect_bool, coin_false hp0 hp1, coin_true hp0 hp1, add_comm]
  simp only [↓reduceIte, Bool.false_eq_true, expect_pure, expect_bind]

/-- The expected size of a node whose subtrees are drawn from `μ`. -/
private theorem expect_node_size (μ : SPMF BinaryTree) :
    expect μ (fun l => expect μ fun r => ((BinaryTree.node l r).size : ℝ≥0∞))
      = expect μ (fun t => (t.size : ℝ≥0∞)) * μ.mass
        + μ.mass * (μ.mass + expect μ (fun t => (t.size : ℝ≥0∞))) := by
  simp only [BinaryTree.size, Nat.cast_add, Nat.cast_one]
  have : ∀ l : BinaryTree, expect μ (fun r => (l.size : ℝ≥0∞) + r.size + 1)
      = μ.mass * l.size + (μ.mass + expect μ (fun t => (t.size : ℝ≥0∞))) := by
    intro l
    rw [show (fun r : BinaryTree => (l.size : ℝ≥0∞) + r.size + 1)
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
theorem genBinaryTree_expected_size_le (hp : 1/2 < p) (hp1 : p ≤ 1) :
    expect (genBinaryTree p : SPMF BinaryTree) (fun t => (t.size : ℝ≥0∞)) ≤ 1 / (2 * pr p - 1) := by
  have hp0 : 0 ≤ p := le_trans (by norm_num) hp.le
  refine genBinaryTree.fixpoint_induct (G := SPMF) p _ (admissible_expect_le _ _) fun z hz => ?_
  rw [expect_genBinaryTree_step hp0 hp1, expect_node_size]
  have hm := mass_le_one z
  calc pr p * (BinaryTree.leaf.size : ℝ≥0∞) + (1 - pr p) * (expect z (fun t => (t.size : ℝ≥0∞))
        * z.mass + z.mass * (z.mass + expect z (fun t => (t.size : ℝ≥0∞))))
      ≤ pr p * 1 + (1 - pr p) * (1 / (2 * pr p - 1) * 1 + 1 * (1 + 1 / (2 * pr p - 1))) := by
        simp only [BinaryTree.size, Nat.cast_one]; gcongr
    _ = 1 / (2 * pr p - 1) := by
        simp only [mul_one, one_mul]; exact size_fixpoint (half_lt_pr hp) (pr_le_one hp0 hp1)

/-- Unfolded once, with the subtrees terminating: `E = x + (1 - x)(2E + 1)`. -/
theorem genBinaryTree_expected_size_step (hp : 1/2 ≤ p) (hp1 : p ≤ 1) :
    expect (genBinaryTree p : SPMF BinaryTree) (fun t => (t.size : ℝ≥0∞))
      = pr p + (1 - pr p) * (expect (genBinaryTree p : SPMF BinaryTree) (fun t => (t.size : ℝ≥0∞))
        + (1 + expect (genBinaryTree p : SPMF BinaryTree) (fun t => (t.size : ℝ≥0∞)))) := by
  have hp0 : 0 ≤ p := le_trans (by norm_num) hp
  have hm : (genBinaryTree p : SPMF BinaryTree).mass = 1 := genBinaryTree_terminates hp hp1
  conv_lhs => rw [genBinaryTree]
  rw [expect_genBinaryTree_step hp0 hp1, expect_node_size, hm]
  simp [BinaryTree.size]

/-- **Proposition 2.1, for binary trees**: the expected size is `x B'(x) / B(x) = 1 / (2p - 1)`. -/
theorem genBinaryTree_expected_size (hp : 1/2 < p) (hp1 : p ≤ 1) :
    expect (genBinaryTree p : SPMF BinaryTree) (fun t => (t.size : ℝ≥0∞)) = 1 / (2 * pr p - 1) := by
  have hx := half_lt_pr hp
  have hx1 := pr_le_one (le_trans (by norm_num) hp.le) hp1
  have hstep := genBinaryTree_expected_size_step hp.le hp1
  have hle := genBinaryTree_expected_size_le hp hp1
  set E := expect (genBinaryTree p : SPMF BinaryTree) (fun t => (t.size : ℝ≥0∞))
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

end size

section supercritical

/-- One unfolding of the mass: `m = x + (1 - x) m²`. -/
theorem genBinaryTree_mass_step (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (genBinaryTree p : SPMF BinaryTree).mass
      = pr p + (1 - pr p) * (genBinaryTree p : SPMF BinaryTree).mass ^ 2 := by
  rw [← expect_one]
  conv_lhs => rw [genBinaryTree]
  rw [expect_genBinaryTree_step hp0 hp1]
  simp [expect_const, sq]

/-- `B = x / (1 - x)` solves `B = x + (1 - x) B²`, the root below `1` when `x < 1/2`. -/
private theorem small_root {x : ℝ≥0∞} (hx : x < 1/2) :
    x + (1 - x) * (x / (1 - x)) ^ 2 = x / (1 - x) := by
  have hx1 : x < 1 := hx.trans (by norm_num)
  have hy0 : 1 - x ≠ 0 := (tsub_pos_of_lt hx1).ne'
  have hytop : 1 - x ≠ ⊤ := ENNReal.sub_ne_top ENNReal.one_ne_top
  have hB : x / (1 - x) * (1 - x) = x := ENNReal.div_mul_cancel hy0 hytop
  calc x + (1 - x) * (x / (1 - x)) ^ 2 = x / (1 - x) * (1 - x) + x / (1 - x) * x := by
        rw [hB, sq, ← mul_assoc, mul_comm (1 - x), hB, mul_comm]
    _ = x / (1 - x) := by rw [← mul_add, tsub_add_cancel_of_le hx1.le, mul_one]

/-- The upper bound, by fixpoint induction: every approximant has mass at most `x / (1 - x)`. -/
theorem genBinaryTree_mass_le (hp0 : 0 ≤ p) (hp : p < 1/2) :
    (genBinaryTree p : SPMF BinaryTree).mass ≤ pr p / (1 - pr p) := by
  have hp1 : p ≤ 1 := hp.le.trans (by norm_num)
  have hx := pr_lt_half hp0 hp
  rw [← expect_one]
  refine genBinaryTree.fixpoint_induct (G := SPMF) p _ (admissible_expect_le _ _) fun z hz => ?_
  rw [expect_genBinaryTree_step hp0 hp1]
  simp only [expect_const, mul_one]
  calc pr p + (1 - pr p) * (z.mass * z.mass)
      ≤ pr p + (1 - pr p) * (pr p / (1 - pr p) * (pr p / (1 - pr p))) := by
        rw [← expect_one] at *; gcongr
    _ = pr p / (1 - pr p) := by rw [← sq]; exact small_root hx

/-- **Supercritical binary trees**: for `p < 1/2` the sampler halts with probability `p / (1 - p)`,
the smaller root of its mass equation. Every tree still gets `p ^ (k + 1) (1 - p) ^ k`
(`genBinaryTree_apply`), which is `x ^ |t| / B` for `x = √(p (1 - p))` and `B = x / p`, the *larger*
root of `B = x + x B²` (`genBinaryTree_boltzmann` holds of either root): the pointwise equations
cannot tell the two apart, only the least fixed point can. -/
theorem genBinaryTree_mass_supercritical (hp0 : 0 ≤ p) (hp : p < 1/2) :
    (genBinaryTree p : SPMF BinaryTree).mass = pr p / (1 - pr p) := by
  have hp1 : p ≤ 1 := hp.le.trans (by norm_num)
  have hx := pr_lt_half hp0 hp
  have hle := genBinaryTree_mass_le hp0 hp
  have hstep := (genBinaryTree_mass_step hp0 hp1).symm.le
  have hx1 : pr p < 1 := hx.trans (by norm_num)
  have hy0 : 1 - pr p ≠ 0 := (tsub_pos_of_lt hx1).ne'
  have hB := ENNReal.div_mul_cancel (b := pr p) hy0 (ENNReal.sub_ne_top ENNReal.one_ne_top)
  have hxx : pr p + pr p < 1 := (ENNReal.add_lt_add hx hx).trans_eq (ENNReal.add_halves 1)
  have hxy : pr p ≤ 1 - pr p := ENNReal.le_sub_of_add_le_left hx1.ne_top hxx.le
  have hB1 : pr p / (1 - pr p) ≤ 1 := ENNReal.div_le_of_le_mul (by rwa [one_mul])
  have hm1 := mass_le_one (genBinaryTree p : SPMF BinaryTree)
  clear hy0 hx1 hp0 hp hp1 hx
  generalize (genBinaryTree p : SPMF BinaryTree).mass = m at *
  generalize pr p / (1 - pr p) = B at *
  generalize pr p = x at *
  basify
  rw [max_eq_left (by linarith)] at hstep hB
  -- `(1-x)(m-1)(m-B) = (1-x)m² - m + x ≤ 0`, with `m < 1`
  have hBlt : B < 1 := by nlinarith
  refine le_antisymm hle (not_lt.1 fun hlt => ?_)
  nlinarith [mul_pos (mul_pos (show (0 : ℝ) < 1 - x by linarith) (sub_pos.2 hlt))
    (show (0 : ℝ) < 1 - m by linarith)]

/-- **Example 2 at `x = 2/5`**: `B(2/5) = 1/2`, so `p = x / B(x) = 4/5`, and the expected size
`x B'(x) / B(x) = 1 / (2p - 1)` is `5/3`. -/
theorem genBinaryTree_expected_size_two_fifths :
    expect (genBinaryTree (4/5) : SPMF BinaryTree) (fun t => (t.size : ℝ≥0∞)) = 5 / 3 := by
  rw [genBinaryTree_expected_size (by norm_num) (by norm_num),
    show pr (4/5) = 4/5 by rw [pr]; norm_num]
  have h : (2 : ℝ≥0∞) * (4 / 5) - 1 = 3 / 5 := by basify; norm_num
  rw [h, one_div, ENNReal.inv_div (by simp) (by simp)]

end supercritical

end Boltzmann
