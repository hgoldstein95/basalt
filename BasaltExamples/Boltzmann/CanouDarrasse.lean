/-
Copyright (c) 2026 Ernest Ng. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Ernest Ng
-/
module

import Mathlib.Tactic.Basify
public import Basalt
public import BasaltExamples.Boltzmann.Rules

/-!
# Singular Boltzmann Samplers for Trees

The three tree samplers of Canou and Darrasse, "Fast and Sound Random Generation for Automated
Testing and Benchmarking in Objective Caml" (ML '09, Figs. 1–3), run at the singularity `x = ρ`,
where every branching probability is rational and every sampler is critical: each is uniform within
a size, terminates almost surely, and has infinite expected size. Their abort-and-retry sampler
(§3.3) is uniform within a size and biased towards small sizes.
-/

@[expose] public section

open RandomChoice SPMF
open scoped ENNReal

namespace Boltzmann.CanouDarrasse

/-! ## Ternary trees: `T = Z + T × T × T`

Fig. 1's grammar puts the atom `Z` only at leaves, so `|t|` counts leaves, though §3.2 says "the
size of a tree is its number of nodes". At `ρ = 2√3/9`, `T(ρ) = 1/√3` and the leaf probability is
`ρ / T(ρ) = 2/3`. -/

/-- Ternary trees. -/
inductive TTree where
  | leaf
  | node (a b c : TTree)
deriving DecidableEq

/-- The size of Fig. 1's grammar: the number of leaves. -/
def TTree.size : TTree → Nat
  | .leaf => 1
  | .node a b c => a.size + b.size + c.size

/-- The number of internal nodes. -/
def TTree.internal : TTree → Nat
  | .leaf => 0
  | .node a b c => a.internal + b.internal + c.internal + 1

theorem TTree.size_eq (t : TTree) : t.size = 2 * t.internal + 1 := by
  induction t with
  | leaf => rfl
  | node a b c iha ihb ihc => simp only [TTree.size, TTree.internal, iha, ihb, ihc]; omega

/-- Fig. 3's `TTree ()`: a leaf with probability `p = x / T(x)`, else a node of three draws. -/
def genTernary [Gen G] (p : Rat) : G TTree := do
  if ← coin p then return .leaf
  else return .node (← genTernary p) (← genTernary p) (← genTernary p)
partial_fixpoint

/-- A tree with `k` internal nodes, so `2k + 1` leaves, has mass `p ^ (2k + 1) (1 - p) ^ k`. -/
theorem genTernary_apply (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (t : TTree) :
    (genTernary p : SPMF TTree) t = pr p ^ t.size * (1 - pr p) ^ t.internal := by
  induction t with
  | leaf =>
    rw [genTernary, bind_apply, tsum_bool]
    simp only [Bool.false_eq_true, ↓reduceIte, coin_false hp0 hp1, coin_true hp0 hp1]
    rw [bind3_pure_apply_of_ne (f := TTree.node) _ _ _ fun _ _ _ => TTree.noConfusion]
    simp [TTree.size, TTree.internal]
  | node a b c iha ihb ihc =>
    rw [genTernary, bind_apply, tsum_bool]
    simp only [Bool.false_eq_true, ↓reduceIte, coin_false hp0 hp1, coin_true hp0 hp1]
    rw [bind3_pure_apply_of_injective (f := TTree.node) (fun _ _ _ _ _ _ h => TTree.node.inj h),
      iha, ihb, ihc]
    simp only [pure_apply, reduceCtorEq, ↓reduceIte, mul_zero, add_zero, TTree.size,
      TTree.internal]
    ring

/-- **Uniform within each size**, for every leaf probability. -/
theorem genTernary_uniform (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {s t : TTree} (h : s.size = t.size) :
    (genTernary p : SPMF TTree) s = (genTernary p : SPMF TTree) t := by
  have : s.internal = t.internal := by rw [TTree.size_eq, TTree.size_eq] at h; omega
  rw [genTernary_apply hp0 hp1, genTernary_apply hp0 hp1, h, this]

/-- **The Boltzmann form.** Any `T` solving `T = x + T³`, with `p = x / T`, gives each tree the mass
`x ^ |t| / T`. -/
theorem genTernary_boltzmann (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {x T : ℝ≥0∞} (hT : T = x + T ^ 3)
    (hT0 : T ≠ 0) (hTtop : T ≠ ⊤) (hpx : pr p = x / T) :
    IsBoltzmann (genTernary p : SPMF TTree) TTree.size x T := by
  intro t
  have hTT : T * T⁻¹ = 1 := ENNReal.mul_inv_cancel hT0 hTtop
  have h1 : x / T + T ^ 2 = 1 := by
    have h := congrArg (· * T⁻¹) hT
    simp only [add_mul, hTT] at h
    calc x / T + T ^ 2 = x * T⁻¹ + T ^ 3 * T⁻¹ := by
          rw [div_eq_mul_inv, show T ^ 3 * T⁻¹ = T ^ 2 * (T * T⁻¹) by ring, hTT, mul_one]
      _ = 1 := h.symm
  have hq : 1 - pr p = T ^ 2 := by
    rw [hpx, ← h1, ENNReal.add_sub_cancel_left]
    exact ne_top_of_le_ne_top ENNReal.one_ne_top (h1 ▸ le_self_add)
  rw [genTernary_apply hp0 hp1, hq, hpx, TTree.size_eq, div_eq_mul_inv, div_eq_mul_inv]
  calc (x * T⁻¹) ^ (2 * t.internal + 1) * (T ^ 2) ^ t.internal
      = x ^ (2 * t.internal + 1) * T⁻¹ * (T * T⁻¹) ^ (2 * t.internal) := by ring
    _ = x ^ (2 * t.internal + 1) * T⁻¹ := by rw [hTT, one_pow, mul_one]

/-- At `ρ`: a tree with `k` internal nodes has mass `(2/3) (4/27) ^ k = (2/3) ρ ^ 2k`. -/
theorem genTernary_singular_apply (t : TTree) :
    (genTernary (2/3) : SPMF TTree) t = 2 / 3 * (4 / 27) ^ t.internal := by
  rw [genTernary_apply (by norm_num) (by norm_num), show pr (2/3) = 2/3 by rw [pr]; norm_num,
    TTree.size_eq, pow_succ, pow_mul, mul_right_comm, ← mul_pow, mul_comm]
  congr 2
  basify; norm_num

theorem pr_two_thirds : pr (2/3) = 2/3 := by rw [pr]; norm_num

private theorem one_sub_two_thirds : (1 : ℝ≥0∞) - 2 / 3 = 1 / 3 := by basify; norm_num

private theorem two_thirds_lt_one : (2/3 : ℝ≥0∞) < 1 := ENNReal.div_lt_of_lt_mul (by norm_num)

/-- One unfolding of `genTernary`, with `z` for the recursive calls. -/
theorem expect_genTernary_step (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (z : SPMF TTree) (f : TTree → ℝ≥0∞) :
    expect (coin p >>= fun b => if b = true then Pure.pure TTree.leaf
        else (z >>= fun a => z >>= fun b => z >>= fun c => Pure.pure (TTree.node a b c))) f
      = pr p * f .leaf
        + (1 - pr p) * expect z (fun a => expect z fun b => expect z fun c => f (.node a b c)) := by
  rw [expect_bind, expect_bool, coin_false hp0 hp1, coin_true hp0 hp1, add_comm]
  simp only [↓reduceIte, Bool.false_eq_true, expect_pure, expect_bind]

/-- One unfolding of the mass: `m = x + (1 - x) m³`. -/
theorem genTernary_mass_step (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (z : SPMF TTree) :
    expect (coin p >>= fun b => if b = true then Pure.pure TTree.leaf
        else (z >>= fun a => z >>= fun b => z >>= fun c => Pure.pure (TTree.node a b c)))
        (fun _ => 1)
      = pr p + (1 - pr p) * z.mass ^ 3 := by
  rw [expect_genTernary_step hp0 hp1]
  simp only [expect_const, mul_one]
  ring

/-- **Terminates almost surely at and above the critical leaf probability `2/3`**: the mean number
of children, `3 (1 - p)`, is at most `1`. -/
theorem genTernary_terminates (hp : 2/3 ≤ p) (hp1 : p ≤ 1) :
    IsAlmostSurelyTerminating (genTernary p : SPMF TTree) := by
  have hp0 : 0 ≤ p := le_trans (by norm_num) hp
  have hx : 2/3 ≤ pr p := pr_two_thirds ▸ pr_mono (by norm_num) hp
  have hx1 := pr_le_one hp0 hp1
  mass_fixpoint using SPMF.LfpIsOne.cubic (a := pr p) (b := 0) (d := 0) (e := 1 - pr p)
    (by rw [add_zero, add_zero, add_tsub_cancel_of_le hx1])
    (by basify; rw [max_eq_left (by linarith)]; linarith) (lt_of_lt_of_le (by norm_num) hx)
  coin_goals p hp0 hp1
  exact le_of_eq (by ring)

/-- Below `2/3` the mass is at most `1 / (3 (1 - p))`: by fixpoint induction, as
`x + (1 - x) t³ ≤ t` at `t = 1 / (3 (1 - x))` with slack `(3 (1 - x) - 1)³ / (27 (1 - x)²)`. -/
theorem genTernary_mass_le (hp0 : 0 ≤ p) (hp : p < 2/3) :
    (genTernary p : SPMF TTree).mass ≤ (3 * (1 - pr p))⁻¹ := by
  have hp1 : p ≤ 1 := hp.le.trans (by norm_num)
  have hx : pr p < 2/3 := pr_two_thirds ▸ pr_strictMono hp0 hp
  rw [← expect_one]
  refine genTernary.fixpoint_induct (G := SPMF) p _ (admissible_expect_le _ _) fun z hz => ?_
  rw [genTernary_mass_step hp0 hp1]
  rw [expect_one] at hz
  have hq0 : 3 * (1 - pr p) ≠ 0 := by
    refine mul_ne_zero (by norm_num) (tsub_pos_of_lt (hx.trans two_thirds_lt_one)).ne'
  have hqtop : 3 * (1 - pr p) ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num) (ENNReal.sub_ne_top ENNReal.one_ne_top)
  have ht := ENNReal.mul_inv_cancel hq0 hqtop
  have ht1 : (3 * (1 - pr p))⁻¹ ≤ 1 := by
    rw [ENNReal.inv_le_one]
    have hx' := hx
    generalize pr p = x at hx'
    basify
    rw [max_eq_left (by linarith)]
    linarith
  calc pr p + (1 - pr p) * z.mass ^ 3 ≤ pr p + (1 - pr p) * ((3 * (1 - pr p))⁻¹) ^ 3 := by
        gcongr
    _ ≤ (3 * (1 - pr p))⁻¹ := by
        have hx1 : pr p ≤ 1 := (hx.trans two_thirds_lt_one).le
        generalize (3 * (1 - pr p))⁻¹ = t at *
        generalize pr p = x at *
        clear hz hq0 hqtop
        basify
        rw [max_eq_left (by linarith)] at *
        nlinarith [pow_nonneg (sub_nonneg.2 ht1) 3]

/-- **The knife edge** (§3.3): with leaf probability `p`, the ternary sampler terminates almost
surely exactly when `p ≥ 2/3`. Canou and Darrasse compute `ρ` in floating point; a rounding of
`ρ / T(ρ)` below `2/3` — the double nearest `2/3` is below it — makes the sampler supercritical. -/
theorem genTernary_terminates_iff (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    IsAlmostSurelyTerminating (genTernary p : SPMF TTree) ↔ 2/3 ≤ p := by
  refine ⟨fun h => not_lt.1 fun hp => ?_, fun hp => genTernary_terminates hp hp1⟩
  have hx : pr p < 2/3 := pr_two_thirds ▸ pr_strictMono hp0 hp
  have h3 : 1 < 3 * (1 - pr p) := by
    clear h
    generalize pr p = x at hx
    have hx1 : x ≤ 1 := (hx.trans two_thirds_lt_one).le
    basify
    rw [max_eq_left (by linarith)]
    linarith
  have hle := genTernary_mass_le hp0 hp
  rw [h] at hle
  exact absurd hle (not_le.2 (ENNReal.inv_lt_one.2 h3))

/-- The double nearest `2/3`, `6004799503160661 / 2⁵³`, is below `2/3`, so a sampler that uses it
loses mass. -/
theorem genTernary_double_two_thirds :
    ¬ IsAlmostSurelyTerminating (genTernary (6004799503160661 / 2 ^ 53) : SPMF TTree) := by
  rw [genTernary_terminates_iff (by norm_num) (by norm_num)]
  norm_num

/-- **Infinite expected size at the singularity** (§3.3: "the mean size of the generated structures
is infinite. We will never generate an infinite object"): the sampler terminates
(`genTernary_terminates`), yet `E = 2/3 + E`. -/
theorem genTernary_expected_size_singular :
    expect (genTernary (2/3) : SPMF TTree) (fun t => (t.size : ℝ≥0∞)) = ⊤ := by
  have hm : (genTernary (2/3) : SPMF TTree).mass = 1 :=
    genTernary_terminates (by norm_num) (by norm_num)
  have hstep := expect_genTernary_step (p := 2/3) (by norm_num) (by norm_num)
    (genTernary (2/3)) (fun t => (t.size : ℝ≥0∞))
  rw [← genTernary] at hstep
  simp only [TTree.size, Nat.cast_add, Nat.cast_one, add_assoc, expect_const_add,
    expect_add_const, hm, one_mul, mul_one] at hstep
  generalize expect (genTernary (2/3) : SPMF TTree) (fun t => (t.size : ℝ≥0∞)) = E at hstep ⊢
  rw [pr_two_thirds, one_sub_two_thirds] at hstep
  by_contra hE
  have h : E + 0 = E + 2 / 3 :=
    calc E + 0 = 2 / 3 + 1 / 3 * (E + (E + E)) := by rw [add_zero]; exact hstep
      _ = E * (3 * (1 / 3)) + 2 / 3 := by ring
      _ = E + 2 / 3 := by rw [ENNReal.mul_div_cancel (by norm_num) (by norm_num), mul_one]
  exact absurd ((ENNReal.add_right_inj hE).1 h).symm (by simp)

/-! ## One-two trees: `T = Z + Z × T + Z × T × T`

At `ρ = 1/3`, `T(ρ) = 1`, and the leaf, unary, and binary branches each have probability `1/3`. -/

/-- One-two (unary-binary, Motzkin) trees. -/
inductive OTTree where
  | leaf
  | unary (t : OTTree)
  | binary (l r : OTTree)
deriving DecidableEq

/-- The size: every node is an atom. -/
def OTTree.size : OTTree → Nat
  | .leaf => 1
  | .unary t => t.size + 1
  | .binary l r => l.size + r.size + 1

def OTTree.leaves : OTTree → Nat
  | .leaf => 1
  | .unary t => t.leaves
  | .binary l r => l.leaves + r.leaves

def OTTree.unaries : OTTree → Nat
  | .leaf => 0
  | .unary t => t.unaries + 1
  | .binary l r => l.unaries + r.unaries

def OTTree.binaries : OTTree → Nat
  | .leaf => 0
  | .unary t => t.binaries
  | .binary l r => l.binaries + r.binaries + 1

theorem OTTree.leaves_eq (t : OTTree) : t.leaves = t.binaries + 1 := by
  induction t <;> simp only [OTTree.leaves, OTTree.binaries, *]; omega

theorem OTTree.size_eq (t : OTTree) : t.size = t.leaves + t.unaries + t.binaries := by
  induction t <;> simp only [OTTree.size, OTTree.leaves, OTTree.unaries, OTTree.binaries, *] <;>
    omega

/-- Fig. 3's `OTTree ()`, with the three branches weighted `a`, `b`, `c` (at `ρ`, all equal). -/
def genOneTwoW [Gen G] (a b c : Nat) (h : 0 < a + b + c) : G OTTree :=
  frequency! [
    (a, fun _ => pure .leaf),
    (b, fun _ => do return .unary (← genOneTwoW a b c h)),
    (c, fun _ => do return .binary (← genOneTwoW a b c h) (← genOneTwoW a b c h))]
    (by simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; omega)
partial_fixpoint

theorem three_pos : 0 < 1 + 1 + 1 := by norm_num

theorem genOneTwoW_apply (h : 0 < a + b + c) (t : OTTree) :
    (genOneTwoW a b c h : SPMF OTTree) t
      = (a / (a + b + c : ℝ≥0∞)) ^ t.leaves * (b / (a + b + c : ℝ≥0∞)) ^ t.unaries
        * (c / (a + b + c : ℝ≥0∞)) ^ t.binaries := by
  induction t with
  | leaf =>
    rw [genOneTwoW, frequencyWith_eq, frequency_apply]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, pure_apply, ↓reduceIte]
    rw [bind_pure_apply_of_ne _ fun _ => OTTree.noConfusion,
      bind_bind_pure_apply_of_ne (f := OTTree.binary) _ _ fun _ _ => OTTree.noConfusion]
    simp [OTTree.leaves, OTTree.unaries, OTTree.binaries, ENNReal.div_eq_inv_mul, add_assoc]
  | unary t ih =>
    rw [genOneTwoW, frequencyWith_eq, frequency_apply]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, pure_apply, reduceCtorEq,
      ↓reduceIte]
    rw [bind_pure_apply_of_injective (fun _ _ h => OTTree.unary.inj h), ih,
      bind_bind_pure_apply_of_ne (f := OTTree.binary) _ _ fun _ _ => OTTree.noConfusion]
    simp only [OTTree.leaves, OTTree.unaries, OTTree.binaries, ENNReal.div_eq_inv_mul, add_zero,
      Nat.cast_add,
      ← add_assoc]
    ring
  | binary l r ihl ihr =>
    rw [genOneTwoW, frequencyWith_eq, frequency_apply]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, pure_apply, reduceCtorEq,
      ↓reduceIte]
    rw [bind_pure_apply_of_ne _ fun _ => OTTree.noConfusion,
      bind_bind_pure_apply_of_injective (f := OTTree.binary) fun _ _ _ _ h => OTTree.binary.inj h,
      ihl, ihr]
    simp only [OTTree.leaves, OTTree.unaries, OTTree.binaries, ENNReal.div_eq_inv_mul, add_zero,
      Nat.cast_add,
      ← add_assoc]
    ring

/-- At `ρ = 1/3` all three weights are equal; a tree of size `n` has mass `(1/3) ^ n`: the
Boltzmann form with `T(ρ) = 1`. -/
theorem genOneTwo_boltzmann :
    IsBoltzmann (genOneTwoW 1 1 1 three_pos : SPMF OTTree) OTTree.size (1/3) 1 := by
  intro t
  rw [genOneTwoW_apply, div_one, OTTree.size_eq, pow_add, pow_add]
  norm_num

/-- Whether the weighted sampler gives two trees of the same size the same mass. -/
def UniformWithinSize (μ : SPMF OTTree) : Prop :=
  ∀ s t : OTTree, s.size = t.size → μ s = μ t

/-- **Exact uniformity needs exact weights.** The weighted one-two sampler is uniform within each
size exactly when `b² = a c` (or it never halts, `a = 0`). Fig. 3's three thresholds, `x / T(x)` and
`(x + U(x)) / T(x)`, are floating-point numbers; nothing makes the rounded unary probability the
geometric mean of the other two, so the floating-point sampler is only approximately uniform
(Duchon et al. 2004, §5). At `ρ`, `a = b = c`. -/
theorem genOneTwoW_uniform_iff (h : 0 < a + b + c) :
    UniformWithinSize (genOneTwoW a b c h : SPMF OTTree) ↔ a = 0 ∨ b ^ 2 = a * c := by
  set S : ℝ≥0∞ := a + b + c
  have hS0 : S ≠ 0 := by simp only [S]; exact_mod_cast h.ne'
  have hStop : S ≠ ⊤ := by simp [S]
  constructor
  · intro hu
    have := hu (.unary (.unary .leaf)) (.binary .leaf .leaf) rfl
    simp only [genOneTwoW_apply, OTTree.leaves, OTTree.unaries, OTTree.binaries] at this
    rw [or_iff_not_imp_left]
    intro ha
    have h3 : (a : ℝ≥0∞) * b ^ 2 = a * (a * c) := by
      have h' := congrArg (· * S ^ 3) this
      simp only [div_eq_mul_inv] at h'
      have hSS : S⁻¹ * S = 1 := ENNReal.inv_mul_cancel hS0 hStop
      calc (a : ℝ≥0∞) * b ^ 2
          = (↑a * S⁻¹) ^ 1 * (↑b * S⁻¹) ^ 2 * (↑c * S⁻¹) ^ 0 * S ^ 3 := by
            simp only [pow_one, pow_zero, mul_one]
            calc (a : ℝ≥0∞) * b ^ 2 = a * b ^ 2 * (S⁻¹ * S) ^ 3 := by rw [hSS, one_pow, mul_one]
              _ = _ := by ring
        _ = (↑a * S⁻¹) ^ 2 * (↑b * S⁻¹) ^ 0 * (↑c * S⁻¹) ^ 1 * S ^ 3 := h'
        _ = a * (a * c) := by
            simp only [pow_one, pow_zero, mul_one]
            calc (↑a * S⁻¹) ^ 2 * (↑c * S⁻¹) * S ^ 3 = a * (a * c) * (S⁻¹ * S) ^ 3 := by ring
              _ = _ := by rw [hSS, one_pow, mul_one]
    have h3' : a * b ^ 2 = a * (a * c) := by exact_mod_cast h3
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero ha) h3'
  · rintro (rfl | hb) s t hst
    · simp only [genOneTwoW_apply, Nat.cast_zero, ENNReal.zero_div, OTTree.leaves_eq,
        zero_pow (Nat.succ_ne_zero _), zero_mul]
    · have hxz : (a / S) * (c / S) = (b / S) ^ 2 := by
        rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, mul_pow,
          show (b : ℝ≥0∞) ^ 2 = a * c by exact_mod_cast hb]
        ring
      have hform : ∀ t : OTTree, (genOneTwoW a b c h : SPMF OTTree) t
          = (a / S) * (b / S) ^ (t.size - 1) := fun t => by
        rw [genOneTwoW_apply, show (a + b + c : ℝ≥0∞) = S from rfl, OTTree.size_eq,
          OTTree.leaves_eq,
          show t.binaries + 1 + t.unaries + t.binaries - 1 = t.unaries + 2 * t.binaries by omega,
          pow_add (b / S), pow_mul, ← hxz, mul_pow, pow_succ]
        ring
      rw [hform, hform, hst]

/-- **Terminates almost surely at the singularity**: one, two, or no children, each with probability
`1/3`, is mean offspring exactly `1`. -/
theorem genOneTwo_terminates :
    IsAlmostSurelyTerminating (genOneTwoW 1 1 1 three_pos : SPMF OTTree) := by
  mass_fixpoint using SPMF.LfpIsOne.quadratic (a := 1 / 3) (b := 1 / 3) (d := 1 / 3)
  norm_num [sq, ENNReal.div_eq_inv_mul, mul_add]
  exact le_of_eq (by ring)

/-- **Infinite expected size at the singularity**: unfolded once, `E = 1 + E`. -/
theorem genOneTwo_expected_size :
    expect (genOneTwoW 1 1 1 three_pos : SPMF OTTree) (fun t => (t.size : ℝ≥0∞)) = ⊤ := by
  have hm : (genOneTwoW 1 1 1 three_pos : SPMF OTTree).mass = 1 := genOneTwo_terminates
  have hstep : expect (genOneTwoW 1 1 1 three_pos : SPMF OTTree) (fun t => (t.size : ℝ≥0∞))
      = expect (genOneTwoW 1 1 1 three_pos : SPMF OTTree) (fun t => (t.size : ℝ≥0∞)) := rfl
  conv_rhs at hstep => rw [genOneTwoW]
  rw [frequencyWith_eq, expect_frequency] at hstep
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, expect_bind, expect_pure,
    OTTree.size, Nat.cast_add, Nat.cast_one, add_assoc, expect_const_add, expect_add_const, hm,
    one_mul, mul_one] at hstep
  generalize expect (genOneTwoW 1 1 1 three_pos : SPMF OTTree) (fun t => (t.size : ℝ≥0∞)) = E
    at hstep ⊢
  rw [show (1 + (E + (1 + (E + (E + (1 + 0))))) : ℝ≥0∞) = 3 * (E + 1) by ring,
    show (1 + (1 + (1 + ((0 : ℕ) : ℝ≥0∞))) : ℝ≥0∞) = 3 by norm_num,
    mul_comm, mul_div_assoc, ENNReal.div_self (by norm_num) (by norm_num), mul_one] at hstep
  by_contra hE
  exact absurd ((ENNReal.add_right_inj hE).1 (hstep.symm.trans (add_zero E).symm)) one_ne_zero

/-- One-two trees, by their top constructor. -/
def OTTree.equiv : OTTree ≃ Unit ⊕ (OTTree ⊕ OTTree × OTTree) where
  toFun
    | .leaf => .inl ()
    | .unary t => .inr (.inl t)
    | .binary l r => .inr (.inr (l, r))
  invFun
    | .inl _ => .leaf
    | .inr (.inl t) => .unary t
    | .inr (.inr (l, r)) => .binary l r
  left_inv t := by cases t <;> rfl
  right_inv x := by rcases x with _ | _ | ⟨_, _⟩ <;> rfl

/-- `c_n`, the number of one-two trees of size `n` (the Motzkin numbers, shifted). -/
noncomputable def count (n : Nat) : ℝ≥0∞ := ∑' t : OTTree, if t.size = n then 1 else 0

theorem OTTree.size_pos (t : OTTree) : 0 < t.size := by cases t <;> simp [OTTree.size]

theorem count_zero : count 0 = 0 :=
  ENNReal.tsum_eq_zero.2 fun t => by simp [(OTTree.size_pos t).ne']

private theorem ite_add_eq (a b n : Nat) :
    (if a + b = n then (1 : ℝ≥0∞) else 0)
      = ∑ p ∈ Finset.antidiagonal n, (if a = p.1 then 1 else 0) * (if b = p.2 then 1 else 0) := by
  by_cases h : a + b = n
  · rw [ite_eq_left_iff.2 fun h' => absurd h h', Finset.sum_eq_single (a, b)]
    · simp
    · intro p _ hp
      by_cases h1 : a = p.1
      · have : b = p.2 := by have := Finset.mem_antidiagonal.1 ‹_›; omega
        exact absurd (Prod.ext h1.symm this.symm) hp
      · simp [h1]
    · intro hab; exact absurd (Finset.mem_antidiagonal.2 h) hab
  · rw [ite_eq_right_iff.2 fun h' => absurd h' h]
    refine (Finset.sum_eq_zero fun p hp => ?_).symm
    have := Finset.mem_antidiagonal.1 hp
    by_cases h1 : a = p.1 <;> by_cases h2 : b = p.2 <;> simp [h1, h2]; omega

/-- The recursion for `c_n`: a leaf, a unary node over a tree of size `n`, or a binary node over two
trees whose sizes add to `n`. -/
theorem count_succ (n : Nat) :
    count (n + 1) = (if n = 0 then 1 else 0) + count n
      + ∑ p ∈ Finset.antidiagonal n, count p.1 * count p.2 := by
  unfold count
  rw [← OTTree.equiv.symm.tsum_eq, Summable.tsum_sum ENNReal.summable ENNReal.summable,
    Summable.tsum_sum ENNReal.summable ENNReal.summable, add_assoc]
  congr 1
  · simp [OTTree.equiv, OTTree.size]
  congr 1
  · simp [OTTree.equiv, OTTree.size]
  simp only [OTTree.equiv, Equiv.coe_fn_symm_mk, OTTree.size, Nat.add_right_cancel_iff]
  simp_rw [ite_add_eq]
  rw [Summable.tsum_finsetSum fun _ _ => ENNReal.summable]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [ENNReal.tsum_prod', ← ENNReal.tsum_mul_right]
  simp_rw [← ENNReal.tsum_mul_left]

theorem count_one : count 1 = 1 := by rw [count_succ]; simp [count_zero]
theorem count_two : count 2 = 1 := by
  rw [count_succ]; simp [Finset.Nat.antidiagonal_succ, count_zero, count_one]
theorem count_three : count 3 = 2 := by
  rw [count_succ]; simp [Finset.Nat.antidiagonal_succ, count_zero, count_one, count_two]; norm_num
theorem count_four : count 4 = 4 := by
  rw [count_succ]
  simp [Finset.Nat.antidiagonal_succ, count_zero, count_one, count_two, count_three]; norm_num
theorem count_five : count 5 = 9 := by
  rw [count_succ]
  simp [Finset.Nat.antidiagonal_succ, count_zero, count_one, count_two, count_three, count_four]
  norm_num

/-- **(2.3) for one-two trees**: size `n` has probability `c_n ρ^n / T(ρ) = c_n / 3^n`. §3.3 prints
`c_n xⁿ ρ⁻ⁿ` instead, which at the singular `x = ρ` is `c_n` itself: at `n = 4` it would give the
size the "probability" `4`. The correct value is `4/81`; the asymptotic `n^{-3/2} (x/ρ)ⁿ` the paper
derives from it is unaffected. -/
theorem prob_size_four :
    prob (genOneTwoW 1 1 1 three_pos : SPMF OTTree) {t | t.size = 4} = 4 / 81 := by
  rw [genOneTwo_boltzmann.prob_size, ← count, count_four, div_one]
  basify; norm_num

/-! ### Abort and retry (§3.3)

"Aborting the generating process as soon as we pass the upper bound of our target size", then
retrying until the size is at least the lower bound. -/


section ceil

variable {α β : Type}

/-- A ceiled draw, relabelled by `g`, at a relabelled value. -/
theorem ceil_map_apply {x : SPMF (Option (α × Nat))}
    {f : Option (α × Nat) → SPMF (Option (β × Nat))}
    {g : α → β} (hg : g.Injective) (hnone : f none = Pure.pure none)
    (hsome : ∀ s k, f (some (s, k)) = Pure.pure (some (g s, k))) (s : α) (k : Nat) :
    (x >>= f) (some (g s, k)) = x (some (s, k)) := by
  rw [bind_apply, tsum_option, hnone, tsum_eq_single (s, k) fun p hp => ?_]
  · simp [hsome]
  · rw [hsome, pure_apply]
    split_ifs with h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      exact absurd (Prod.ext (hg h.1).symm h.2.symm) hp
    · rw [mul_zero]

theorem ceil_map_apply_of_ne {x : SPMF (Option (α × Nat))}
    {f : Option (α × Nat) → SPMF (Option (β × Nat))} {g : α → β} (hnone : f none = Pure.pure none)
    (hsome : ∀ s k, f (some (s, k)) = Pure.pure (some (g s, k))) {u : β} (hu : ∀ s, g s ≠ u)
    (k : Nat) : (x >>= f) (some (u, k)) = 0 := by
  rw [bind_apply, tsum_option, hnone]
  simp only [hsome]
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq]
  simp [fun s => Ne.symm (hu s)]

/-- A ceiled draw followed by a second whose budget is what the first left, at a pair. -/
theorem ceil_bind_apply {x : SPMF (Option (α × Nat))} {y : Nat → SPMF (Option (α × Nat))}
    {f : Option (α × Nat) → SPMF (Option (β × Nat))}
    {F : α → Option (α × Nat) → SPMF (Option (β × Nat))} {g : α → α → β}
    (hg : ∀ l r l' r', g l r = g l' r' → l = l' ∧ r = r') (hnone : f none = Pure.pure none)
    (hsome : ∀ l k, f (some (l, k)) = y k >>= F l) (hFnone : ∀ l, F l none = Pure.pure none)
    (hFsome : ∀ l r k, F l (some (r, k)) = Pure.pure (some (g l r, k))) (l r : α) (k : Nat) :
    (x >>= f) (some (g l r, k)) = ∑' k', x (some (l, k')) * y k' (some (r, k)) := by
  rw [bind_apply, tsum_option, hnone, ENNReal.tsum_prod']
  simp only [pure_apply, reduceCtorEq, ↓reduceIte, mul_zero, zero_add, hsome]
  rw [tsum_eq_single l fun l' hl' => ENNReal.tsum_eq_zero.2 fun k' => by
    rw [ceil_map_apply_of_ne (hFnone l') (hFsome l') (fun r' h => hl' (hg _ _ _ _ h).1),
      mul_zero]]
  exact tsum_congr fun k' => by
    rw [ceil_map_apply (fun r r' h => (hg _ _ _ _ h).2) (hFnone l) (hFsome l)]

theorem ceil_bind_apply_of_ne {x : SPMF (Option (α × Nat))} {y : Nat → SPMF (Option (α × Nat))}
    {f : Option (α × Nat) → SPMF (Option (β × Nat))}
    {F : α → Option (α × Nat) → SPMF (Option (β × Nat))} {g : α → α → β}
    (hnone : f none = Pure.pure none) (hsome : ∀ l k, f (some (l, k)) = y k >>= F l)
    (hFnone : ∀ l, F l none = Pure.pure none)
    (hFsome : ∀ l r k, F l (some (r, k)) = Pure.pure (some (g l r, k))) {u : β}
    (hu : ∀ l r, g l r ≠ u) (k : Nat) : (x >>= f) (some (u, k)) = 0 := by
  rw [bind_apply, tsum_option, hnone, ENNReal.tsum_prod']
  simp only [pure_apply, reduceCtorEq, ↓reduceIte, mul_zero, zero_add, hsome]
  exact ENNReal.tsum_eq_zero.2 fun l => ENNReal.tsum_eq_zero.2 fun k' => by
    rw [ceil_map_apply_of_ne (hFnone l) (hFsome l) (hu l), mul_zero]

end ceil

/-- `genOneTwoW` with a budget of `k` atoms: it gives up (`none`) as soon as the tree would exceed
the budget, and returns the budget left. -/
def genOTCeil [Gen G] (a b c : Nat) (h : 0 < a + b + c) (k : Nat) :
    G (Option (OTTree × Nat)) := do
  if k = 0 then return none
  frequency! [
    (a, fun _ => pure (some (.leaf, k - 1))),
    (b, fun _ => do
      match ← genOTCeil a b c h (k - 1) with
      | none => return none
      | some (t, k') => return some (.unary t, k')),
    (c, fun _ => do
      match ← genOTCeil a b c h (k - 1) with
      | none => return none
      | some (l, k') =>
        match ← genOTCeil a b c h k' with
        | none => return none
        | some (r, k'') => return some (.binary l r, k''))]
    (by simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; omega)
partial_fixpoint

/-- One round: a ceiled draw, kept if it reaches the lower bound. -/
def roundOT [Gen G] (a b c : Nat) (h : 0 < a + b + c) (lo hi : Nat) : G (Option OTTree) := do
  match ← genOTCeil a b c h hi with
  | some (t, _) => return if lo ≤ t.size then some t else none
  | none => return none

/-- The abort-and-retry sampler. -/
def ceiledOT [Gen G] (a b c : Nat) (h : 0 < a + b + c) (lo hi : Nat) : G OTTree :=
  retry (roundOT a b c h lo hi)

theorem genOneTwoW_leaf (h : 0 < a + b + c) :
    (genOneTwoW a b c h : SPMF OTTree) .leaf = a / (a + b + c : ℝ≥0∞) := by
  simp [genOneTwoW_apply, OTTree.leaves, OTTree.unaries, OTTree.binaries]

theorem genOneTwoW_unary (h : 0 < a + b + c) (t : OTTree) :
    (genOneTwoW a b c h : SPMF OTTree) (.unary t)
      = b / (a + b + c : ℝ≥0∞) * (genOneTwoW a b c h : SPMF OTTree) t := by
  simp only [genOneTwoW_apply, OTTree.leaves, OTTree.unaries, OTTree.binaries]; ring

theorem genOneTwoW_binary (h : 0 < a + b + c) (l r : OTTree) :
    (genOneTwoW a b c h : SPMF OTTree) (.binary l r)
      = c / (a + b + c : ℝ≥0∞)
        * ((genOneTwoW a b c h : SPMF OTTree) l * (genOneTwoW a b c h : SPMF OTTree) r) := by
  simp only [genOneTwoW_apply, OTTree.leaves, OTTree.unaries, OTTree.binaries]; ring

theorem genOTCeil_apply (h : 0 < a + b + c) (t : OTTree) :
    ∀ k k', (genOTCeil a b c h k : SPMF _) (some (t, k'))
      = if t.size ≤ k ∧ k' = k - t.size then (genOneTwoW a b c h : SPMF OTTree) t else 0 := by
  induction t with
  | leaf =>
    intro k k'
    rcases k with _ | j
    · rw [genOTCeil]; simp [OTTree.size]
    rw [genOTCeil]
    simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    rw [frequencyWith_eq, frequency_apply]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    rw [ceil_map_apply_of_ne (g := OTTree.unary) (by rfl) (by intros; rfl)
        (by intros; exact OTTree.noConfusion),
      ceil_bind_apply_of_ne (g := OTTree.binary) (by rfl) (by intros; rfl) (by intros; rfl)
        (by intros; rfl) (by intros; exact OTTree.noConfusion), genOneTwoW_leaf]
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq, true_and, mul_zero, add_zero,
      Nat.cast_add, ← add_assoc]
    split_ifs with h1 h2 h2 <;> simp only [OTTree.size] at * <;> first | omega | simp
  | unary t ih =>
    intro k k'
    rcases k with _ | j
    · rw [genOTCeil]; simp [OTTree.size]
    rw [genOTCeil]
    simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    rw [frequencyWith_eq, frequency_apply]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    rw [ceil_map_apply (g := OTTree.unary) (fun _ _ h => OTTree.unary.inj h) (by rfl)
        (by intros; rfl),
      ceil_bind_apply_of_ne (g := OTTree.binary) (by rfl) (by intros; rfl) (by intros; rfl)
        (by intros; rfl) (by intros; exact OTTree.noConfusion), ih, genOneTwoW_unary]
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq, reduceCtorEq, false_and, ↓reduceIte,
      mul_zero, zero_add, add_zero, Nat.cast_add, ← add_assoc]
    split_ifs with h1 h2 h2 <;> simp only [OTTree.size] at * <;>
      first | omega | simp | (simp only [div_eq_mul_inv]; ring)
  | binary l r ihl ihr =>
    intro k k'
    rcases k with _ | j
    · rw [genOTCeil]; simp [OTTree.size]
    rw [genOTCeil]
    simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    rw [frequencyWith_eq, frequency_apply]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    rw [ceil_map_apply_of_ne (g := OTTree.unary) (by rfl) (by intros; rfl)
        (by intros; exact OTTree.noConfusion),
      ceil_bind_apply (g := OTTree.binary) (fun _ _ _ _ h => OTTree.binary.inj h) (by rfl)
        (by intros; rfl) (by intros; rfl) (by intros; rfl),
      tsum_eq_single (j - l.size) fun k1 hk1 => by
        rw [ihl, ite_eq_right_iff.2 fun h => absurd h (by omega), zero_mul],
      ihl,
      ihr, genOneTwoW_binary]
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq, reduceCtorEq, false_and, ↓reduceIte,
      mul_zero, zero_add, Nat.cast_add, ← add_assoc, and_true]
    split_ifs with h1 h2 h3 h3 <;> simp only [OTTree.size] at * <;>
      first | omega | simp | (simp only [div_eq_mul_inv]; ring)

/-- The ceiled sampler always halts: the budget shrinks on every call. -/
theorem genOTCeil_mass (h : 0 < a + b + c) (k : Nat) :
    (genOTCeil a b c h k : SPMF _).mass = 1 := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  rcases k with _ | j
  · rw [genOTCeil]; simp
  rw [genOTCeil]
  simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
  rw [frequencyWith_eq, mass_frequency]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, mass_pure,
    mul_one]
  rw [mass_bind_of_mass_one (by rintro (_ | ⟨t, k⟩) _ <;> simp), ih j (by omega),
    mass_bind_of_mass_one ?_, ih j (by omega), mul_one, mul_one]
  · rw [← Nat.cast_add, ← Nat.cast_add, ← add_assoc]
    exact ENNReal.div_self (by exact_mod_cast h.ne') (by simp)
  · rintro (_ | ⟨l, k'⟩) hne
    · simp
    · have hk : k' ≤ j := by
        rw [genOTCeil_apply] at hne
        by_contra hk
        exact hne (ite_eq_right_iff.2 fun h => absurd h (by omega))
      rw [mass_bind_of_mass_one (by rintro (_ | ⟨r, k''⟩) _ <;> simp), ih k' (by omega)]

/-- One round keeps each tree in the window with `genOneTwoW`'s mass. -/
theorem roundOT_some (h : 0 < a + b + c) (lo hi : Nat) (t : OTTree) :
    (roundOT a b c h lo hi : SPMF _) (some t)
      = if lo ≤ t.size ∧ t.size ≤ hi then (genOneTwoW a b c h : SPMF OTTree) t else 0 := by
  rw [roundOT, bind_apply, tsum_option, ENNReal.tsum_prod', tsum_eq_single t fun t' ht' =>
    ENNReal.tsum_eq_zero.2 fun k => by dsimp only; split_ifs <;> simp [Ne.symm ht'],
    tsum_eq_single (hi - t.size) fun k hk => by
      rw [genOTCeil_apply, ite_eq_right_iff.2 fun h => absurd h (by omega), zero_mul]]
  simp only [pure_apply, reduceCtorEq, ↓reduceIte, mul_zero, zero_add, genOTCeil_apply]
  by_cases h1 : lo ≤ t.size <;> by_cases h2 : t.size ≤ hi <;> simp [h1, h2]

/-- The window `[lo, hi]` on sizes. -/
def window (lo hi : Nat) (t : OTTree) : Bool := decide (lo ≤ t.size ∧ t.size ≤ hi)

theorem roundOT_mass (h : 0 < a + b + c) (lo hi : Nat) :
    (roundOT a b c h lo hi : SPMF _).mass = 1 := by
  rw [roundOT, mass_bind_of_mass_one (by rintro (_ | ⟨t, k⟩) _ <;> simp), genOTCeil_mass]

/-- **The law of abort-and-retry**, for every weighting: `genOneTwoW` conditioned on the window. -/
theorem ceiledOT_apply (h : 0 < a + b + c) (lo hi : Nat) (t : OTTree) :
    (ceiledOT a b c h lo hi : SPMF OTTree) t
      = (if window lo hi t then (genOneTwoW a b c h : SPMF OTTree) t else 0)
        / prob (genOneTwoW a b c h : SPMF OTTree) {t | window lo hi t = true} := by
  classical
  have hsum := roundOT_mass h lo hi
  rw [mass, tsum_option] at hsum
  have hQ : 1 - (roundOT a b c h lo hi : SPMF _) none
      = prob (genOneTwoW a b c h : SPMF OTTree) {t | window lo hi t = true} := by
    rw [← hsum, ENNReal.add_sub_cancel_left (apply_ne_top _ _), prob_eq_tsum_ite]
    exact tsum_congr fun t => by rw [roundOT_some]; simp [window]
  rw [ceiledOT, retry_apply, hQ, roundOT_some]
  simp [window]

/-- Within a size, abort-and-retry at `ρ` is uniform. -/
theorem ceiledOT_uniform (lo hi : Nat) {s t : OTTree} (hst : s.size = t.size) :
    (ceiledOT 1 1 1 three_pos lo hi : SPMF OTTree) s
      = (ceiledOT 1 1 1 three_pos lo hi : SPMF OTTree) t := by
  rw [ceiledOT_apply, ceiledOT_apply, window, window, hst,
    genOneTwo_boltzmann.uniform hst]

/-- A unary chain of size `n + 1`. -/
def OTTree.chain : Nat → OTTree
  | 0 => .leaf
  | n + 1 => .unary (OTTree.chain n)

theorem OTTree.chain_size (n : Nat) : (OTTree.chain n).size = n + 1 := by
  induction n <;> simp [OTTree.chain, OTTree.size, *]

/-- **Abort-and-retry terminates** although the sampler it ceils is critical with infinite expected
size, for any nonempty window of positive sizes. -/
theorem ceiledOT_terminates {lo hi : Nat} (hlo : 1 ≤ lo) (hle : lo ≤ hi) :
    IsAlmostSurelyTerminating (ceiledOT 1 1 1 three_pos lo hi : SPMF OTTree) := by
  classical
  set Q := prob (genOneTwoW 1 1 1 three_pos : SPMF OTTree) {t | window lo hi t = true}
  have hQsum : (∑' t, if window lo hi t = true then (genOneTwoW 1 1 1 three_pos : SPMF OTTree) t
      else 0) = Q := by simp only [Q, prob_eq_tsum_ite, Set.mem_ofPred_eq]
  have hw : window lo hi (OTTree.chain (lo - 1)) = true := by
    simp [window, OTTree.chain_size]; omega
  have hQ0 : Q ≠ 0 := by
    rw [← hQsum]
    refine (lt_of_lt_of_le ?_ (ENNReal.le_tsum (OTTree.chain (lo - 1)))).ne'
    simp only [hw, ↓reduceIte, genOneTwo_boltzmann _]
    simp [ENNReal.pow_pos]
  have hQtop : Q ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top
    ((prob_le_mass _ _).trans (mass_le_one _))
  unfold IsAlmostSurelyTerminating mass
  simp_rw [ceiledOT_apply, div_eq_mul_inv]
  rw [ENNReal.tsum_mul_right, hQsum, ENNReal.mul_inv_cancel hQ0 hQtop]

private theorem tsum_size_eq (m : Nat) :
    (∑' t : OTTree, if t.size = m then (genOneTwoW 1 1 1 three_pos : SPMF OTTree) t else 0)
      = count m * (1 / 3) ^ m := by
  rw [count, ← ENNReal.tsum_mul_right]
  refine tsum_congr fun t => ?_
  by_cases ht : t.size = m <;> simp [ht, genOneTwo_boltzmann t]

theorem prob_window_three_five :
    prob (genOneTwoW 1 1 1 three_pos : SPMF OTTree) {t | window 3 5 t = true} = 13 / 81 := by
  classical
  rw [prob_eq_tsum_ite]
  have : ∀ t : OTTree, (if t ∈ {t | window 3 5 t = true}
      then (genOneTwoW 1 1 1 three_pos : SPMF OTTree) t else 0)
      = (if t.size = 3 then (genOneTwoW 1 1 1 three_pos : SPMF OTTree) t else 0)
        + (if t.size = 4 then (genOneTwoW 1 1 1 three_pos : SPMF OTTree) t else 0)
        + (if t.size = 5 then (genOneTwoW 1 1 1 three_pos : SPMF OTTree) t else 0) := fun t => by
    simp only [Set.mem_ofPred_eq, window, decide_eq_true_eq]
    by_cases h3 : t.size = 3 <;> by_cases h4 : t.size = 4 <;> by_cases h5 : t.size = 5 <;>
      simp [h3, h4, h5]
    all_goals (intros; omega)
  rw [tsum_congr this, ENNReal.tsum_add, ENNReal.tsum_add, tsum_size_eq, tsum_size_eq,
    tsum_size_eq, count_three, count_four, count_five]
  basify; norm_num

/-- The probability that abort-and-retry returns size `m`: `c_m ρ^m`, renormalized over the
window. -/
theorem prob_ceiledOT_size (lo hi m : Nat) :
    prob (ceiledOT 1 1 1 three_pos lo hi : SPMF OTTree) {t | t.size = m}
      = (if lo ≤ m ∧ m ≤ hi then count m * (1 / 3) ^ m else 0)
        / prob (genOneTwoW 1 1 1 three_pos : SPMF OTTree) {t | window lo hi t = true} := by
  classical
  rw [prob_eq_tsum_ite]
  simp_rw [ceiledOT_apply, div_eq_mul_inv]
  have : ∀ t : OTTree, (if t ∈ {t : OTTree | t.size = m} then
      (if window lo hi t = true then (genOneTwoW 1 1 1 three_pos : SPMF OTTree) t else 0) *
        (prob (genOneTwoW 1 1 1 three_pos : SPMF OTTree) {t | window lo hi t = true})⁻¹ else 0)
      = (if lo ≤ m ∧ m ≤ hi then
          (if t.size = m then (genOneTwoW 1 1 1 three_pos : SPMF OTTree) t else 0) else 0) *
        (prob (genOneTwoW 1 1 1 three_pos : SPMF OTTree) {t | window lo hi t = true})⁻¹ :=
    fun t => by
      by_cases ht : t.size = m
      · subst ht; simp [window]
      · simp [ht]
  rw [tsum_congr this, ENNReal.tsum_mul_right]
  split_ifs <;> simp [tsum_size_eq]

/-- **"A measurable bias towards smaller sized trees"** (§3), on the window `[3, 5]`: sizes `3`,
`4`, `5` come out with probabilities `6/13`, `4/13`, `3/13`, though uniform within each size
(`ceiledOT_uniform`). -/
theorem ceiledOT_bias :
    prob (ceiledOT 1 1 1 three_pos 3 5 : SPMF OTTree) {t | t.size = 3} = 6 / 13
      ∧ prob (ceiledOT 1 1 1 three_pos 3 5 : SPMF OTTree) {t | t.size = 4} = 4 / 13
      ∧ prob (ceiledOT 1 1 1 three_pos 3 5 : SPMF OTTree) {t | t.size = 5} = 3 / 13 := by
  simp only [prob_ceiledOT_size, prob_window_three_five, count_three, count_four, count_five]
  refine ⟨?_, ?_, ?_⟩ <;> norm_num <;>
    (rw [← ENNReal.toReal_eq_toReal_iff'
      (by simp [ENNReal.div_eq_top, ENNReal.mul_eq_top, ENNReal.pow_eq_top_iff])
      (by simp [ENNReal.div_eq_top])]; simp [ENNReal.toReal_div]; norm_num)

/-! ## General trees: `T = Z × Seq(T)`

At `ρ = 1/4`, `T(ρ) = 1/2`, so the number of children is geometric with parameter `1/2`: exactly the
length law of Basalt's `listOf`. The sampler is the naive recursive generator `node <$> listOf gen`.

Fig. 1 writes `T = Z × F, F = Seq(T)` and Fig. 2 `F(z) = 1 / (1 - T(z))`; §3.1's dictionary instead
translates `Seq(A)` to `z / (1 - A(z))`, counting the sequence itself as an atom, which would give
`T = z² / (1 - T)` and a different `ρ`. Figs. 2–3 are the consistent reading. -/

/-- General plane trees. -/
inductive GTree where
  | node (cs : List GTree)

/-- The size: the number of nodes. -/
def GTree.size : GTree → Nat
  | .node cs => (cs.attach.map fun ⟨c, _⟩ => c.size).sum + 1

theorem GTree.size_node (cs : List GTree) :
    (GTree.node cs).size = (cs.map GTree.size).sum + 1 := by
  rw [GTree.size]
  congr 2
  conv_rhs => rw [← List.attach_map_subtype_val cs, List.map_map]
  rfl

private theorem prod_map_eq {f : GTree → ℝ≥0∞} :
    ∀ cs : List GTree, (∀ c ∈ cs, f c = 2 * (1 / 4) ^ c.size) →
      (cs.map f).prod = 2 ^ cs.length * (1 / 4) ^ (cs.map GTree.size).sum
  | [], _ => by simp
  | c :: cs, h => by
    rw [List.map_cons, List.prod_cons, h c (by simp),
      prod_map_eq cs fun c' hc' => h c' (by simp [hc'])]
    simp only [List.length_cons, List.map_cons, List.sum_cons, pow_succ, pow_add]
    ring

/-- Fig. 3's `GTree ()`: a node, then a geometric number of independent subtrees. -/
def genGeneral [Gen G] : G GTree := do
  return .node (← listOf genGeneral)
partial_fixpoint

/-- **The Boltzmann form**: a tree of `n` nodes has mass `ρ ^ n / T(ρ) = 2 (1/4) ^ n`. -/
theorem genGeneral_apply : ∀ t : GTree, (genGeneral : SPMF GTree) t = 2 * (1 / 4) ^ t.size
  | .node cs => by
    have ih : ∀ c ∈ cs, (genGeneral : SPMF GTree) c = 2 * (1 / 4) ^ c.size :=
      fun c _ => genGeneral_apply c
    rw [genGeneral, bind_pure_apply_of_injective (fun _ _ h => GTree.node.inj h), listOf_apply,
      GTree.size_node, prod_map_eq cs ih, pow_succ, pow_add, pow_one]
    have h2 : (1 / 2 : ℝ≥0∞) ^ cs.length * 2 ^ cs.length = 1 := by
      rw [← mul_pow, one_div, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_pow]
    calc (1 / 2 : ℝ≥0∞) ^ cs.length * (1 / 2) * (2 ^ cs.length * (1 / 4) ^ (cs.map GTree.size).sum)
        = ((1 / 2) ^ cs.length * 2 ^ cs.length) * (1 / 2) * (1 / 4) ^ (cs.map GTree.size).sum := by
          ring
      _ = 2 * ((1 / 4) ^ (cs.map GTree.size).sum * (1 / 4)) := by
          rw [h2, one_mul]
          rw [show (1 / 2 : ℝ≥0∞) = 2 * (1 / 4) by
            rw [← ENNReal.toReal_eq_toReal_iff' (by simp) (by simp [ENNReal.mul_eq_top])]
            simp; norm_num]
          ring

/-- **Terminates almost surely**: the mass satisfies `m = 1/2 + m²/2`, whose only root in `[0, 1]`
is the double root `1` of the critical case — here the unfolding alone decides. -/
theorem genGeneral_terminates : IsAlmostSurelyTerminating (genGeneral : SPMF GTree) := by
  have hstep := mass_listOf_step (genGeneral : SPMF GTree)
  have hm : (genGeneral : SPMF GTree).mass = (listOf genGeneral : SPMF (List GTree)).mass := by
    conv_lhs => rw [genGeneral]
    exact mass_bind_pure
  rw [← hm] at hstep
  replace hstep := hstep.symm.le
  have hm1 := mass_le_one (genGeneral : SPMF GTree)
  unfold IsAlmostSurelyTerminating
  generalize (genGeneral : SPMF GTree).mass = m at *
  clear hm
  basify
  nlinarith [sq_nonneg (m - 1)]

/-- **Infinite expected size**: with `S` the expected size of the children, `E = S + 1` and
`S = (E + S) / 2`. -/
theorem genGeneral_expected_size :
    expect (genGeneral : SPMF GTree) (fun t => (t.size : ℝ≥0∞)) = ⊤ := by
  have hm : (genGeneral : SPMF GTree).mass = 1 := genGeneral_terminates
  have hL : (listOf genGeneral : SPMF (List GTree)).mass = 1 := by
    rw [← hm]; conv_rhs => rw [genGeneral]
    exact mass_bind_pure.symm
  set S := expect (listOf genGeneral : SPMF (List GTree))
    (fun cs => ((cs.map GTree.size).sum : ℝ≥0∞))
  have hE : expect (genGeneral : SPMF GTree) (fun t => (t.size : ℝ≥0∞)) = S + 1 := by
    conv_lhs => rw [genGeneral]
    rw [expect_bind]
    simp only [expect_pure, GTree.size_node, Nat.cast_add, Nat.cast_one]
    rw [expect_add_const, hL, one_mul]
  have hS : S = 1 / 2 * (expect (genGeneral : SPMF GTree) (fun t => (t.size : ℝ≥0∞)) + S) := by
    conv_lhs => simp only [S]; rw [expect_listOf_step]
    simp only [List.map_nil, List.sum_nil, Nat.cast_zero, mul_zero, zero_add, List.map_cons,
      List.sum_cons, Nat.cast_add, expect_const_add, expect_add_const, hL, hm, one_mul]
    rfl
  rw [hE] at hS ⊢
  by_contra htop
  have hSt : S ≠ ⊤ := fun h => htop (by rw [h, top_add])
  have h2 : S + S = S + (S + 1) := by
    calc S + S = 2 * S := (two_mul S).symm
      _ = 2 * (1 / 2) * (S + 1 + S) := by rw [mul_assoc, ← hS]
      _ = S + (S + 1) := by
        rw [ENNReal.mul_div_cancel (by norm_num) (by norm_num), one_mul, add_comm]
  have := (ENNReal.add_right_inj hSt).1 h2
  have h3 : S + 0 = S + 1 := by rw [add_zero]; exact this
  exact absurd ((ENNReal.add_right_inj hSt).1 h3) zero_ne_one

end Boltzmann.CanouDarrasse
