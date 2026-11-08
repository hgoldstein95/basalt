/-
Copyright (c) 2026 Ernest Ng. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Ernest Ng
-/
module

import Mathlib.Tactic.Basify
public import Basalt
public import BasaltExamples.Boltzmann.DuchonEtAl

/-!
# Singular Boltzmann Samplers for Trees

The three tree samplers of Canou and Darrasse, "Fast and Sound Random Generation for Automated
Testing and Benchmarking in Objective Caml" (ML '09, Figs. 1–3), run at the singularity `x = ρ`,
where every branching probability is rational and every sampler is critical: each is uniform within
a size, terminates almost surely, and has infinite expected size. Their abort-and-retry sampler
(§3.3) has the generator's law conditioned on the size window.
-/

@[expose] public section

open RandomChoice SPMF
open scoped ENNReal

namespace Boltzmann.CanouDarrasse

/-! ## Ternary trees: `T = Z + T × T × T`

Fig. 1's grammar puts the atom `Z` only at leaves, so `|t|` counts leaves. At `ρ = 2√3/9`,
`T(ρ) = 1/√3` and the leaf probability is
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
    rw [(apply_eq_zero_iff _ TTree.leaf).2 (by simp)]
    simp [TTree.size, TTree.internal]
  | node a b c iha ihb ihc =>
    rw [genTernary, bind_apply, tsum_bool]
    simp only [Bool.false_eq_true, ↓reduceIte, coin_false hp0 hp1, coin_true hp0 hp1]
    rw [bind_apply_of_unique a (by simp), bind_apply_of_unique b (by simp),
      bind_apply_of_unique c (by simp), iha, ihb, ihc]
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
  mass_fixpoint using SPMF.LfpIsOne.poly ![pr p, 0, 0, 1 - pr p]
    (by simp [Fin.sum_univ_succ, add_tsub_cancel_of_le hx1])
    (by simp [Fin.sum_univ_succ]; basify; rw [max_eq_left (by linarith)]; linarith)
    (lt_of_lt_of_le (by norm_num) hx)
  coin_goals p hp0 hp1
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  exact le_of_eq (by simp; ring)

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
surely exactly when `p ≥ 2/3`. -/
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

/-! ## Unary-binary trees: `T = Z + Z × T + Z × T × T`

At `ρ = 1/3`, `T(ρ) = 1`, and the leaf, unary, and binary branches each have probability `1/3`. -/

/-- Unary-binary (Motzkin) trees, the paper's one-two trees. -/
inductive UBTree where
  | leaf
  | unary (t : UBTree)
  | binary (l r : UBTree)
deriving DecidableEq

/-- The size: every node is an atom. -/
def UBTree.size : UBTree → Nat
  | .leaf => 1
  | .unary t => t.size + 1
  | .binary l r => l.size + r.size + 1

def UBTree.leaves : UBTree → Nat
  | .leaf => 1
  | .unary t => t.leaves
  | .binary l r => l.leaves + r.leaves

def UBTree.unaries : UBTree → Nat
  | .leaf => 0
  | .unary t => t.unaries + 1
  | .binary l r => l.unaries + r.unaries

def UBTree.binaries : UBTree → Nat
  | .leaf => 0
  | .unary t => t.binaries
  | .binary l r => l.binaries + r.binaries + 1

theorem UBTree.leaves_eq (t : UBTree) : t.leaves = t.binaries + 1 := by
  induction t <;> simp only [UBTree.leaves, UBTree.binaries, *]; omega

theorem UBTree.size_eq (t : UBTree) : t.size = t.leaves + t.unaries + t.binaries := by
  induction t <;> simp only [UBTree.size, UBTree.leaves, UBTree.unaries, UBTree.binaries, *] <;>
    omega

/-- Fig. 3's `UBTree ()`, with the three branches weighted `a`, `b`, `c` (at `ρ`, all equal). -/
def genUnaryBinaryW [Gen G] (a b c : Nat) (h : 0 < a + b + c) : G UBTree :=
  frequency! [
    (a, fun _ => pure .leaf),
    (b, fun _ => do return .unary (← genUnaryBinaryW a b c h)),
    (c, fun _ => do return .binary (← genUnaryBinaryW a b c h) (← genUnaryBinaryW a b c h))]
    (by simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; omega)
partial_fixpoint

theorem three_pos : 0 < 1 + 1 + 1 := by norm_num

theorem genUnaryBinaryW_apply (h : 0 < a + b + c) (t : UBTree) :
    (genUnaryBinaryW a b c h : SPMF UBTree) t
      = (a / (a + b + c : ℝ≥0∞)) ^ t.leaves * (b / (a + b + c : ℝ≥0∞)) ^ t.unaries
        * (c / (a + b + c : ℝ≥0∞)) ^ t.binaries := by
  induction t with
  | leaf =>
    rw [genUnaryBinaryW, frequencyWith_eq, frequency_apply]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, pure_apply, ↓reduceIte]
    rw [(apply_eq_zero_iff _ UBTree.leaf).2 (by simp),
      (apply_eq_zero_iff _ UBTree.leaf).2 (by simp)]
    simp [UBTree.leaves, UBTree.unaries, UBTree.binaries, ENNReal.div_eq_inv_mul, add_assoc]
  | unary t ih =>
    rw [genUnaryBinaryW, frequencyWith_eq, frequency_apply]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, pure_apply, reduceCtorEq,
      ↓reduceIte]
    rw [bind_pure_apply_of_injective (fun _ _ h => UBTree.unary.inj h), ih,
      (apply_eq_zero_iff _ (UBTree.unary t)).2 (by simp)]
    simp only [UBTree.leaves, UBTree.unaries, UBTree.binaries, ENNReal.div_eq_inv_mul, add_zero,
      Nat.cast_add,
      ← add_assoc]
    ring
  | binary l r ihl ihr =>
    rw [genUnaryBinaryW, frequencyWith_eq, frequency_apply]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, pure_apply, reduceCtorEq,
      ↓reduceIte]
    rw [(apply_eq_zero_iff _ (UBTree.binary l r)).2 (by simp), bind_apply_of_unique l (by simp),
      bind_apply_of_unique r (by simp), ihl, ihr]
    simp only [pure_apply, ↓reduceIte, mul_one, UBTree.leaves, UBTree.unaries, UBTree.binaries,
      ENNReal.div_eq_inv_mul, add_zero, Nat.cast_add, ← add_assoc]
    ring

/-- At `ρ = 1/3` all three weights are equal; a tree of size `n` has mass `(1/3) ^ n`: the
Boltzmann form with `T(ρ) = 1`. -/
theorem genUnaryBinary_boltzmann :
    IsBoltzmann (genUnaryBinaryW 1 1 1 three_pos : SPMF UBTree) UBTree.size (1/3) 1 := by
  intro t
  rw [genUnaryBinaryW_apply, div_one, UBTree.size_eq, pow_add, pow_add]
  norm_num

/-- **Terminates almost surely at the singularity**: one, two, or no children, each with probability
`1/3`, is mean offspring exactly `1`. -/
theorem genUnaryBinary_terminates :
    IsAlmostSurelyTerminating (genUnaryBinaryW 1 1 1 three_pos : SPMF UBTree) := by
  mass_fixpoint using SPMF.LfpIsOne.poly ![1 / 3, 1 / 3, 1 / 3]
  norm_num [Fin.sum_univ_succ, sq, ENNReal.div_eq_inv_mul, mul_add]

/-- **Infinite expected size at the singularity**: unfolded once, `E = 1 + E`. -/
theorem genUnaryBinary_expected_size :
    expect (genUnaryBinaryW 1 1 1 three_pos : SPMF UBTree) (fun t => (t.size : ℝ≥0∞)) = ⊤ := by
  have hm : (genUnaryBinaryW 1 1 1 three_pos : SPMF UBTree).mass = 1 := genUnaryBinary_terminates
  have hstep : expect (genUnaryBinaryW 1 1 1 three_pos : SPMF UBTree) (fun t => (t.size : ℝ≥0∞))
      = expect (genUnaryBinaryW 1 1 1 three_pos : SPMF UBTree) (fun t => (t.size : ℝ≥0∞)) := rfl
  conv_rhs at hstep => rw [genUnaryBinaryW]
  rw [frequencyWith_eq, expect_frequency] at hstep
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, expect_bind, expect_pure,
    UBTree.size, Nat.cast_add, Nat.cast_one, add_assoc, expect_const_add, expect_add_const, hm,
    one_mul, mul_one] at hstep
  generalize expect (genUnaryBinaryW 1 1 1 three_pos : SPMF UBTree) (fun t => (t.size : ℝ≥0∞)) = E
    at hstep ⊢
  rw [show (1 + (E + (1 + (E + (E + (1 + 0))))) : ℝ≥0∞) = 3 * (E + 1) by ring,
    show (1 + (1 + (1 + ((0 : ℕ) : ℝ≥0∞))) : ℝ≥0∞) = 3 by norm_num,
    mul_comm, mul_div_assoc, ENNReal.div_self (by norm_num) (by norm_num), mul_one] at hstep
  by_contra hE
  exact absurd ((ENNReal.add_right_inj hE).1 (hstep.symm.trans (add_zero E).symm)) one_ne_zero

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

/-- `genUnaryBinaryW` with a budget of `k` atoms: it gives up (`none`) as soon as the tree would
exceed the budget, and returns the budget left. -/
def genUnaryBinaryCeil [Gen G] (a b c : Nat) (h : 0 < a + b + c) (k : Nat) :
    G (Option (UBTree × Nat)) := do
  if k = 0 then return none
  frequency! [
    (a, fun _ => pure (some (.leaf, k - 1))),
    (b, fun _ => do
      match ← genUnaryBinaryCeil a b c h (k - 1) with
      | none => return none
      | some (t, k') => return some (.unary t, k')),
    (c, fun _ => do
      match ← genUnaryBinaryCeil a b c h (k - 1) with
      | none => return none
      | some (l, k') =>
        match ← genUnaryBinaryCeil a b c h k' with
        | none => return none
        | some (r, k'') => return some (.binary l r, k''))]
    (by simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; omega)
partial_fixpoint

/-- One round: a ceiled draw, kept if it reaches the lower bound. -/
def roundUnaryBinary [Gen G] (a b c : Nat) (h : 0 < a + b + c) (lo hi : Nat) :
    G (Option UBTree) := do
  match ← genUnaryBinaryCeil a b c h hi with
  | some (t, _) => return if lo ≤ t.size then some t else none
  | none => return none

/-- The abort-and-retry sampler. -/
def ceiledUnaryBinary [Gen G] (a b c : Nat) (h : 0 < a + b + c) (lo hi : Nat) : G UBTree :=
  (fun o => o.getD .leaf) <$> suchThat (roundUnaryBinary a b c h lo hi) Option.isSome

theorem genUnaryBinaryW_leaf (h : 0 < a + b + c) :
    (genUnaryBinaryW a b c h : SPMF UBTree) .leaf = a / (a + b + c : ℝ≥0∞) := by
  simp [genUnaryBinaryW_apply, UBTree.leaves, UBTree.unaries, UBTree.binaries]

theorem genUnaryBinaryW_unary (h : 0 < a + b + c) (t : UBTree) :
    (genUnaryBinaryW a b c h : SPMF UBTree) (.unary t)
      = b / (a + b + c : ℝ≥0∞) * (genUnaryBinaryW a b c h : SPMF UBTree) t := by
  simp only [genUnaryBinaryW_apply, UBTree.leaves, UBTree.unaries, UBTree.binaries]; ring

theorem genUnaryBinaryW_binary (h : 0 < a + b + c) (l r : UBTree) :
    (genUnaryBinaryW a b c h : SPMF UBTree) (.binary l r)
      = c / (a + b + c : ℝ≥0∞)
        * ((genUnaryBinaryW a b c h : SPMF UBTree) l
          * (genUnaryBinaryW a b c h : SPMF UBTree) r) := by
  simp only [genUnaryBinaryW_apply, UBTree.leaves, UBTree.unaries, UBTree.binaries]; ring

theorem genUnaryBinaryCeil_apply (h : 0 < a + b + c) (t : UBTree) :
    ∀ k k', (genUnaryBinaryCeil a b c h k : SPMF _) (some (t, k'))
      = if t.size ≤ k ∧ k' = k - t.size then (genUnaryBinaryW a b c h : SPMF UBTree) t else 0 := by
  induction t with
  | leaf =>
    intro k k'
    rcases k with _ | j
    · rw [genUnaryBinaryCeil]; simp [UBTree.size]
    rw [genUnaryBinaryCeil]
    simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    rw [frequencyWith_eq, frequency_apply]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    rw [ceil_map_apply_of_ne (g := UBTree.unary) (by rfl) (by intros; rfl)
        (by intros; exact UBTree.noConfusion),
      ceil_bind_apply_of_ne (g := UBTree.binary) (by rfl) (by intros; rfl) (by intros; rfl)
        (by intros; rfl) (by intros; exact UBTree.noConfusion), genUnaryBinaryW_leaf]
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq, true_and, mul_zero, add_zero,
      Nat.cast_add, ← add_assoc]
    split_ifs with h1 h2 h2 <;> simp only [UBTree.size] at * <;> first | omega | simp
  | unary t ih =>
    intro k k'
    rcases k with _ | j
    · rw [genUnaryBinaryCeil]; simp [UBTree.size]
    rw [genUnaryBinaryCeil]
    simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    rw [frequencyWith_eq, frequency_apply]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    rw [ceil_map_apply (g := UBTree.unary) (fun _ _ h => UBTree.unary.inj h) (by rfl)
        (by intros; rfl),
      ceil_bind_apply_of_ne (g := UBTree.binary) (by rfl) (by intros; rfl) (by intros; rfl)
        (by intros; rfl) (by intros; exact UBTree.noConfusion), ih, genUnaryBinaryW_unary]
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq, reduceCtorEq, false_and, ↓reduceIte,
      mul_zero, zero_add, add_zero, Nat.cast_add, ← add_assoc]
    split_ifs with h1 h2 h2 <;> simp only [UBTree.size] at * <;>
      first | omega | simp | (simp only [div_eq_mul_inv]; ring)
  | binary l r ihl ihr =>
    intro k k'
    rcases k with _ | j
    · rw [genUnaryBinaryCeil]; simp [UBTree.size]
    rw [genUnaryBinaryCeil]
    simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    rw [frequencyWith_eq, frequency_apply]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    rw [ceil_map_apply_of_ne (g := UBTree.unary) (by rfl) (by intros; rfl)
        (by intros; exact UBTree.noConfusion),
      ceil_bind_apply (g := UBTree.binary) (fun _ _ _ _ h => UBTree.binary.inj h) (by rfl)
        (by intros; rfl) (by intros; rfl) (by intros; rfl),
      tsum_eq_single (j - l.size) fun k1 hk1 => by
        rw [ihl, ite_eq_right_iff.2 fun h => absurd h (by omega), zero_mul],
      ihl,
      ihr, genUnaryBinaryW_binary]
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq, reduceCtorEq, false_and, ↓reduceIte,
      mul_zero, zero_add, Nat.cast_add, ← add_assoc, and_true]
    split_ifs with h1 h2 h3 h3 <;> simp only [UBTree.size] at * <;>
      first | omega | simp | (simp only [div_eq_mul_inv]; ring)

/-- The ceiled sampler always halts: the budget shrinks on every call. -/
theorem genUnaryBinaryCeil_mass (h : 0 < a + b + c) (k : Nat) :
    (genUnaryBinaryCeil a b c h k : SPMF _).mass = 1 := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  rcases k with _ | j
  · rw [genUnaryBinaryCeil]; simp
  rw [genUnaryBinaryCeil]
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
        rw [genUnaryBinaryCeil_apply] at hne
        by_contra hk
        exact hne (ite_eq_right_iff.2 fun h => absurd h (by omega))
      rw [mass_bind_of_mass_one (by rintro (_ | ⟨r, k''⟩) _ <;> simp), ih k' (by omega)]

/-- One round keeps each tree in the window with `genUnaryBinaryW`'s mass. -/
theorem roundUnaryBinary_some (h : 0 < a + b + c) (lo hi : Nat) (t : UBTree) :
    (roundUnaryBinary a b c h lo hi : SPMF _) (some t)
      = if lo ≤ t.size ∧ t.size ≤ hi then (genUnaryBinaryW a b c h : SPMF UBTree) t else 0 := by
  rw [roundUnaryBinary, bind_apply, tsum_option, ENNReal.tsum_prod', tsum_eq_single t fun t' ht' =>
    ENNReal.tsum_eq_zero.2 fun k => by dsimp only; split_ifs <;> simp [Ne.symm ht'],
    tsum_eq_single (hi - t.size) fun k hk => by
      rw [genUnaryBinaryCeil_apply, ite_eq_right_iff.2 fun h => absurd h (by omega), zero_mul]]
  simp only [pure_apply, reduceCtorEq, ↓reduceIte, mul_zero, zero_add, genUnaryBinaryCeil_apply]
  by_cases h1 : lo ≤ t.size <;> by_cases h2 : t.size ≤ hi <;> simp [h1, h2]

/-- Whether a tree's size lies between `lo` and `hi`. -/
def between (lo hi : Nat) (t : UBTree) : Bool := decide (lo ≤ t.size ∧ t.size ≤ hi)

theorem roundUnaryBinary_mass (h : 0 < a + b + c) (lo hi : Nat) :
    (roundUnaryBinary a b c h lo hi : SPMF _).mass = 1 := by
  rw [roundUnaryBinary, mass_bind_of_mass_one (by rintro (_ | ⟨t, k⟩) _ <;> simp),
    genUnaryBinaryCeil_mass]

/-- **The law of abort-and-retry**, for every weighting: `genUnaryBinaryW` conditioned on the
window. -/
theorem ceiledUnaryBinary_apply (h : 0 < a + b + c) (lo hi : Nat) (t : UBTree) :
    (ceiledUnaryBinary a b c h lo hi : SPMF UBTree) t
      = (if between lo hi t then (genUnaryBinaryW a b c h : SPMF UBTree) t else 0)
        / prob (genUnaryBinaryW a b c h : SPMF UBTree) {t | between lo hi t = true} := by
  classical
  have hsum := roundUnaryBinary_mass h lo hi
  rw [mass, tsum_option] at hsum
  have hQ : 1 - (roundUnaryBinary a b c h lo hi : SPMF _) none
      = prob (genUnaryBinaryW a b c h : SPMF UBTree) {t | between lo hi t = true} := by
    rw [← hsum, ENNReal.add_sub_cancel_left (apply_ne_top _ _), prob_eq_tsum_ite]
    exact tsum_congr fun t => by rw [roundUnaryBinary_some]; simp [between]
  rw [ceiledUnaryBinary, getD_suchThat_isSome_apply, hQ, roundUnaryBinary_some]
  simp [between]

/-! ## Rose trees: `T = Z × Seq(T)`

At `ρ = 1/4`, `T(ρ) = 1/2`, so the number of children is geometric with parameter `1/2`: exactly the
length law of Basalt's `listOf`. The sampler is the naive recursive generator `node <$> listOf gen`.
-/

/-- Unlabelled rose trees (general plane trees), the paper's general trees. -/
inductive RoseTree where
  | node (cs : List RoseTree)

/-- The size: the number of nodes. -/
def RoseTree.size : RoseTree → Nat
  | .node cs => (cs.attach.map fun ⟨c, _⟩ => c.size).sum + 1

theorem RoseTree.size_node (cs : List RoseTree) :
    (RoseTree.node cs).size = (cs.map RoseTree.size).sum + 1 := by
  rw [RoseTree.size]
  congr 2
  conv_rhs => rw [← List.attach_map_subtype_val cs, List.map_map]
  rfl

private theorem prod_map_eq {f : RoseTree → ℝ≥0∞} :
    ∀ cs : List RoseTree, (∀ c ∈ cs, f c = 2 * (1 / 4) ^ c.size) →
      (cs.map f).prod = 2 ^ cs.length * (1 / 4) ^ (cs.map RoseTree.size).sum
  | [], _ => by simp
  | c :: cs, h => by
    rw [List.map_cons, List.prod_cons, h c (by simp),
      prod_map_eq cs fun c' hc' => h c' (by simp [hc'])]
    simp only [List.length_cons, List.map_cons, List.sum_cons, pow_succ, pow_add]
    ring

/-- Fig. 3's `RoseTree ()`: a node, then a geometric number of independent subtrees. -/
def genRoseTree [Gen G] : G RoseTree := do
  return .node (← listOf genRoseTree)
partial_fixpoint

/-- **The Boltzmann form**: a tree of `n` nodes has mass `ρ ^ n / T(ρ) = 2 (1/4) ^ n`. -/
theorem genRoseTree_apply : ∀ t : RoseTree, (genRoseTree : SPMF RoseTree) t = 2 * (1 / 4) ^ t.size
  | .node cs => by
    have ih : ∀ c ∈ cs, (genRoseTree : SPMF RoseTree) c = 2 * (1 / 4) ^ c.size :=
      fun c _ => genRoseTree_apply c
    rw [genRoseTree, bind_pure_apply_of_injective (fun _ _ h => RoseTree.node.inj h), listOf_apply,
      RoseTree.size_node, prod_map_eq cs ih, pow_succ, pow_add, pow_one]
    have h2 : (1 / 2 : ℝ≥0∞) ^ cs.length * 2 ^ cs.length = 1 := by
      rw [← mul_pow, one_div, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_pow]
    calc (1 / 2 : ℝ≥0∞) ^ cs.length * (1 / 2)
          * (2 ^ cs.length * (1 / 4) ^ (cs.map RoseTree.size).sum)
        = ((1 / 2) ^ cs.length * 2 ^ cs.length) * (1 / 2)
          * (1 / 4) ^ (cs.map RoseTree.size).sum := by
          ring
      _ = 2 * ((1 / 4) ^ (cs.map RoseTree.size).sum * (1 / 4)) := by
          rw [h2, one_mul]
          rw [show (1 / 2 : ℝ≥0∞) = 2 * (1 / 4) by
            rw [← ENNReal.toReal_eq_toReal_iff' (by simp) (by simp [ENNReal.mul_eq_top])]
            simp; norm_num]
          ring

/-- **Terminates almost surely**: the mass satisfies `m = 1/2 + m²/2`, whose only root in `[0, 1]`
is the double root `1` of the critical case — here the unfolding alone decides. -/
theorem genRoseTree_terminates : IsAlmostSurelyTerminating (genRoseTree : SPMF RoseTree) := by
  have hstep := mass_listOf_step (genRoseTree : SPMF RoseTree)
  have hm : (genRoseTree : SPMF RoseTree).mass
      = (listOf genRoseTree : SPMF (List RoseTree)).mass := by
    conv_lhs => rw [genRoseTree]
    exact mass_bind_pure
  rw [← hm] at hstep
  replace hstep := hstep.symm.le
  have hm1 := mass_le_one (genRoseTree : SPMF RoseTree)
  unfold IsAlmostSurelyTerminating
  generalize (genRoseTree : SPMF RoseTree).mass = m at *
  clear hm
  basify
  nlinarith [sq_nonneg (m - 1)]

/-- **Infinite expected size**: with `S` the expected size of the children, `E = S + 1` and
`S = (E + S) / 2`. -/
theorem genRoseTree_expected_size :
    expect (genRoseTree : SPMF RoseTree) (fun t => (t.size : ℝ≥0∞)) = ⊤ := by
  have hm : (genRoseTree : SPMF RoseTree).mass = 1 := genRoseTree_terminates
  have hL : (listOf genRoseTree : SPMF (List RoseTree)).mass = 1 := by
    rw [← hm]; conv_rhs => rw [genRoseTree]
    exact mass_bind_pure.symm
  set S := expect (listOf genRoseTree : SPMF (List RoseTree))
    (fun cs => ((cs.map RoseTree.size).sum : ℝ≥0∞))
  have hE : expect (genRoseTree : SPMF RoseTree) (fun t => (t.size : ℝ≥0∞)) = S + 1 := by
    conv_lhs => rw [genRoseTree]
    rw [expect_bind]
    simp only [expect_pure, RoseTree.size_node, Nat.cast_add, Nat.cast_one]
    rw [expect_add_const, hL, one_mul]
  have hS : S = 1 / 2 * (expect (genRoseTree : SPMF RoseTree) (fun t => (t.size : ℝ≥0∞)) + S) := by
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
