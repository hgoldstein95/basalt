/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Ernest Ng
-/
module

public import Basalt

/-!
# Branching Processes for QuickCheck Generators

This file formalizes some results
from "Branching Processes for QuickCheck Generators" (Mista et al. Haskell '18).
In particular, we prove results about the termination probability of an automatically
derived generator (Appendix B.1 of their paper), and the exact expected no. of constructors
for a few particular generators (sections 3 & 4 from the paper), and Theorem 1's prediction from
the mean matrix of types for the mutually recursive types of section 6.
-/

@[expose] public section

open RandomChoice
open scoped ENNReal NNReal

namespace BranchingProcesses

/-! ## Termination of `derive` generators (Appendix B.1)

A termination probability below `1` is a least fixed point below `1`: fixpoint induction bounds it
above by a fixed point of the one-step mass equation, and unfolding once bounds it below by that
equation, whose fixed points are `1` and the one the induction found. -/

/-- The data type of Appendix B.1. -/
inductive T : Type where
  | a : T
  | b : T → T → T
  | c : T → T → T

/-- `derive`'s generator for `T`: a uniform choice of constructor, each recursive argument filled by
a recursive call. -/
def genT [Gen G] : G T :=
  oneOf! [
    fun _ => pure .a,
    fun _ => do
      let l ← genT
      let r ← genT
      return .b l r,
    fun _ => do
      let l ← genT
      let r ← genT
      return .c l r]
partial_fixpoint

theorem genT.mass_le : (genT : SPMF T).mass ≤ 1 / 2 := by
  rw [← SPMF.expect_one, SPMF.expect_eq_obs]
  walk fixpoint
  norm_num only [List.sum_cons, List.sum_nil, List.length_cons, List.length_nil]
  basify
  nlinarith

/-- One unfolding: the mass `d` satisfies `d ≥ 1/3 + 2/3 · d²`, the paper's generation
recurrence. -/
theorem genT.le_mass_step :
    1 / 3 + 2 / 3 * (genT : SPMF T).mass ^ 2 ≤ (genT : SPMF T).mass := by
  rw [← SPMF.expect_one, SPMF.expect_eq_obs]
  conv_rhs => rw [genT]
  walk [le_refl (SPMF.expectObs.spec (genT : SPMF T) fun _ => 1)]
  have hm : (SPMF.expectObs.spec (genT : SPMF T) fun _ => 1) ≤ 1 :=
    (SPMF.expect_one _).trans_le (SPMF.mass_le_one _)
  generalize SPMF.expectObs.spec (genT : SPMF T) (fun _ => 1) = m at *
  norm_num only [List.sum_cons, List.sum_nil, List.length_cons, List.length_nil]
  basify
  nlinarith

/-- **Appendix B.1**: "the extinction probability [is] the smallest `d` such that
`d = (1/3) + (2/3) · d²` … In this case `d = 1/2`." -/
theorem genT.mass_eq : (genT : SPMF T).mass = 1 / 2 := by
  have hm := SPMF.mass_le_one (genT : SPMF T)
  have hle := genT.mass_le
  have hstep := genT.le_mass_step
  generalize (genT : SPMF T).mass = m at *
  basify
  by_contra hne
  have hlt : m < 1 / 2 := lt_of_le_of_ne hle hne
  nlinarith [mul_pos (sub_pos.mpr hlt) (show (0 : ℝ) < 1 - m by linarith)]

/-- `derive`'s generator for a type with one leaf and `k` binary recursive constructors, which
differ only in their label, so the `k` are one branch of weight `k`. `genT` is `k = 2`. -/
def genTk [Gen G] (k : Nat) : G T :=
  frequency! [
    (1, fun _ => pure .a),
    (k, fun _ => do
      let l ← genTk k
      let r ← genTk k
      return .b l r)] (by simp)
partial_fixpoint

theorem genTk.mass_le {k : Nat} (hk : 1 ≤ k) : (genTk k : SPMF T).mass ≤ 1 / k := by
  rw [← SPMF.expect_one, SPMF.expect_eq_obs]
  walk fixpoint
  simp only [List.map, List.sum_cons, List.sum_nil, add_zero, Nat.cast_one, one_mul, Nat.cast_add]
  have hk0 : (k : ℝ≥0∞) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have hkt : (k : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top k
  rw [one_div, ← mul_assoc, ENNReal.mul_inv_cancel hk0 hkt, one_mul,
    ENNReal.div_le_iff (by simp) (by simp), mul_add, mul_one, ENNReal.inv_mul_cancel hk0 hkt,
    add_comm]

theorem genTk.le_mass_step (k : Nat) :
    (1 + k * (genTk k : SPMF T).mass ^ 2) / (1 + k) ≤ (genTk k : SPMF T).mass := by
  rw [← SPMF.expect_one, SPMF.expect_eq_obs]
  conv_rhs => rw [genTk]
  walk [le_refl (SPMF.expectObs.spec (genTk k : SPMF T) fun _ => 1)]
  simp only [List.map, List.sum_cons, List.sum_nil, add_zero, Nat.cast_one, one_mul, Nat.cast_add,
    sq]
  exact le_rfl

/-- **Appendix B.1**: "this non terminating behavior gets worse as we increase … the number of
recursive constructors": with `k` of them the generator terminates with probability `1 / k`. -/
theorem genTk.mass_eq {k : Nat} (hk : 1 ≤ k) : (genTk k : SPMF T).mass = 1 / k := by
  have hm := SPMF.mass_le_one (genTk k : SPMF T)
  have hle := genTk.mass_le hk
  have hstep := genTk.le_mass_step k
  generalize (genTk k : SPMF T).mass = m at *
  have hk0 : (k : ℝ≥0∞) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  rw [ENNReal.div_le_iff (by simp) (by simp)] at hstep
  rw [ENNReal.le_div_iff_mul_le (.inl hk0) (.inl (ENNReal.natCast_ne_top k))] at hle
  rw [ENNReal.eq_div_iff hk0 (ENNReal.natCast_ne_top k)]
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  basify
  by_contra hne
  have hlt : m * k < 1 := lt_of_le_of_ne hle (by contrapose! hne; linarith)
  nlinarith [mul_pos (sub_pos.mpr hlt) (show (0 : ℝ) < 1 - m by nlinarith)]

/-! ## MegaDeTH's generator (§2.2, §3) -/

/-- The binary trees of §2. -/
inductive Tree : Type where
  | leafA | leafB | leafC
  | node : Tree → Tree → Tree

def Tree.nodes : Tree → Nat
  | .node l r => l.nodes + r.nodes + 1
  | _ => 0

/-- MegaDeTH's generator for `Tree` (Figure 2): uniform, halving the size at each `node`. -/
def genMegaDeTH [Gen G] (n : Nat) : G Tree :=
  match n with
  | 0 => oneOf! [fun _ => pure .leafA, fun _ => pure .leafB, fun _ => pure .leafC]
  | n + 1 => oneOf! [
      fun _ => pure .leafA, fun _ => pure .leafB, fun _ => pure .leafC,
      fun _ => do
        let l ← genMegaDeTH ((n + 1) / 2)
        let r ← genMegaDeTH ((n + 1) / 2)
        return .node l r]
partial_fixpoint

/-- The expected number of `node`s at size `n` -/
noncomputable def megaNodes : Nat → ℝ≥0∞
  | 0 => 0
  | n + 1 => (1 + 2 * megaNodes ((n + 1) / 2)) / 4

theorem genMegaDeTH.expect_nodes_le (n : Nat) :
    SPMF.expect (genMegaDeTH n) (fun t => (t.nodes : ℝ≥0∞)) ≤ megaNodes n := by
  rw [SPMF.expect_eq_obs]
  walk fixpoint
  all_goals simp [Tree.nodes, megaNodes, two_mul, add_assoc]

theorem genMegaDeTH.le_expect_nodes (n : Nat) (k : ℝ≥0∞) :
    k + megaNodes n ≤
      SPMF.expectObs.spec (genMegaDeTH n : SPMF Tree) (fun t => k + (t.nodes : ℝ≥0∞)) := by
  induction n using Nat.strong_induction_on generalizing k with
  | _ n ih =>
    cases n with
    | zero =>
      conv_rhs => rw [genMegaDeTH]
      walk
      simp only [Tree.nodes, megaNodes, List.sum_cons, List.sum_nil, List.length_cons,
        List.length_nil, Nat.cast_zero, add_zero]
      rw [ENNReal.le_div_iff_mul_le (by norm_num) (by norm_num)]
      apply le_of_eq
      push_cast
      ring
    | succ n =>
      conv_rhs => rw [genMegaDeTH]
      walk [ih ((n + 1) / 2) (by omega)]
      simp only [Tree.nodes, megaNodes, List.sum_cons, List.sum_nil, List.length_cons,
        List.length_nil, Nat.cast_zero, add_zero]
      push_cast
      rw [ENNReal.le_div_iff_mul_le (by norm_num) (by norm_num), add_mul,
        ENNReal.div_mul_cancel (by norm_num) (by norm_num)]
      apply le_of_eq
      ring

/-- The expected number of `node`s is exactly `megaNodes n`. -/
theorem genMegaDeTH.expect_nodes (n : Nat) :
    SPMF.expect (genMegaDeTH n) (fun t => (t.nodes : ℝ≥0∞)) = megaNodes n := by
  refine le_antisymm (genMegaDeTH.expect_nodes_le n) ?_
  simpa [SPMF.expect_eq_obs] using genMegaDeTH.le_expect_nodes n 0

/-- The expected no. of `node`s when `size = 10` is 15 / 32 (`genMegaDeTH.expect_nodes`). -/
theorem megaNodes_ten : megaNodes 10 = 15 / 32 := by
  simp [megaNodes]
  basify
  norm_num

/-! ## Dragen's generator (§4) -/

/-- The data type of §3–4, with two recursive constructors. -/
inductive Tree' : Type where
  | leaf
  | nodeA : Tree' → Tree' → Tree'
  | nodeB : Tree' → Tree'

def Tree'.countA : Tree' → Nat
  | .leaf => 0
  | .nodeA l r => l.countA + r.countA + 1
  | .nodeB t => t.countA

def Tree'.countB : Tree' → Nat
  | .leaf => 0
  | .nodeA l r => l.countB + r.countB
  | .nodeB t => t.countB + 1

/-- Dragen's generator for `Tree'` (Figure 5), at the probabilities of §4: `pLeaf = 0.2`,
`pNodeA = 0.5`, `pNodeB = 0.3`. -/
def genDragen [Gen G] (n : Nat) : G Tree' :=
  match n with
  | 0 => pure .leaf
  | n + 1 => frequency! [
      (2, fun _ => pure .leaf),
      (5, fun _ => do
        let l ← genDragen n
        let r ← genDragen n
        return .nodeA l r),
      (3, fun _ => do
        let t ← genDragen n
        return .nodeB t)] (by simp)
partial_fixpoint

/-- The expected number of `nodeA`s at size `n` -/
noncomputable def dragenA : Nat → ℝ≥0
  | 0 => 0
  | n + 1 => (5 + 13 * dragenA n) / 10

/-- The expected number of `nodeB`s at size `n` -/
noncomputable def dragenB : Nat → ℝ≥0
  | 0 => 0
  | n + 1 => (3 + 13 * dragenB n) / 10

/-- At size `n`, the expected number of `nodeA`s is at most `dragenA n`: one step adds `1` for a
`nodeA` (probability `1/2`) and recurses into two subtrees, or recurses into one (`nodeB`, `3/10`),
so the mean grows by the type's mean offspring `2 · 1/2 + 3/10 = 13/10` per level. -/
theorem genDragen.expect_countA_le (n : Nat) :
    SPMF.expect (genDragen n) (fun t => (t.countA : ℝ≥0∞)) ≤ (dragenA n : ℝ≥0∞) := by
  rw [SPMF.expect_eq_obs]
  walk fixpoint
  all_goals simp [Tree'.countA, dragenA, ENNReal.coe_div]
  all_goals (apply le_of_eq; ring_nf)

/-- At size `n`, the expected number of `nodeB`s is at most `dragenB n`: the same recurrence as
`genDragen.expect_countA_le`, with `1` added for a `nodeB` (probability `3/10`) instead. -/
theorem genDragen.expect_countB_le (n : Nat) :
    SPMF.expect (genDragen n) (fun t => (t.countB : ℝ≥0∞)) ≤ (dragenB n : ℝ≥0∞) := by
  rw [SPMF.expect_eq_obs]
  walk fixpoint
  all_goals simp [Tree'.countB, dragenB, ENNReal.coe_div]
  all_goals (apply le_of_eq; ring_nf)

theorem genDragen.le_expect_countA (n : Nat) (k : ℝ≥0∞) :
    k + (dragenA n : ℝ≥0∞) ≤
      SPMF.expectObs.spec (genDragen n : SPMF Tree') (fun t => k + (t.countA : ℝ≥0∞)) := by
  induction n generalizing k with
  | zero =>
    conv_rhs => rw [genDragen]
    walk
    simp [Tree'.countA, dragenA]
  | succ n ih =>
    conv_rhs => rw [genDragen]
    walk [ih]
    simp only [Tree'.countA, dragenA, List.map, List.sum_cons, List.sum_nil, Nat.cast_ofNat,
      add_zero, Nat.cast_zero, ENNReal.coe_div (by norm_num : (10 : ℝ≥0) ≠ 0)]
    push_cast
    rw [ENNReal.le_div_iff_mul_le (by norm_num) (by norm_num), add_mul,
      ENNReal.div_mul_cancel (by norm_num) (by norm_num)]
    apply le_of_eq
    ring

theorem genDragen.le_expect_countB (n : Nat) (k : ℝ≥0∞) :
    k + (dragenB n : ℝ≥0∞) ≤
      SPMF.expectObs.spec (genDragen n : SPMF Tree') (fun t => k + (t.countB : ℝ≥0∞)) := by
  induction n generalizing k with
  | zero =>
    conv_rhs => rw [genDragen]
    walk
    simp [Tree'.countB, dragenB]
  | succ n ih =>
    conv_rhs => rw [genDragen]
    walk [ih]
    simp only [Tree'.countB, dragenB, List.map, List.sum_cons, List.sum_nil, Nat.cast_ofNat,
      add_zero, Nat.cast_zero, ENNReal.coe_div (by norm_num : (10 : ℝ≥0) ≠ 0)]
    push_cast
    rw [ENNReal.le_div_iff_mul_le (by norm_num) (by norm_num), add_mul,
      ENNReal.div_mul_cancel (by norm_num) (by norm_num)]
    apply le_of_eq
    ring

/-- The expected number of `nodeA`s is exactly `dragenA n`. -/
theorem genDragen.expect_countA (n : Nat) :
    SPMF.expect (genDragen n) (fun t => (t.countA : ℝ≥0∞)) = (dragenA n : ℝ≥0∞) := by
  refine le_antisymm (genDragen.expect_countA_le n) ?_
  simpa [SPMF.expect_eq_obs] using genDragen.le_expect_countA n 0

/-- The expected number of `nodeB`s is exactly `dragenB n`. -/
theorem genDragen.expect_countB (n : Nat) :
    SPMF.expect (genDragen n) (fun t => (t.countB : ℝ≥0∞)) = (dragenB n : ℝ≥0∞) := by
  refine le_antisymm (genDragen.expect_countB_le n) ?_
  simpa [SPMF.expect_eq_obs] using genDragen.le_expect_countB n 0

/-- §4 reports 21.322 `NodeA`s at size `10`; the expectation is `21.3097486415`. -/
theorem dragenA_ten : dragenA 10 = 42619497283 / 2000000000 := by
  norm_num [dragenA]

/-- §4 reports 12.813 `NodeB`s at size `10`; the expectation is `12.7858491849`. -/
theorem dragenB_ten : dragenB 10 = 127858491849 / 10000000000 := by
  norm_num [dragenB]


/-! ## Mutually recursive types (§6) -/

mutual
/-- The first of the mutually recursive types of Figure 8. -/
inductive T1 : Type where
  | a : T1
  | b : T1 → T2 → T1
/-- The second of the mutually recursive types of Figure 8. -/
inductive T2 : Type where
  | c : T2
  | d : T1 → T2
end

/-- The constructors of `T1` and `T2`, as kinds of offspring. -/
inductive Ctor : Type where
  | A | B | C | D
  deriving DecidableEq

mutual
/-- The number of `c` constructors in a `T1`. -/
def T1.count (c : Ctor) : T1 → Nat
  | .a => if c = .A then 1 else 0
  | .b t u => (if c = .B then 1 else 0) + t.count c + u.count c
/-- The number of `c` constructors in a `T2`. -/
def T2.count (c : Ctor) : T2 → Nat
  | .c => if c = .C then 1 else 0
  | .d t => (if c = .D then 1 else 0) + t.count c
end

mutual
/-- The generator for `T1` of Figure 8, at `pA = pB = 1/2`. -/
def genT1 [Gen G] (n : Nat) : G T1 :=
  match n with
  | 0 => pure .a
  | n + 1 => oneOf! [
      fun _ => pure .a,
      fun _ => do
        let t ← genT1 n
        let u ← genT2 n
        return .b t u]
partial_fixpoint
/-- The generator for `T2` of Figure 8, at `pC = 1/3`, `pD = 2/3`. -/
def genT2 [Gen G] (n : Nat) : G T2 :=
  match n with
  | 0 => pure .c
  | n + 1 => frequency! [
      (1, fun _ => pure .c),
      (2, fun _ => do
        let t ← genT1 n
        return .d t)] (by simp)
partial_fixpoint
end

/-- The type a constructor builds, `0` for `T1` and `1` for `T2`. -/
def Ctor.ty : Ctor → Fin 2
  | .A | .B => 0
  | .C | .D => 1

/-- Whether a constructor has no recursive argument. -/
def Ctor.terminal : Ctor → Bool
  | .A | .C => true
  | .B | .D => false

/-- The probability the generators give each constructor. -/
noncomputable def Ctor.prob : Ctor → ℝ≥0∞
  | .A => 1 / 2
  | .B => 1 / 2
  | .C => 1 / 3
  | .D => 2 / 3

/-- The branching factor `β(T_v, C)`: the number of arguments of `C` of type `v`. -/
def β (v : Fin 2) : Ctor → Nat
  | .B => 1
  | .D => if v = 0 then 1 else 0
  | _ => 0

/-- The mean matrix of types, by Prop. A.2: `m_{T_u T_v} = Σ_{C ∈ cons(T_u)} β(T_v, C) · p_C`. -/
noncomputable def meanTypes : Matrix (Fin 2) (Fin 2) ℝ≥0∞ :=
  fun u v => ([Ctor.A, .B, .C, .D].map fun c => if c.ty = u then (β v c : ℝ≥0∞) * c.prob else 0).sum

/-- The expected number of type placeholders at each level, starting from one of type `r`:
`E[G^T_k] = E[G^T_0] · M_T^k` (equation 7). -/
noncomputable def level (r : Fin 2) (k : Nat) : Fin 2 → ℝ≥0∞ :=
  Matrix.vecMul (Pi.single r 1) (meanTypes ^ k)

/-- The paper's prediction for the expected number of `c`s at size `n` from a root of type `r`: the
placeholders of `c`'s type on the first `n` levels, times `p_c` (Theorem 1), and for a terminal,
every placeholder of its type on the last level (§5). -/
noncomputable def predicted (r : Fin 2) (c : Ctor) (n : Nat) : ℝ≥0∞ :=
  c.prob * ∑ k ∈ Finset.range n, level r k c.ty + if c.terminal then level r n c.ty else 0

/-- The matrix §6 gives for `T1` and `T2`: `[[p_B, p_B], [p_D, 0]]`. -/
theorem meanTypes_eq : meanTypes = !![1 / 2, 1 / 2; 2 / 3, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [meanTypes, β, Ctor.ty, Ctor.prob]

theorem level_zero (r : Fin 2) : level r 0 = Pi.single r 1 := by
  simp [level]

theorem level_apply (r : Fin 2) (k : Nat) (t : Fin 2) : level r k t = (meanTypes ^ k) r t := by
  simp [level]

theorem level_succ (r : Fin 2) (k : Nat) (t : Fin 2) :
    level r (k + 1) t = ∑ v, meanTypes r v * level v k t := by
  simp only [level_apply, pow_succ', Matrix.mul_apply]

theorem predicted_succ (r : Fin 2) (c : Ctor) (n : Nat) :
    predicted r c (n + 1) =
      c.prob * (if c.ty = r then 1 else 0) + ∑ v, meanTypes r v * predicted v c n := by
  simp only [predicted, Finset.sum_range_succ', level_succ, level_zero, Fin.sum_univ_two,
    Finset.sum_add_distrib, ← Finset.mul_sum, Pi.single_apply]
  split_ifs <;> ring

/-- The upper half of `genT12.expect_count`: each constructor's expected count is at most the
paper's prediction from the mean matrix of types. -/
theorem genT12.expect_count_le (n : Nat) :
    (∀ c, SPMF.expect (genT1 n) (fun t => (t.count c : ℝ≥0∞)) ≤ predicted 0 c n) ∧
    (∀ c, SPMF.expect (genT2 n) (fun t => (t.count c : ℝ≥0∞)) ≤ predicted 1 c n) := by
  induction n with
  | zero =>
    refine ⟨fun c => ?_, fun c => ?_⟩ <;> rw [SPMF.expect_eq_obs]
    · conv_lhs => rw [genT1]
      walk
      cases c <;> simp [T1.count, predicted, level_zero, Ctor.terminal, Ctor.ty]
    · conv_lhs => rw [genT2]
      walk
      cases c <;> simp [T2.count, predicted, level_zero, Ctor.terminal, Ctor.ty]
  | succ n ih =>
    refine ⟨fun c => ?_, fun c => ?_⟩ <;> rw [SPMF.expect_eq_obs]
    · have h1 := ih.1 c
      have h2 := ih.2 c
      rw [SPMF.expect_eq_obs] at h1 h2
      conv_lhs => rw [genT1]
      walk [h1, h2]
      rw [predicted_succ]
      cases c <;> simp [T1.count, meanTypes, β, Ctor.ty, Ctor.prob, Fin.sum_univ_two]
      all_goals (apply le_of_eq; simp only [div_eq_mul_inv]; ring)
    · have h1 := ih.1 c
      rw [SPMF.expect_eq_obs] at h1
      conv_lhs => rw [genT2]
      walk [h1]
      rw [predicted_succ]
      cases c <;> simp [T2.count, meanTypes, β, Ctor.ty, Ctor.prob]
      all_goals (apply le_of_eq; simp only [div_eq_mul_inv]; ring)

theorem genT12.le_expect_count (n : Nat) :
    (∀ c k, k + predicted 0 c n ≤
      SPMF.expectObs.spec (genT1 n : SPMF T1) (fun t => k + (t.count c : ℝ≥0∞))) ∧
    (∀ c k, k + predicted 1 c n ≤
      SPMF.expectObs.spec (genT2 n : SPMF T2) (fun t => k + (t.count c : ℝ≥0∞))) := by
  induction n with
  | zero =>
    refine ⟨fun c k => ?_, fun c k => ?_⟩
    · conv_rhs => rw [genT1]
      walk
      cases c <;> simp [T1.count, predicted, level_zero, Ctor.terminal, Ctor.ty]
    · conv_rhs => rw [genT2]
      walk
      cases c <;> simp [T2.count, predicted, level_zero, Ctor.terminal, Ctor.ty]
  | succ n ih =>
    refine ⟨fun c k => ?_, fun c k => ?_⟩
    · conv_rhs => rw [genT1]
      walk [ih.1 c, ih.2 c]
      rw [predicted_succ]
      cases c <;> simp [T1.count, meanTypes, β, Ctor.ty, Ctor.prob, Fin.sum_univ_two]
      all_goals
        apply le_of_eq
        conv_lhs => rw [show k = 2⁻¹ * k + 2⁻¹ * k by
          rw [← add_mul, ENNReal.inv_two_add_inv_two, one_mul]]
        simp only [div_eq_mul_inv]
        ring
    · conv_rhs => rw [genT2]
      walk [ih.1 c]
      rw [predicted_succ]
      cases c <;> simp [T2.count, meanTypes, β, Ctor.ty, Ctor.prob]
      all_goals
        apply le_of_eq
        conv_lhs => rw [show k = 3⁻¹ * k + 2 * 3⁻¹ * k by
          rw [← add_mul, ← one_add_mul, show (1 : ℝ≥0∞) + 2 = 3 by norm_num,
            ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]]
        simp only [div_eq_mul_inv]
        ring

/-- **Theorem 1 for Figure 8**, exactly: each constructor's expected count is the paper's
prediction from the mean matrix of types. -/
theorem genT12.expect_count (n : Nat) :
    (∀ c, SPMF.expect (genT1 n) (fun t => (t.count c : ℝ≥0∞)) = predicted 0 c n) ∧
    (∀ c, SPMF.expect (genT2 n) (fun t => (t.count c : ℝ≥0∞)) = predicted 1 c n) := by
  refine ⟨fun c => le_antisymm ((genT12.expect_count_le n).1 c) ?_,
    fun c => le_antisymm ((genT12.expect_count_le n).2 c) ?_⟩
  · simpa [SPMF.expect_eq_obs] using (genT12.le_expect_count n).1 c 0
  · simpa [SPMF.expect_eq_obs] using (genT12.le_expect_count n).2 c 0

end BranchingProcesses
