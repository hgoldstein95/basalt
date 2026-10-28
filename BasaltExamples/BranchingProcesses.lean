/-
Copyright (c) 2026 Harrison Goldstein & Ernest Ng. All rights reserved.
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
for a few particular generators (sections 3 & 4 from the paper), as Theorem 1's prediction from the
mean matrix of types (`Basalt/SPMF/BranchingProcess.lean`) for Dragen's generator and for the
mutually recursive types of section 6.
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
differ only in their label, so the `k` are one branch of weight `k` that builds `.b`. At `k = 2` it
has `genT`'s termination probability, though not its distribution, since it never builds `.c`. -/
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

/-! ## Dragen's generator (§4, §5)

A single type with two recursive constructors is the one-type case of `BranchingProcess.Spec`, so
every constructor's expected count, the leaves' included, is the prediction of Theorem 1 and §5. -/

/-- The data type of §3–4, with two recursive constructors. -/
inductive Tree' : Type where
  | leaf
  | nodeA : Tree' → Tree' → Tree'
  | nodeB : Tree' → Tree'

/-- The constructors of `Tree'`. -/
inductive Con' : Type where
  | leaf | nodeA | nodeB
  deriving DecidableEq

instance : Fintype Con' := ⟨{.leaf, .nodeA, .nodeB}, fun c => by cases c <;> simp⟩

/-- The number of `c` constructors in a `Tree'`. -/
def Tree'.count (c : Con') : Tree' → Nat
  | .leaf => if c = .leaf then 1 else 0
  | .nodeA l r => (if c = .nodeA then 1 else 0) + l.count c + r.count c
  | .nodeB t => (if c = .nodeB then 1 else 0) + t.count c

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

/-- The probability `genDragen` gives each constructor. -/
noncomputable def Con'.prob : Con' → ℝ≥0∞
  | .leaf => 2 / 10
  | .nodeA => 5 / 10
  | .nodeB => 3 / 10

/-- The number of `Tree'` arguments of each constructor. -/
def Con'.args : Con' → Nat
  | .leaf => 0
  | .nodeA => 2
  | .nodeB => 1

/-- `genDragen` as a branching process. -/
noncomputable def dragenSpec : BranchingProcess.Spec Unit Con' := ⟨fun _ => (), Con'.prob, fun _ => Con'.args⟩

@[simp] theorem dragenSpec_prob (c : Con') : dragenSpec.prob c = c.prob := rfl
@[simp] theorem dragenSpec_args (v : Unit) (c : Con') : dragenSpec.args v c = c.args := rfl
@[simp] theorem dragenSpec_ty (c : Con') : dragenSpec.ty c = () := rfl

/-- The mean number of offspring, `2 · pNodeA + pNodeB`. -/
theorem dragenSpec_meanTypes (u v : Unit) : dragenSpec.meanTypes u v = 13 / 10 := by
  simp [BranchingProcess.Spec.meanTypes, Finset.univ, Fintype.elems, Con'.prob, Con'.args,
    ← mul_div_assoc, ENNReal.div_add_div_same]
  norm_num

theorem genDragen.expect_count_le (c : Con') (n : Nat) :
    SPMF.expect (genDragen n) (fun t => (t.count c : ℝ≥0∞)) ≤ dragenSpec.predicted () c n := by
  rw [SPMF.expect_eq_obs]
  walk fixpoint
  · rw [dragenSpec.predicted_zero]
    cases c <;> simp [Tree'.count, BranchingProcess.Spec.terminal, Con'.args]
  · rw [Nat.succ_eq_add_one, dragenSpec.predicted_succ]
    simp only [Fintype.sum_unique, dragenSpec_meanTypes]
    cases c <;> simp [Tree'.count, Con'.prob]
    all_goals (apply le_of_eq; simp only [div_eq_mul_inv]; ring)

theorem genDragen.le_expect_count (c : Con') (n : Nat) (k : ℝ≥0∞) :
    k + dragenSpec.predicted () c n ≤
      SPMF.expectObs.spec (genDragen n : SPMF Tree') (fun t => k + (t.count c : ℝ≥0∞)) := by
  induction n generalizing k with
  | zero =>
    conv_rhs => rw [genDragen]
    walk
    rw [dragenSpec.predicted_zero]
    cases c <;> simp [Tree'.count, BranchingProcess.Spec.terminal, Con'.args]
  | succ n ih =>
    conv_rhs => rw [genDragen]
    walk [ih]
    rw [dragenSpec.predicted_succ]
    simp only [Fintype.sum_unique, dragenSpec_meanTypes]
    conv_lhs => rw [show k = k * 10 * 10⁻¹ from
      (ENNReal.mul_inv_cancel_right (by norm_num) (by norm_num)).symm]
    cases c <;> simp [Tree'.count, Con'.prob]
    all_goals (apply le_of_eq; simp only [div_eq_mul_inv]; ring)

/-- **§4–5**: every constructor's expected count is the branching process's prediction. -/
theorem genDragen.expect_count (c : Con') (n : Nat) :
    SPMF.expect (genDragen n) (fun t => (t.count c : ℝ≥0∞)) = dragenSpec.predicted () c n := by
  refine le_antisymm (genDragen.expect_count_le c n) ?_
  simpa [SPMF.expect_eq_obs] using genDragen.le_expect_count c n 0

theorem dragenSpec_level (k : Nat) : dragenSpec.level () k () = (13 / 10) ^ k := by
  induction k with
  | zero => simp [dragenSpec.level_zero]
  | succ k ih => rw [dragenSpec.level_succ, Fintype.sum_unique, dragenSpec_meanTypes]; simp [ih, pow_succ, mul_comm]

/-- §4 reports 21.322 `NodeA`s at size `10`; the expectation is `21.3097486415`. -/
theorem dragen_nodeA_ten : dragenSpec.predicted () .nodeA 10 = 42619497283 / 2000000000 := by
  simp [BranchingProcess.Spec.predicted, BranchingProcess.Spec.terminal, Con'.args, Con'.prob,
    dragenSpec_level, Finset.sum_range_succ]
  basify
  norm_num

/-- §4 reports 12.813 `NodeB`s at size `10`; the expectation is `12.7858491849`. -/
theorem dragen_nodeB_ten : dragenSpec.predicted () .nodeB 10 = 127858491849 / 10000000000 := by
  simp [BranchingProcess.Spec.predicted, BranchingProcess.Spec.terminal, Con'.args, Con'.prob,
    dragenSpec_level, Finset.sum_range_succ]
  basify
  norm_num

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

instance : Fintype Ctor := ⟨{.A, .B, .C, .D}, fun c => by cases c <;> simp⟩

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

/-- The probability the generators give each constructor. -/
noncomputable def Ctor.prob : Ctor → ℝ≥0∞
  | .A => 1 / 2
  | .B => 1 / 2
  | .C => 1 / 3
  | .D => 2 / 3

/-- The branching factor `β(T_v, C)`: the number of arguments of `C` of type `v`. -/
def Ctor.args (v : Fin 2) : Ctor → Nat
  | .B => 1
  | .D => if v = 0 then 1 else 0
  | _ => 0

/-- `genT1` and `genT2` as a branching process. -/
noncomputable def fig8Spec : BranchingProcess.Spec (Fin 2) Ctor := ⟨Ctor.ty, Ctor.prob, Ctor.args⟩

@[simp] theorem fig8Spec_ty (c : Ctor) : fig8Spec.ty c = c.ty := rfl
@[simp] theorem fig8Spec_prob (c : Ctor) : fig8Spec.prob c = c.prob := rfl
@[simp] theorem fig8Spec_args (v : Fin 2) (c : Ctor) : fig8Spec.args v c = c.args v := rfl

/-- The matrix §6 gives for `T1` and `T2`: `[[p_B, p_B], [p_D, 0]]`. -/
theorem fig8Spec_meanTypes : fig8Spec.meanTypes = !![1 / 2, 1 / 2; 2 / 3, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [BranchingProcess.Spec.meanTypes, Finset.univ, Fintype.elems, Ctor.ty, Ctor.prob, Ctor.args]

/-- Each constructor's expected count is at most its prediction. -/
theorem genT12.expect_count_le (n : Nat) :
    (∀ c, SPMF.expect (genT1 n) (fun t => (t.count c : ℝ≥0∞)) ≤ fig8Spec.predicted 0 c n) ∧
    (∀ c, SPMF.expect (genT2 n) (fun t => (t.count c : ℝ≥0∞)) ≤ fig8Spec.predicted 1 c n) := by
  induction n with
  | zero =>
    refine ⟨fun c => ?_, fun c => ?_⟩ <;> rw [SPMF.expect_eq_obs, fig8Spec.predicted_zero]
    · conv_lhs => rw [genT1]
      walk
      cases c <;> simp [T1.count, BranchingProcess.Spec.terminal, Ctor.ty, Ctor.args]
    · conv_lhs => rw [genT2]
      walk
      cases c <;> simp [T2.count, BranchingProcess.Spec.terminal, Ctor.ty, Ctor.args]
  | succ n ih =>
    refine ⟨fun c => ?_, fun c => ?_⟩ <;>
      rw [SPMF.expect_eq_obs, fig8Spec.predicted_succ, fig8Spec_meanTypes]
    · have h1 := ih.1 c
      have h2 := ih.2 c
      rw [SPMF.expect_eq_obs] at h1 h2
      conv_lhs => rw [genT1]
      walk [h1, h2]
      cases c <;> simp [T1.count, Ctor.ty, Ctor.prob, Fin.sum_univ_two]
      all_goals (apply le_of_eq; simp only [div_eq_mul_inv]; ring)
    · have h1 := ih.1 c
      rw [SPMF.expect_eq_obs] at h1
      conv_lhs => rw [genT2]
      walk [h1]
      cases c <;> simp [T2.count, Ctor.ty, Ctor.prob, Fin.sum_univ_two]
      all_goals (apply le_of_eq; simp only [div_eq_mul_inv]; ring)

theorem genT12.le_expect_count (n : Nat) :
    (∀ c k, k + fig8Spec.predicted 0 c n ≤
      SPMF.expectObs.spec (genT1 n : SPMF T1) (fun t => k + (t.count c : ℝ≥0∞))) ∧
    (∀ c k, k + fig8Spec.predicted 1 c n ≤
      SPMF.expectObs.spec (genT2 n : SPMF T2) (fun t => k + (t.count c : ℝ≥0∞))) := by
  induction n with
  | zero =>
    refine ⟨fun c k => ?_, fun c k => ?_⟩ <;> rw [fig8Spec.predicted_zero]
    · conv_rhs => rw [genT1]
      walk
      cases c <;> simp [T1.count, BranchingProcess.Spec.terminal, Ctor.ty, Ctor.args]
    · conv_rhs => rw [genT2]
      walk
      cases c <;> simp [T2.count, BranchingProcess.Spec.terminal, Ctor.ty, Ctor.args]
  | succ n ih =>
    refine ⟨fun c k => ?_, fun c k => ?_⟩ <;> rw [fig8Spec.predicted_succ, fig8Spec_meanTypes]
    · conv_rhs => rw [genT1]
      walk [ih.1 c, ih.2 c]
      conv_lhs => rw [show k = k * 2 * 2⁻¹ from
        (ENNReal.mul_inv_cancel_right (by norm_num) (by norm_num)).symm]
      cases c <;> simp [T1.count, Ctor.ty, Ctor.prob, Fin.sum_univ_two]
      all_goals (apply le_of_eq; simp only [div_eq_mul_inv]; ring)
    · conv_rhs => rw [genT2]
      walk [ih.1 c]
      conv_lhs => rw [show k = k * 3 * 3⁻¹ from
        (ENNReal.mul_inv_cancel_right (by norm_num) (by norm_num)).symm]
      cases c <;> simp [T2.count, Ctor.ty, Ctor.prob, Fin.sum_univ_two]
      all_goals (apply le_of_eq; simp only [div_eq_mul_inv]; ring)

/-- **Theorem 1 for Figure 8**: each constructor's expected count is the prediction from the mean
matrix of types. -/
theorem genT12.expect_count (n : Nat) :
    (∀ c, SPMF.expect (genT1 n) (fun t => (t.count c : ℝ≥0∞)) = fig8Spec.predicted 0 c n) ∧
    (∀ c, SPMF.expect (genT2 n) (fun t => (t.count c : ℝ≥0∞)) = fig8Spec.predicted 1 c n) := by
  refine ⟨fun c => le_antisymm ((genT12.expect_count_le n).1 c) ?_,
    fun c => le_antisymm ((genT12.expect_count_le n).2 c) ?_⟩
  · simpa [SPMF.expect_eq_obs] using (genT12.le_expect_count n).1 c 0
  · simpa [SPMF.expect_eq_obs] using (genT12.le_expect_count n).2 c 0

end BranchingProcesses
