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

/-- Binary trees with three different kinds of leaves -/
inductive Tree : Type where
  | leafA | leafB | leafC
  | node : Tree → Tree → Tree

/-- No. of nodes in a tree -/
def Tree.nodes : Tree → Nat
  | .node l r => l.nodes + r.nodes + 1
  | _ => 0

/-- A generator for `Tree`s taken from Figure 2 of the Branching Processes paper, where
    the size at each `node` is halved -/
def genTree [Gen G] (n : Nat) : G Tree :=
  match n with
  | 0 => oneOf! [fun _ => pure .leafA, fun _ => pure .leafB, fun _ => pure .leafC]
  | n + 1 => oneOf! [
      fun _ => pure .leafA, fun _ => pure .leafB, fun _ => pure .leafC,
      fun _ => do
        let l ← genTree ((n + 1) / 2)
        let r ← genTree ((n + 1) / 2)
        return .node l r]
partial_fixpoint

/-- The expected number of `node`s at size `n` -/
noncomputable def expectedNodesAtSize : Nat → ℝ≥0∞
  | 0 => 0
  | n + 1 => (1 + 2 * expectedNodesAtSize ((n + 1) / 2)) / 4

theorem genTree.mass (n : Nat) : (genTree n : SPMF Tree).mass = 1 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero =>
      rw [← SPMF.expect_one, genTree, oneOfWith_eq, SPMF.expect_oneOf]
      norm_num [ENNReal.div_self]
    | succ n =>
      rw [← SPMF.expect_one, genTree, oneOfWith_eq, SPMF.expect_oneOf]
      simp only [List.map, SPMF.expect_bind, SPMF.expect_pure]
      simp only [SPMF.expect_one, ih ((n + 1) / 2) (by omega)]
      norm_num [ENNReal.div_self]

/-- The expected number of `node`s is exactly `expectedNodesAtSize n`. -/
theorem genTree.expect_nodes (n : Nat) :
    SPMF.expect (genTree n) (fun t => (t.nodes : ℝ≥0∞)) = expectedNodesAtSize n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero =>
      rw [genTree, oneOfWith_eq, SPMF.expect_oneOf]
      simp [Tree.nodes, expectedNodesAtSize]
    | succ n =>
      rw [genTree, oneOfWith_eq, SPMF.expect_oneOf, expectedNodesAtSize]
      simp only [List.map, SPMF.expect_bind, SPMF.expect_pure, Tree.nodes, Nat.cast_add,
        Nat.cast_one, Nat.cast_zero, SPMF.expect_add, SPMF.expect_const, ih ((n + 1) / 2) (by omega),
        genTree.mass, one_mul]
      congr 1
      norm_num
      ring


/-! ## Dragen's generator (§4, §5)

A single type with two recursive constructors is the one-type case of `BranchingProcess.Spec`, so
every constructor's expected count, the leaves' included, is the prediction of Theorem 1 and §5. -/

/-- The tree data type of §3–4, with two recursive constructors (two different kinds of nodes). -/
inductive Tree' : Type where
  | leaf
  | nodeA : Tree' → Tree' → Tree'
  | nodeB : Tree' → Tree'

/-- The constructors of `Tree'`. -/
inductive Ctor : Type where
  | leaf | nodeA | nodeB
  deriving DecidableEq

instance : Fintype Ctor := ⟨{.leaf, .nodeA, .nodeB}, fun c => by cases c <;> simp⟩

/-- The number of `c` constructors in a `Tree'`. -/
def Tree'.count (c : Ctor) : Tree' → Nat
  | .leaf => if c = .leaf then 1 else 0
  | .nodeA l r => (if c = .nodeA then 1 else 0) + l.count c + r.count c
  | .nodeB t => (if c = .nodeB then 1 else 0) + t.count c

/-- Dragen's generator for `Tree'` (Figure 5), at the probabilities of §4: `pLeaf = 0.2`,
`pNodeA = 0.5`, `pNodeB = 0.3`. -/
def genTree2 [Gen G] (n : Nat) : G Tree' :=
  match n with
  | 0 => pure .leaf
  | n + 1 => frequency! [
      (2, fun _ => pure .leaf),
      (5, fun _ => do
        let l ← genTree2 n
        let r ← genTree2 n
        return .nodeA l r),
      (3, fun _ => do
        let t ← genTree2 n
        return .nodeB t)] (by simp)
partial_fixpoint

/-- The probability `genTree2` gives each constructor. -/
noncomputable def Ctor.prob : Ctor → ℝ≥0∞
  | .leaf => 2 / 10
  | .nodeA => 5 / 10
  | .nodeB => 3 / 10

/-- The number of `Tree'` arguments of each constructor. -/
def Ctor.args : Ctor → Nat
  | .leaf => 0
  | .nodeA => 2
  | .nodeB => 1

/-- `genTree2` as a branching process. -/
noncomputable def genTree2Spec : BranchingProcess.Spec Unit Ctor :=
  ⟨fun _ => (), Ctor.prob, fun _ => Ctor.args⟩

@[simp] theorem genTree2Spec_prob (c : Ctor) : genTree2Spec.prob c = c.prob := rfl
@[simp] theorem genTree2Spec_args (v : Unit) (c : Ctor) : genTree2Spec.args v c = c.args := rfl
@[simp] theorem genTree2Spec_ty (c : Ctor) : genTree2Spec.ty c = () := rfl

/-- The mean number of offspring, `2 · pNodeA + pNodeB`. -/
theorem genTree2Spec_meanTypes (u v : Unit) : genTree2Spec.meanTypes u v = 13 / 10 := by
  simp [BranchingProcess.Spec.meanTypes, Finset.univ, Fintype.elems, Ctor.prob, Ctor.args,
    ← mul_div_assoc, ENNReal.div_add_div_same]
  norm_num

theorem genTree2.mass (n : Nat) : (genTree2 n : SPMF Tree').mass = 1 := by
  induction n with
  | zero => rw [genTree2]; simp
  | succ n ih =>
    rw [← SPMF.expect_one, genTree2, frequencyWith_eq, SPMF.expect_frequency]
    simp only [List.map, SPMF.expect_bind, SPMF.expect_pure]
    simp only [SPMF.expect_one, ih]
    norm_num [ENNReal.div_self]

/-- **§4–5**: every constructor's expected count is the branching process's prediction. -/
theorem genTree2.expect_count (c : Ctor) (n : Nat) :
    SPMF.expect (genTree2 n) (fun t => (t.count c : ℝ≥0∞)) = genTree2Spec.predicted () c n := by
  induction n with
  | zero =>
    rw [genTree2, genTree2Spec.predicted_zero]
    cases c <;> simp [Tree'.count, BranchingProcess.Spec.terminal, Ctor.args]
  | succ n ih =>
    rw [genTree2, genTree2Spec.predicted_succ, frequencyWith_eq, SPMF.expect_frequency]
    simp only [List.map, SPMF.expect_bind, SPMF.expect_pure, Tree'.count, Nat.cast_add,
      SPMF.expect_add, SPMF.expect_const, one_mul, ih, genTree2.mass, Fintype.sum_unique,
      genTree2Spec_meanTypes]
    cases c <;> simp [Ctor.prob]
    all_goals (simp only [div_eq_mul_inv]; ring)

theorem genTree2Spec_level (k : Nat) : genTree2Spec.level () k () = (13 / 10) ^ k := by
  induction k with
  | zero => simp [genTree2Spec.level_zero]
  | succ k ih =>
    rw [genTree2Spec.level_succ, Fintype.sum_unique, genTree2Spec_meanTypes]
    simp [ih, pow_succ, mul_comm]

/-- The paper's closed form for `NodeA` (equation 9): `pNodeA · Σ_{k<n} m^k`, with mean offspring
`m = 13/10`. -/
theorem genTree2.expect_nodeA (n : Nat) :
    SPMF.expect (genTree2 n) (fun t => (t.count .nodeA : ℝ≥0∞)) =
      5 / 10 * ∑ k ∈ Finset.range n, (13 / 10) ^ k := by
  rw [genTree2.expect_count]
  simp [BranchingProcess.Spec.predicted, BranchingProcess.Spec.terminal, Ctor.args, Ctor.prob,
    genTree2Spec_level]

/-- The paper's closed form for `NodeB`: `pNodeB · Σ_{k<n} m^k`. -/
theorem genTree2.expect_nodeB (n : Nat) :
    SPMF.expect (genTree2 n) (fun t => (t.count .nodeB : ℝ≥0∞)) =
      3 / 10 * ∑ k ∈ Finset.range n, (13 / 10) ^ k := by
  rw [genTree2.expect_count]
  simp [BranchingProcess.Spec.predicted, BranchingProcess.Spec.terminal, Ctor.args, Ctor.prob,
    genTree2Spec_level]

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
inductive MutualCtor : Type where
  | A | B | C | D
  deriving DecidableEq

instance : Fintype MutualCtor := ⟨{.A, .B, .C, .D}, fun c => by cases c <;> simp⟩

mutual
/-- The number of `c` constructors in a `T1`. -/
def T1.count (c : MutualCtor) : T1 → Nat
  | .a => if c = .A then 1 else 0
  | .b t u => (if c = .B then 1 else 0) + t.count c + u.count c
/-- The number of `c` constructors in a `T2`. -/
def T2.count (c : MutualCtor) : T2 → Nat
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
def MutualCtor.ty : MutualCtor → Fin 2
  | .A | .B => 0
  | .C | .D => 1

/-- The probability the generators give each constructor. -/
noncomputable def MutualCtor.prob : MutualCtor → ℝ≥0∞
  | .A => 1 / 2
  | .B => 1 / 2
  | .C => 1 / 3
  | .D => 2 / 3

/-- The branching factor `β(T_v, C)`: the number of arguments of `C` of type `v`. -/
def MutualCtor.args (v : Fin 2) : MutualCtor → Nat
  | .B => 1
  | .D => if v = 0 then 1 else 0
  | _ => 0

/-- `genT1` and `genT2` as a branching process. -/
noncomputable def mutualSpec : BranchingProcess.Spec (Fin 2) MutualCtor :=
  ⟨MutualCtor.ty, MutualCtor.prob, MutualCtor.args⟩

@[simp] theorem mutualSpec_ty (c : MutualCtor) : mutualSpec.ty c = c.ty := rfl
@[simp] theorem mutualSpec_prob (c : MutualCtor) : mutualSpec.prob c = c.prob := rfl
@[simp] theorem mutualSpec_args (v : Fin 2) (c : MutualCtor) : mutualSpec.args v c = c.args v := rfl

/-- The matrix §6 gives for `T1` and `T2`: `[[p_B, p_B], [p_D, 0]]`. -/
theorem mutualSpec_meanTypes : mutualSpec.meanTypes = !![1 / 2, 1 / 2; 2 / 3, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [BranchingProcess.Spec.meanTypes, Finset.univ, Fintype.elems, MutualCtor.ty,
      MutualCtor.prob, MutualCtor.args]

theorem genT12.mass (n : Nat) :
    (genT1 n : SPMF T1).mass = 1 ∧ (genT2 n : SPMF T2).mass = 1 := by
  induction n with
  | zero => constructor <;> simp [genT1, genT2]
  | succ n ih =>
    constructor
    · rw [← SPMF.expect_one, genT1, oneOfWith_eq, SPMF.expect_oneOf]
      simp only [List.map, SPMF.expect_bind, SPMF.expect_pure]
      simp only [SPMF.expect_one, ih.1, ih.2]
      norm_num [ENNReal.div_self]
    · rw [← SPMF.expect_one, genT2, frequencyWith_eq, SPMF.expect_frequency]
      simp only [List.map, SPMF.expect_bind, SPMF.expect_pure]
      simp only [SPMF.expect_one, ih.1]
      norm_num [ENNReal.div_self]

/-- **Theorem 1 for Figure 8**: each constructor's expected count is the prediction from the mean
matrix of types. -/
theorem genT12.expect_count (n : Nat) :
    (∀ c, SPMF.expect (genT1 n) (fun t => (t.count c : ℝ≥0∞)) = mutualSpec.predicted 0 c n) ∧
    (∀ c, SPMF.expect (genT2 n) (fun t => (t.count c : ℝ≥0∞)) = mutualSpec.predicted 1 c n) := by
  induction n with
  | zero =>
    refine ⟨fun c => ?_, fun c => ?_⟩ <;> rw [mutualSpec.predicted_zero]
    · rw [genT1]
      cases c <;> simp [T1.count, BranchingProcess.Spec.terminal, MutualCtor.ty, MutualCtor.args]
    · rw [genT2]
      cases c <;> simp [T2.count, BranchingProcess.Spec.terminal, MutualCtor.ty, MutualCtor.args]
  | succ n ih =>
    refine ⟨fun c => ?_, fun c => ?_⟩ <;> rw [mutualSpec.predicted_succ, mutualSpec_meanTypes]
    · rw [genT1, oneOfWith_eq, SPMF.expect_oneOf]
      simp only [List.map, SPMF.expect_bind, SPMF.expect_pure, T1.count, Nat.cast_add,
        SPMF.expect_add, SPMF.expect_const, ih.1 c, ih.2 c, (genT12.mass n).1, (genT12.mass n).2,
        one_mul]
      cases c <;> simp [MutualCtor.ty, MutualCtor.prob, Fin.sum_univ_two]
      all_goals (simp only [div_eq_mul_inv]; ring)
    · rw [genT2, frequencyWith_eq, SPMF.expect_frequency]
      simp only [List.map, SPMF.expect_bind, SPMF.expect_pure, T2.count, Nat.cast_add,
        SPMF.expect_add, SPMF.expect_const, ih.1 c, (genT12.mass n).1, one_mul]
      cases c <;> simp [MutualCtor.ty, MutualCtor.prob, Fin.sum_univ_two]
      all_goals (simp only [div_eq_mul_inv]; ring)

end BranchingProcesses
