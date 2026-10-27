/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Ernest Ng
-/
module

public import Basalt

/-!
# Branching Processes for QuickCheck Generators

The generators of Mista, Russo, and Hughes, "Branching Processes for QuickCheck Generators"
(Haskell '18, arXiv:1808.01520), with their claims about them stated and proved: the termination
probability of a `derive` generator (Appendix B.1), and the expected constructor counts the paper
predicts for MegaDeTH (§3) and Dragen (§4) generators at size `10`.
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

/-- The expected number of `node`s at size `n`, by the generator's own recurrence. -/
noncomputable def megaNodes : Nat → ℝ≥0∞
  | 0 => 0
  | n + 1 => (1 + 2 * megaNodes ((n + 1) / 2)) / 4

theorem genMegaDeTH.expect_nodes_le (n : Nat) :
    SPMF.expect (genMegaDeTH n) (fun t => (t.nodes : ℝ≥0∞)) ≤ megaNodes n := by
  rw [SPMF.expect_eq_obs]
  walk fixpoint
  all_goals simp [Tree.nodes, megaNodes, two_mul, add_assoc]

/-- §3 predicts "an expected number of `Node` constructors up to level 10 of 0.4997" for this
generator at size `10`; it has at most `15/32 = 0.46875`, since halving the size leaves four levels
of `node`s, where the prediction counts eleven. -/
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

/-- The expected number of `nodeA`s at size `n`, by the generator's own recurrence. -/
noncomputable def dragenA : Nat → ℝ≥0
  | 0 => 0
  | n + 1 => (5 + 13 * dragenA n) / 10

/-- The expected number of `nodeB`s at size `n`, by the generator's own recurrence. -/
noncomputable def dragenB : Nat → ℝ≥0
  | 0 => 0
  | n + 1 => (3 + 13 * dragenB n) / 10

theorem genDragen.expect_countA_le (n : Nat) :
    SPMF.expect (genDragen n) (fun t => (t.countA : ℝ≥0∞)) ≤ (dragenA n : ℝ≥0∞) := by
  rw [SPMF.expect_eq_obs]
  walk fixpoint
  all_goals simp [Tree'.countA, dragenA, ENNReal.coe_div]
  all_goals (apply le_of_eq; ring_nf)

theorem genDragen.expect_countB_le (n : Nat) :
    SPMF.expect (genDragen n) (fun t => (t.countB : ℝ≥0∞)) ≤ (dragenB n : ℝ≥0∞) := by
  rw [SPMF.expect_eq_obs]
  walk fixpoint
  all_goals simp [Tree'.countB, dragenB, ENNReal.coe_div]
  all_goals (apply le_of_eq; ring_nf)

/-- §4: "our QuickCheck generator with a size parameter of 10 will generate on average 21.322
`NodeA`s" — it generates fewer. -/
theorem dragenA_ten : dragenA 10 < 21322 / 1000 := by
  norm_num [dragenA]

/-- §4: "… and 12.813 `NodeB`s" — it generates fewer. -/
theorem dragenB_ten : dragenB 10 < 12813 / 1000 := by
  norm_num [dragenB]

end BranchingProcesses
