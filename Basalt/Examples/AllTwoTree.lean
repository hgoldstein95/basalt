import Basalt

open RandomChoice

namespace AllTwoTree

inductive Tree : Type where
  | leaf : Tree
  | node : Tree → Nat → Tree → Tree

def Tree.size : Tree → Nat
  | .leaf => 0
  | .node l _ r => l.size + r.size + 1

def Tree.isAllTwos : Tree → Prop
  | .leaf => True
  | .node l v r => v = 2 ∧ Tree.isAllTwos l ∧ Tree.isAllTwos r

def Tree.cost : Tree → Nat := fun t => 3 * t.size + 1

def genTree [Gen G] : G Tree :=
  pick
    (fun () => pure .leaf)
    (fun () => do
      let l ← genTree
      let r ← genTree
      return .node l 2 r)
partial_fixpoint

theorem genTree_support : t ∈ SPMF.support genTree ↔ Tree.isAllTwos t := by
  fun_induction Tree.isAllTwos
    <;> rw [genTree]
    <;> simp
  grind

theorem genTree_terminates : SPMF.IsPMF genTree := by
  refine SPMF.IsPMF_of_critical (F := fun c => 1 / 2 + 1 / 2 * c ^ 2)
    (fun _ hle hge => SPMF.eq_one_of_half_add_half_sq_le hle hge) ?_
  conv_rhs => rw [genTree]
  simp only [SPMF.mass_pick, SPMF.mass_pure, mul_one]
  gcongr
  rw [sq]
  apply SPMF.mass_bind_ge_mul le_rfl
  intro l
  simp only [SPMF.mass_bind_pure]
  exact le_rfl

theorem genTree_cost : IsBounded genTree Tree.cost := by
  open Lean.Order in
  delta genTree
  apply (fix_induct (motive := fun (g : SPMF.Cost Tree) => IsBounded g Tree.cost) _ ?admissible ?step)
  case admissible =>
    exact admissible_IsBounded _
  case step =>
    intro genTree_rec ih
    simp [IsBounded_iff] at *
    intro t n hn
    grind [
      pick,
      Tree.cost,
      Tree.size,
      SPMF.Cost.mem_support_bind_iff,
      SPMF.Cost.mem_support_pure_iff,
      SPMF.Cost.mem_support_choose_iff
    ]

instance : LawfulGenerator genTree Tree.isAllTwos Tree.cost where
  support_iff := genTree_support
  is_pmf      := genTree_terminates
  is_bounded  := genTree_cost

section weighted

open scoped NNReal ENNReal

def genWeightedTree [Gen G] : G Tree :=
  frequency [
    (2, fun _ => pure .leaf),
    (1, fun _ => do
      let l ← genWeightedTree
      let r ← genWeightedTree
      return .node l 2 r)
  ] (by dsimp; omega)
partial_fixpoint

private lemma one_sub_two_thirds : (1 : ℝ≥0∞) - 2 / 3 = 1 / 3 := by
  refine ENNReal.sub_eq_of_eq_add (ENNReal.div_lt_top (by norm_num) (by norm_num)).ne ?_
  rw [ENNReal.div_add_div_same, show (1 : ℝ≥0∞) + 2 = 3 by norm_num]
  exact (ENNReal.div_self (by norm_num) (by norm_num)).symm

theorem genWeightedTree_terminates : SPMF.IsPMF genWeightedTree := by
  refine SPMF.IsPMF_of_subcritical (m := 2 / 3) ?_ ?_
  · rw [ENNReal.div_lt_iff (by norm_num) (by norm_num), one_mul]
    norm_num
  · have hmass : (genWeightedTree : SPMF Tree).mass
        = 2 / 3 + 1 / 3 * ((genWeightedTree : SPMF Tree).mass
            * (genWeightedTree : SPMF Tree).mass) := by
      conv_lhs => rw [genWeightedTree]
      rw [SPMF.mass_frequency]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, SPMF.mass_pure,
        Nat.cast_one, Nat.cast_ofNat, add_zero, mul_one, one_mul]
      rw [SPMF.mass_bind_of_forall_mass_eq fun l => SPMF.mass_bind_pure]
      rw [show ((2 + 1 : ℕ) : ℝ≥0∞) = 3 by norm_num, ENNReal.add_div]
      congr 1
      rw [div_eq_mul_inv, one_div, mul_comm]
    calc 1 - (genWeightedTree : SPMF Tree).mass
        ≤ 1 / 3 * (1 - (genWeightedTree : SPMF Tree).mass
            * (genWeightedTree : SPMF Tree).mass) :=
          ENNReal.one_sub_le_mul_one_sub
            (by rw [ENNReal.div_add_div_same, show (2 : ℝ≥0∞) + 1 = 3 by norm_num]
                exact ENNReal.div_self (by norm_num) (by norm_num))
            (ENNReal.div_lt_top (by norm_num) (by norm_num)).ne hmass.ge
      _ ≤ 1 / 3 * ((1 - (genWeightedTree : SPMF Tree).mass)
            + (1 - (genWeightedTree : SPMF Tree).mass)) := by
          gcongr
          exact ENNReal.one_sub_mul_le_add (SPMF.mass_le_one _) (SPMF.mass_le_one _)
      _ = 2 / 3 * (1 - (genWeightedTree : SPMF Tree).mass) := by
          rw [← two_mul, ← mul_assoc]
          congr 1
          rw [one_div, mul_comm 3⁻¹ 2, ← div_eq_mul_inv]

theorem genWeightedTree_expectedSteps :
    SPMF.LevelOp.expectedSteps (fun e (j : Unit) => 2 / 3 * e j) () = 3 := by
  rw [SPMF.LevelOp.expectedSteps_const_mul, one_sub_two_thirds, one_div, inv_inv]

theorem genTree_expectedSteps_infinite :
    SPMF.LevelOp.expectedSteps (fun e (j : Unit) => 1 * e j) () = ⊤ := by
  rw [SPMF.LevelOp.expectedSteps_const_mul]
  simp

end weighted

end AllTwoTree
