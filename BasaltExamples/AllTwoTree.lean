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
    (fun c hle hge => ?_) ?_
  · rw [← ENNReal.toReal_eq_one_iff]
    ennreal_to_real at hge   -- before `hle`: finiteness needs `c ≤ 1`
    ennreal_to_real at hle
    norm_num at hge hle
    nlinarith [sq_nonneg (c.toReal - 1)]
  · conv_rhs => rw [genTree]
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
    rw [IsBounded_iff]
    rintro ⟨t, n⟩ hmem
    cost_support_simp at hmem
    obtain ⟨m, rfl, h | h⟩ := hmem
    · obtain ⟨rfl, rfl⟩ := h
      simp [Tree.cost, Tree.size]
    · obtain ⟨l, n1, n2, hl, ⟨r, n3, n4, hr, ⟨rfl, hn4⟩, hn2⟩, hm⟩ := h
      have hL : n1 ≤ Tree.cost l := ih (l, n1) hl
      have hR : n3 ≤ Tree.cost r := ih (r, n3) hr
      show 1 + m ≤ Tree.cost (Tree.node l 2 r)
      simp only [Tree.cost, Tree.size] at *
      omega

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
          ENNReal.one_sub_le_mul_one_sub (by ennreal_to_real; norm_num)
            (by finiteness) hmass.ge
      _ ≤ 1 / 3 * ((1 - (genWeightedTree : SPMF Tree).mass)
            + (1 - (genWeightedTree : SPMF Tree).mass)) := by
          gcongr
          exact ENNReal.one_sub_mul_le_add (SPMF.mass_le_one _) (SPMF.mass_le_one _)
      _ = 2 / 3 * (1 - (genWeightedTree : SPMF Tree).mass) := by
          rw [← two_mul, ← mul_assoc,
            show (1 / 3 : ℝ≥0∞) * 2 = 2 / 3 by ennreal_to_real; norm_num]

theorem genWeightedTree_expectedSteps :
    SPMF.LevelOp.expectedSteps (fun e (j : Unit) => 2 / 3 * e j) () = 3 := by
  rw [SPMF.LevelOp.expectedSteps_const_mul,
    show (1 : ℝ≥0∞) - 2 / 3 = 1 / 3 from by ennreal_to_real; norm_num, one_div, inv_inv]

theorem genTree_expectedSteps_infinite :
    SPMF.LevelOp.expectedSteps (fun e (j : Unit) => 1 * e j) () = ⊤ := by
  rw [SPMF.LevelOp.expectedSteps_const_mul]
  simp

end weighted

end AllTwoTree
