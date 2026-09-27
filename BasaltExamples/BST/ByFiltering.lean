/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt
import BasaltExamples.BST

/-!
# Binary Search Trees by Filtering

`Tree.genBSTByFiltering` draws a tree sized by `n` with keys in `[lo, hi]`, and retries until it
draws a search tree. Its source is only known to accept its leaves, a `1 / (n + 1)` share of its
draws (`Tree.genTree.reject_le`); compare `NonEmptyList.lean`, whose source rarely rejects.
-/

open RandomChoice
open scoped ENNReal

namespace BST

/-- `Tree.isBST`, decided. -/
def Tree.isBSTb (lo hi : Int) : Tree Int → Bool
  | leaf => true
  | node l x r => decide (lo ≤ x ∧ x ≤ hi) && isBSTb lo (x - 1) l && isBSTb (x + 1) hi r

theorem Tree.isBSTb_iff {lo hi : Int} {t : Tree Int} : t.isBSTb lo hi = true ↔ t.isBST lo hi := by
  induction t generalizing lo hi with
  | leaf => simp [isBSTb, isBST]
  | node l x r ihl ihr => simp [isBSTb, isBST, ihl, ihr, and_assoc]

/-- A tree sized by `n`, with keys in `[lo, hi]`: a leaf with weight `1` against a node with weight
`n`, and `n` halved for the subtrees. -/
def Tree.genTree [Gen G] (lo hi : Int) (h : lo ≤ hi) (n : Nat) : G (Tree Int) :=
  if hn : n = 0 then pure leaf
  else
    frequency! [
      (1, fun _ => pure leaf),
      (n, fun _ => do
        let x ← chooseInt lo hi h
        let l ← Tree.genTree lo hi h (n / 2)
        let r ← Tree.genTree lo hi h (n / 2)
        return node l x r)
    ] (by simp)
termination_by n
decreasing_by all_goals omega

/-- Draws from `Tree.genTree` until the tree drawn is a search tree. -/
def Tree.genBSTByFiltering [Gen G] (lo hi : Int) (h : lo ≤ hi := by gen_side_condition)
    (n : Nat) : G (Tree Int) :=
  suchThat (Tree.genTree lo hi h n) (·.isBSTb lo hi)

/-! ## Support -/

theorem Tree.genBSTByFiltering.sound {lo hi : Int} (h : lo ≤ hi) (n : Nat) :
    IsSoundFor (Tree.genBSTByFiltering lo hi h n) (Tree.isBST lo hi) := by
  rw [IsSoundFor.iff_obs]
  walk
  next t ht => exact Tree.isBSTb_iff.mp ht

/-! ## Termination -/

theorem Tree.genTree.terminates {lo hi : Int} (h : lo ≤ hi) (n : Nat) :
    IsAlmostSurelyTerminating (Tree.genTree lo hi h n : SPMF (Tree Int)) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [IsAlmostSurelyTerminating.iff_obs, Tree.genTree]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [dite_eq_left rfl]; walk; rfl
    · rw [dite_eq_right (by omega)]
      walk [(ih (n / 2) (by omega)).obs]
      norm_num [add_comm, ENNReal.div_self]

/-- The average over `[lo, hi]` of values at most `d` is at most `d`. -/
private theorem average_le {lo hi : Int} {F : Int → ℝ≥0∞} {d : ℝ≥0∞} (hF : ∀ x, F x ≤ d) :
    (∑ x ∈ Finset.Icc lo hi, F x) / (((hi - lo + 1).toNat : ℕ) : ℝ≥0∞) ≤ d := by
  refine ENNReal.div_le_of_le_mul ?_
  calc ∑ x ∈ Finset.Icc lo hi, F x ≤ ∑ _x ∈ Finset.Icc lo hi, d := Finset.sum_le_sum fun x _ => hF x
    _ = d * (((hi - lo + 1).toNat : ℕ) : ℝ≥0∞) := by
      rw [Finset.sum_const, Int.card_Icc, nsmul_eq_mul, mul_comm,
        show (hi + 1 - lo).toNat = (hi - lo + 1).toNat by omega]

/-- A leaf is a search tree, so at most `n / (n + 1)` of the trees drawn are rejected. -/
theorem Tree.genTree.reject_le {lo hi : Int} (h : lo ≤ hi) (n : Nat) :
    SPMF.expectObs.spec (Tree.genTree lo hi h n : SPMF (Tree Int))
      (fun t => if t.isBSTb lo hi = true then 0 else 1) ≤ n / (n + 1) := by
  have hle : ∀ m (p : Tree Int → ℝ≥0∞),
      SPMF.expectObs.spec (Tree.genTree lo hi h m : SPMF (Tree Int)) p ≤ ⨆ a, p a :=
    fun _ _ => SPMF.expect_le_iSup
  rw [Tree.genTree]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [dite_eq_left rfl]; walk; simp [Tree.isBSTb]
  · rw [dite_eq_right (by omega)]
    walk [hle]
    have hS := average_le (lo := lo) (hi := hi) (d := 1)
      (F := fun x => ⨆ a, ⨆ b,
        if (Tree.node a x b).isBSTb lo hi = true then (0 : ℝ≥0∞) else 1) fun x => by
        simp only [iSup_le_iff]; intros; split <;> simp
    simp only [show (Tree.leaf : Tree Int).isBSTb lo hi = true from rfl, ite_true, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, Nat.cast_one, one_mul, add_zero, Nat.cast_add,
      zero_add]
    rw [add_comm (1 : ℝ≥0∞)]
    gcongr
    exact mul_le_of_le_one_right' hS

theorem Tree.genBSTByFiltering.terminates {lo hi : Int} (h : lo ≤ hi) (n : Nat) :
    IsAlmostSurelyTerminating (Tree.genBSTByFiltering lo hi h n : SPMF (Tree Int)) := by
  rw [IsAlmostSurelyTerminating.iff_obs]
  walk [(Tree.genTree.terminates h n).obs, Tree.genTree.reject_le h n]
  rw [ite_eq_left ⟨le_rfl, ENNReal.div_lt_of_lt_mul (by
    rw [one_mul]; exact_mod_cast n.lt_succ_self)⟩, one_mul]

end BST
