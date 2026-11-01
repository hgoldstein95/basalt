/-
Copyright (c) 2026 Ernest Ng. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Ernest Ng
-/
module

public import Basalt
public import BasaltExamples.Boltzmann.DuchonEtAlRules

/-!
# Ceiled Rejection Sampling of Binary Trees

The ceiled rejection sampler of Duchon et al. (2004, §7) for `genBinaryTree`
(`DuchonEtAlBoltzmann`): each draw is interrupted as soon as it exceeds the window's upper end. For
every `p` it has `genBinaryTree`'s law conditioned on the window, and it terminates whether or not
`genBinaryTree` does.
-/

@[expose] public section

open RandomChoice SPMF
open scoped ENNReal

namespace Boltzmann

/-- The paper's `Γ B_{<k}`: `genBinaryTree` with a budget of `k` atoms, its global counter `K` made
a parameter. It keeps trees of at most `k` atoms, gives up (`none`) as soon as the tree would exceed
the budget, and returns the budget left. -/
def genBinaryTreeCeil [Gen G] (p : Rat) (k : Nat) : G (Option (BinaryTree × Nat)) := do
  if k = 0 then return none
  if ← coin p then return some (.leaf, k - 1)
  match ← genBinaryTreeCeil p (k - 1) with
  | none => return none
  | some (l, k') =>
    match ← genBinaryTreeCeil p k' with
    | none => return none
    | some (r, k'') => return some (.node l r, k'')
partial_fixpoint

/-- One round of `ν_B`: a ceiled draw, kept if it reaches the lower bound. -/
def roundBinaryTree [Gen G] (p : Rat) (lo hi : Nat) : G (Option BinaryTree) := do
  match ← genBinaryTreeCeil p hi with
  | some (t, _) => return if lo ≤ t.size then some t else none
  | none => return none

/-- `ν_B(x; n, ε)`: `repeat γ := Γ B_{<hi} until γ ≠ ⊥ ∧ |γ| ≥ lo`. -/
def ceiled [Gen G] (p : Rat) (lo hi : Nat) : G BinaryTree :=
  (fun o => o.getD .leaf) <$> suchThat (roundBinaryTree p lo hi) Option.isSome

/-- Run to the end, the ceiled sampler gives `genBinaryTree`'s mass to each tree that fits the
budget. -/
theorem genBinaryTreeCeil_apply (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (t : BinaryTree) :
    ∀ k k', (genBinaryTreeCeil p k : SPMF _) (some (t, k'))
      = if t.size ≤ k ∧ k' = k - t.size then (genBinaryTree p : SPMF BinaryTree) t else 0 := by
  induction t with
  | leaf =>
    intro k k'
    rcases k with _ | j
    · rw [genBinaryTreeCeil]; simp [BinaryTree.size]
    rw [genBinaryTreeCeil]
    simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    rw [bind_apply, tsum_bool]
    simp only [Bool.false_eq_true, ↓reduceIte, coin_true hp0 hp1]
    rw [bind_apply, ENNReal.tsum_eq_zero.2 fun o => ?_]
    · by_cases hk : k' = j <;>
        simp [hk, BinaryTree.size, genBinaryTree_apply hp0 hp1, BinaryTree.internal]
    rcases o with _ | ⟨l, k1⟩
    · simp
    · rw [bind_apply, ENNReal.tsum_eq_zero.2 fun o' => ?_, mul_zero]
      rcases o' with _ | ⟨r, k2⟩ <;> simp
  | node l r ihl ihr =>
    intro k k'
    rcases k with _ | j
    · rw [genBinaryTreeCeil]; simp [BinaryTree.size]
    rw [genBinaryTreeCeil]
    simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    rw [bind_apply, tsum_bool]
    simp only [Bool.false_eq_true, ↓reduceIte, coin_false hp0 hp1]
    rw [bind_apply, tsum_eq_single (some (l, j - l.size)) fun o ho => ?_]
    · rw [bind_apply, tsum_eq_single (some (r, k')) fun o' ho' => ?_]
      · simp only [pure_apply, ite_true, mul_one]
        rw [ihl, ihr, genBinaryTree_node hp0 hp1]
        simp only [BinaryTree.size]
        by_cases hl : l.size ≤ j <;> by_cases hr : r.size ≤ j - l.size <;>
          by_cases hk : k' = j - l.size - r.size <;>
          simp [hl, hr, hk] <;> omega
      · rcases o' with _ | ⟨r', k2⟩
        · simp
        · simp only [pure_apply]
          split_ifs with h
          · simp only [Option.some.injEq, Prod.mk.injEq, BinaryTree.node.injEq, true_and] at h
            obtain ⟨rfl, rfl⟩ := h
            exact absurd rfl ho'
          · rw [mul_zero]
    · rcases o with _ | ⟨l', k1⟩
      · simp
      · by_cases hl : l' = l
        · subst hl
          rw [ihl, ite_eq_right_iff.2 (fun h => absurd (by rw [h.2]) ho), zero_mul]
        · rw [bind_apply, ENNReal.tsum_eq_zero.2 fun o' => ?_, mul_zero]
          rcases o' with _ | ⟨r', k2⟩ <;> simp [Ne.symm hl]

/-- The ceiled sampler always halts: the budget shrinks on every call. -/
theorem genBinaryTreeCeil_mass (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (k : Nat) :
    (genBinaryTreeCeil p k : SPMF _).mass = 1 := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  rcases k with _ | j
  · rw [genBinaryTreeCeil]; simp
  rw [genBinaryTreeCeil]
  simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
  rw [mass_bind_tsum, tsum_bool]
  simp only [Bool.false_eq_true, ↓reduceIte, coin_false hp0 hp1, coin_true hp0 hp1, mass_pure,
    mul_one]
  rw [mass_bind_of_mass_one ?_, ih j (by omega), mul_one,
    tsub_add_cancel_of_le (pr_le_one hp0 hp1)]
  rintro (_ | ⟨l, k'⟩) hne
  · simp
  · have hk : k' ≤ j := by
      rw [genBinaryTreeCeil_apply hp0 hp1] at hne
      by_contra hk
      exact hne (ite_eq_right_iff.2 fun h => absurd h (by omega))
    rw [mass_bind_of_mass_one (by rintro (_ | ⟨r, k''⟩) _ <;> simp), ih k' (by omega)]

/-- One round keeps each tree in the window with `genBinaryTree`'s mass. -/
theorem roundBinaryTree_some (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (lo hi : Nat) (t : BinaryTree) :
    (roundBinaryTree p lo hi : SPMF _) (some t)
      = if between lo hi t then (genBinaryTree p : SPMF BinaryTree) t else 0 := by
  rw [roundBinaryTree, bind_apply, tsum_option, ENNReal.tsum_prod', tsum_eq_single t fun t' ht' =>
    ENNReal.tsum_eq_zero.2 fun k => by dsimp only; split_ifs <;> simp [Ne.symm ht'],
    tsum_eq_single (hi - t.size) fun k hk => by
      rw [genBinaryTreeCeil_apply hp0 hp1, ite_eq_right_iff.2 fun h => absurd h (by omega),
        zero_mul]]
  simp only [pure_apply, reduceCtorEq, ↓reduceIte, mul_zero, zero_add,
    genBinaryTreeCeil_apply hp0 hp1]
  by_cases h1 : lo ≤ t.size <;> by_cases h2 : t.size ≤ hi <;> simp [between, h1, h2]

theorem roundBinaryTree_mass (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (lo hi : Nat) :
    (roundBinaryTree p lo hi : SPMF _).mass = 1 := by
  rw [roundBinaryTree, mass_bind_of_mass_one (by rintro (_ | ⟨t, k⟩) _ <;> simp),
    genBinaryTreeCeil_mass hp0 hp1]

/-- **The law of the ceiled rejection sampler**, for every `p`: `genBinaryTree` conditioned on the
window. -/
theorem ceiled_apply (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (lo hi : Nat) (t : BinaryTree) :
    (ceiled p lo hi : SPMF BinaryTree) t
      = (if between lo hi t then (genBinaryTree p : SPMF BinaryTree) t else 0)
        / prob (genBinaryTree p : SPMF BinaryTree) {t | between lo hi t = true} := by
  classical
  have hsum := roundBinaryTree_mass hp0 hp1 lo hi
  rw [mass, tsum_option] at hsum
  have hQ : 1 - (roundBinaryTree p lo hi : SPMF _) none
      = prob (genBinaryTree p : SPMF BinaryTree) {t | between lo hi t = true} := by
    rw [← hsum, ENNReal.add_sub_cancel_left (apply_ne_top _ _), prob_eq_tsum_ite]
    exact tsum_congr fun t => by rw [roundBinaryTree_some hp0 hp1]; simp
  rw [ceiled, getD_suchThat_isSome_apply, hQ, roundBinaryTree_some hp0 hp1]

/-- The ceiled sampler terminates for every `0 < p < 1`, with no termination of `genBinaryTree`
assumed, once some tree lies in the window. -/
theorem ceiled_terminates (hp0 : 0 < p) (hp1 : p < 1) (hw : ∃ t, between lo hi t = true) :
    IsAlmostSurelyTerminating (ceiled p lo hi : SPMF BinaryTree) := by
  obtain ⟨t₀, ht₀⟩ := hw
  have hx0 : pr p ≠ 0 := by
    rw [pr_eq_ofReal hp0.le]; exact (ENNReal.ofReal_pos.2 (by exact_mod_cast hp0)).ne'
  have hx1 : pr p < 1 := by
    rw [pr_eq_ofReal hp0.le]; exact ENNReal.ofReal_lt_one.2 (by exact_mod_cast hp1)
  set Q := prob (genBinaryTree p : SPMF BinaryTree) {t | between lo hi t = true}
  have hQsum :
      (∑' t, if between lo hi t = true then (genBinaryTree p : SPMF BinaryTree) t else 0) = Q := by
    simp only [Q, prob_eq_tsum_ite, Set.mem_ofPred_eq]
  have hQ0 : Q ≠ 0 := by
    rw [← hQsum]
    refine (lt_of_lt_of_le ?_ (ENNReal.le_tsum t₀)).ne'
    simp only [ht₀, ↓reduceIte]
    rw [genBinaryTree_apply hp0.le hp1.le]
    exact pos_iff_ne_zero.2 (mul_ne_zero (pow_ne_zero _ hx0)
      (pow_ne_zero _ (tsub_pos_of_lt hx1).ne'))
  have hQtop : Q ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top
    ((prob_le_mass _ _).trans (mass_le_one _))
  unfold IsAlmostSurelyTerminating mass
  simp_rw [ceiled_apply hp0.le hp1.le, div_eq_mul_inv]
  rw [ENNReal.tsum_mul_right, hQsum, ENNReal.mul_inv_cancel hQ0 hQtop]

end Boltzmann
