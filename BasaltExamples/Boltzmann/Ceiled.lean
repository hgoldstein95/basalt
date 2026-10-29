/-
Copyright (c) 2026 Ernest Ng. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Ernest Ng
-/
module

public import Basalt
public import BasaltExamples.Boltzmann.Rules

/-!
# Ceiled Rejection Sampling of Binary Trees

The ceiled rejection sampler of Duchon et al. (2004, §7) for `genB` (`BasaltExamples/Boltzmann`):
each draw is interrupted as soon as it exceeds the window's upper end. For every `p` it has `genB`'s
law conditioned on the window, and it terminates whether or not `genB` does; when `genB` terminates
it equals straight rejection (`ceiled_eq_suchThat`).
-/

@[expose] public section

open RandomChoice SPMF
open scoped ENNReal

namespace Boltzmann

/-- The paper's `Γ B_{<k}`: `genB` with a budget of `k` atoms, its global counter `K` made a
parameter. It keeps trees of at most `k` atoms, gives up (`none`) as soon as the tree would exceed
the budget, and returns the budget left. -/
def genBCeil [Gen G] (p : Rat) (k : Nat) : G (Option (BTree × Nat)) := do
  if k = 0 then return none
  if ← coin p then return some (.leaf, k - 1)
  match ← genBCeil p (k - 1) with
  | none => return none
  | some (l, k') =>
    match ← genBCeil p k' with
    | none => return none
    | some (r, k'') => return some (.node l r, k'')
partial_fixpoint

/-- One round of `ν_B`: a ceiled draw, kept if it reaches the lower bound. -/
def roundB [Gen G] (p : Rat) (lo hi : Nat) : G (Option BTree) := do
  match ← genBCeil p hi with
  | some (t, _) => return if lo ≤ t.size then some t else none
  | none => return none

/-- `ν_B(x; n, ε)`: `repeat γ := Γ B_{<hi} until γ ≠ ⊥ ∧ |γ| ≥ lo`. -/
def ceiled [Gen G] (p : Rat) (lo hi : Nat) : G BTree :=
  retry (roundB p lo hi)

/-- Run to the end, the ceiled sampler gives `genB`'s mass to each tree that fits the budget. -/
theorem genBCeil_apply (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (t : BTree) :
    ∀ k k', (genBCeil p k : SPMF _) (some (t, k'))
      = if t.size ≤ k ∧ k' = k - t.size then (genB p : SPMF BTree) t else 0 := by
  induction t with
  | leaf =>
    intro k k'
    rcases k with _ | j
    · rw [genBCeil]; simp [BTree.size]
    rw [genBCeil]
    simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    rw [bind_apply, tsum_bool]
    simp only [Bool.false_eq_true, ↓reduceIte, coin_true hp0 hp1]
    rw [bind_apply, ENNReal.tsum_eq_zero.2 fun o => ?_]
    · by_cases hk : k' = j <;> simp [hk, BTree.size, genB_apply hp0 hp1, BTree.internal]
    rcases o with _ | ⟨l, k1⟩
    · simp
    · rw [bind_apply, ENNReal.tsum_eq_zero.2 fun o' => ?_, mul_zero]
      rcases o' with _ | ⟨r, k2⟩ <;> simp
  | node l r ihl ihr =>
    intro k k'
    rcases k with _ | j
    · rw [genBCeil]; simp [BTree.size]
    rw [genBCeil]
    simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    rw [bind_apply, tsum_bool]
    simp only [Bool.false_eq_true, ↓reduceIte, coin_false hp0 hp1]
    rw [bind_apply, tsum_eq_single (some (l, j - l.size)) fun o ho => ?_]
    · rw [bind_apply, tsum_eq_single (some (r, k')) fun o' ho' => ?_]
      · simp only [pure_apply, ite_true, mul_one]
        rw [ihl, ihr, genB_node hp0 hp1]
        simp only [BTree.size]
        by_cases hl : l.size ≤ j <;> by_cases hr : r.size ≤ j - l.size <;>
          by_cases hk : k' = j - l.size - r.size <;>
          simp [hl, hr, hk] <;> omega
      · rcases o' with _ | ⟨r', k2⟩
        · simp
        · simp only [pure_apply]
          split_ifs with h
          · simp only [Option.some.injEq, Prod.mk.injEq, BTree.node.injEq, true_and] at h
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
theorem genBCeil_mass (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (k : Nat) : (genBCeil p k : SPMF _).mass = 1 := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  rcases k with _ | j
  · rw [genBCeil]; simp
  rw [genBCeil]
  simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
  rw [mass_bind_tsum, tsum_bool]
  simp only [Bool.false_eq_true, ↓reduceIte, coin_false hp0 hp1, coin_true hp0 hp1, mass_pure,
    mul_one]
  rw [mass_bind_of_mass_one ?_, ih j (by omega), mul_one,
    tsub_add_cancel_of_le (pr_le_one hp0 hp1)]
  rintro (_ | ⟨l, k'⟩) hne
  · simp
  · have hk : k' ≤ j := by
      rw [genBCeil_apply hp0 hp1] at hne
      by_contra hk
      exact hne (ite_eq_right_iff.2 fun h => absurd h (by omega))
    rw [mass_bind_of_mass_one (by rintro (_ | ⟨r, k''⟩) _ <;> simp), ih k' (by omega)]

/-- One round keeps each tree in the window with `genB`'s mass. -/
theorem roundB_some (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (lo hi : Nat) (t : BTree) :
    (roundB p lo hi : SPMF _) (some t)
      = if window lo hi t then (genB p : SPMF BTree) t else 0 := by
  rw [roundB, bind_apply, tsum_option, ENNReal.tsum_prod', tsum_eq_single t fun t' ht' =>
    ENNReal.tsum_eq_zero.2 fun k => by dsimp only; split_ifs <;> simp [Ne.symm ht'],
    tsum_eq_single (hi - t.size) fun k hk => by
      rw [genBCeil_apply hp0 hp1, ite_eq_right_iff.2 fun h => absurd h (by omega), zero_mul]]
  simp only [pure_apply, reduceCtorEq, ↓reduceIte, mul_zero, zero_add, genBCeil_apply hp0 hp1]
  by_cases h1 : lo ≤ t.size <;> by_cases h2 : t.size ≤ hi <;> simp [window, h1, h2]

theorem roundB_mass (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (lo hi : Nat) :
    (roundB p lo hi : SPMF _).mass = 1 := by
  rw [roundB, mass_bind_of_mass_one (by rintro (_ | ⟨t, k⟩) _ <;> simp), genBCeil_mass hp0 hp1]

/-- **The law of the ceiled rejection sampler**, for every `p`: `genB` conditioned on the window. -/
theorem ceiled_apply (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (lo hi : Nat) (t : BTree) :
    (ceiled p lo hi : SPMF BTree) t
      = (if window lo hi t then (genB p : SPMF BTree) t else 0)
        / prob (genB p : SPMF BTree) {t | window lo hi t = true} := by
  classical
  have hsum := roundB_mass hp0 hp1 lo hi
  rw [mass, tsum_option] at hsum
  have hQ : 1 - (roundB p lo hi : SPMF _) none
      = prob (genB p : SPMF BTree) {t | window lo hi t = true} := by
    rw [← hsum, ENNReal.add_sub_cancel_left (apply_ne_top _ _), prob_eq_tsum_ite]
    exact tsum_congr fun t => by rw [roundB_some hp0 hp1]; simp
  rw [ceiled, retry_apply, hQ, roundB_some hp0 hp1]

/-- **Ceiled rejection = straight rejection**, when `genB` terminates. -/
theorem ceiled_eq_suchThat (hp : 1/2 ≤ p) (hp1 : p ≤ 1) (lo hi : Nat) :
    (ceiled p lo hi : SPMF BTree) = suchThat (genB p) (window lo hi) := by
  ext t
  rw [ceiled_apply (le_trans (by norm_num) hp) hp1,
    suchThat_apply_of_mass _ _ (genB_terminates hp hp1)]
  split <;> simp

/-- The ceiled sampler terminates for every `0 < p < 1`, with no termination of `genB` assumed,
once some tree lies in the window. -/
theorem ceiled_terminates (hp0 : 0 < p) (hp1 : p < 1) (hw : ∃ t, window lo hi t = true) :
    IsAlmostSurelyTerminating (ceiled p lo hi : SPMF BTree) := by
  obtain ⟨t₀, ht₀⟩ := hw
  have hx0 : pr p ≠ 0 := by
    rw [pr_eq_ofReal hp0.le]; exact (ENNReal.ofReal_pos.2 (by exact_mod_cast hp0)).ne'
  have hx1 : pr p < 1 := by
    rw [pr_eq_ofReal hp0.le]; exact ENNReal.ofReal_lt_one.2 (by exact_mod_cast hp1)
  set Q := prob (genB p : SPMF BTree) {t | window lo hi t = true}
  have hQsum : (∑' t, if window lo hi t = true then (genB p : SPMF BTree) t else 0) = Q := by
    simp only [Q, prob_eq_tsum_ite, Set.mem_ofPred_eq]
  have hQ0 : Q ≠ 0 := by
    rw [← hQsum]
    refine (lt_of_lt_of_le ?_ (ENNReal.le_tsum t₀)).ne'
    simp only [ht₀, ↓reduceIte]
    rw [genB_apply hp0.le hp1.le]
    exact pos_iff_ne_zero.2 (mul_ne_zero (pow_ne_zero _ hx0)
      (pow_ne_zero _ (tsub_pos_of_lt hx1).ne'))
  have hQtop : Q ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top
    ((prob_le_mass _ _).trans (mass_le_one _))
  unfold IsAlmostSurelyTerminating mass
  simp_rw [ceiled_apply hp0.le hp1.le, div_eq_mul_inv]
  rw [ENNReal.tsum_mul_right, hQsum, ENNReal.mul_inv_cancel hQ0 hQtop]

end Boltzmann
