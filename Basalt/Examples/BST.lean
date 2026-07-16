import Basalt
import Basalt.Combinators

open RandomChoice

namespace BST

inductive Tree (α : Type) where
  | leaf : Tree α
  | node : Tree α → α → Tree α → Tree α
deriving Repr

def Tree.size : Tree α → Nat
  | leaf => 0
  | node l _ r => l.size + r.size + 1

def Tree.isBST (lo hi : Nat) : Tree Nat → Prop
  | leaf => true
  | node l x r =>
    lo ≤ x ∧ x ≤ hi ∧
    isBST lo (x - 1) l ∧
    isBST (x + 1) hi r

def Tree.genBST [Gen G] (lo hi : Nat) : G (Tree Nat) := do
  if h : lo > hi then
    return leaf
  else
    pick
      (fun () => pure leaf)
      (fun () => do
        let x ← choose lo hi (by omega)
        let l ← Tree.genBST lo (x.down.val - 1)
        let r ← Tree.genBST (x.down.val + 1) hi
        return node l x.down.val r)
partial_fixpoint

tunable def Tree.genWeightedBST [Gen G] (lo hi : Nat) : G (Tree Nat) := do
  if h : lo > hi then
    return leaf
  else
    frequency [
      (1, fun _ => pure leaf),
      (5, fun _ => do
        let x ← choose lo hi (by omega)
        let l ← Tree.genWeightedBST lo (x.down.val - 1)
        let r ← Tree.genWeightedBST (x.down.val + 1) hi
        return node l x.down.val r)
    ] (by dsimp; omega)
partial_fixpoint

theorem Tree.genBST_support :
    t ∈ SPMF.support (Tree.genBST lo hi) ↔ t ∈ {t | Tree.isBST lo hi t} := by
  simp
  fun_induction Tree.isBST
    <;> rw [Tree.genBST]
    <;> split
    <;> simp
    <;> grind

theorem Tree.genBST_terminates : SPMF.IsPMF (Tree.genBST lo hi) := by
  haveI : Nonempty (Nat × Nat) := ⟨(0, 0)⟩
  refine (SPMF.IsPMF_of_mass_fixpoint
      (g := fun (lo, hi) => (Tree.genBST lo hi : SPMF (Tree Nat)))
      (F := fun c => 1 / 2 + 1 / 2 * c ^ 2)
      ?bounds ?mass) (lo, hi)
  case bounds =>
    intro c hle hge
    apply ENNReal.eq_one_of_fixed_ineq' hle hge
    intro hmono
    rw [ENNReal.toReal_add (by norm_num) (by aesop), ENNReal.toReal_mul] at hmono
    norm_num at hmono
    nlinarith [sq_nonneg c.toReal]
  case mass =>
    intro ⟨lo, hi⟩ hc_le
    dsimp only
    by_cases hlt : lo > hi
    · rw [Tree.genBST, dif_pos hlt, SPMF.mass_pure]
      conv_lhs => rw [← ENNReal.add_halves 1]
      gcongr
      exact mul_le_of_le_one_right (by positivity) (pow_le_one₀ (by positivity) hc_le)
    · push Not at hlt
      conv_lhs => rw [Tree.genBST, dif_neg (by omega)]
      simp only [SPMF.mass_pick, SPMF.mass_pure, mul_one]
      gcongr
      rw [sq]
      apply SPMF.mass_bind_ge_of_isPMF (SPMF.IsPMF_choose lo hi hlt)
      intro x
      apply SPMF.mass_bind_ge_mul (SPMF.mass_ge_iInf _ (lo, x.down.val - 1))
      intro l
      simp only [SPMF.mass_bind_pure]
      exact SPMF.mass_ge_iInf _ (x.down.val + 1, hi)

theorem Tree.genBST_cost :
    IsBounded (Tree.genBST lo hi) (fun t => 3 * t.size + 1) := by
  open Lean.Order in
  delta genBST
  apply (fix_induct (motive := fun (g : Nat → Nat → SPMF.Cost (Tree Nat)) => ∀ lo hi, IsBounded (g lo hi) (fun t => 3 * t.size + 1)) _ ?admissible ?step)
  case admissible =>
    exact admissible_pi_apply _ fun _ => admissible_pi_apply _ fun _ => admissible_IsBounded _
  case step =>
    intro genBST_rec ih lo hi
    simp [IsBounded_iff] at *
    intro t n hn
    grind [
      pick,
      size,
      SPMF.Cost.mem_support_bind_iff,
      SPMF.Cost.mem_support_choose_iff,
      SPMF.Cost.mem_support_pure_iff
    ]

instance {lo hi : Nat} : LawfulGenerator (Tree.genBST lo hi) (Tree.isBST lo hi) (fun t => 3 * t.size + 1) where
  support_iff := Tree.genBST_support
  is_pmf := Tree.genBST_terminates
  is_bounded := Tree.genBST_cost

section weighted_termination

open SPMF
open scoped NNReal ENNReal

noncomputable def weightedBSTLevel (e : Nat × Nat → ℝ≥0∞) (p : Nat × Nat) : ℝ≥0∞ :=
  if p.1 > p.2 then 0
  else 5 / 6 * ((∑ x ∈ Finset.Icc p.1 p.2, (e (p.1, x - 1) + e (x + 1, p.2)))
    / ((p.2 - p.1 + 1 : ℕ) : ℝ≥0∞))

def weightedBSTRank (p : Nat × Nat) : Nat :=
  (p.2 + 1 - p.1) + 1 + (if p.1 = 0 then 4 else 0)

private theorem levelOp_weightedBSTLevel : LevelOp weightedBSTLevel := by
  constructor
  · -- mono
    intro e f hef p
    unfold weightedBSTLevel
    split
    · exact le_rfl
    · gcongr with x hx <;> exact hef _
  · -- add
    intro e f
    funext p
    simp only [weightedBSTLevel, Pi.add_apply]
    split
    · simp
    · simp only [add_add_add_comm, Finset.sum_add_distrib, ← ENNReal.div_add_div_same, mul_add]
  · -- smul
    intro r e
    funext p
    simp only [weightedBSTLevel]
    split
    · simp
    · simp only [← mul_add, ← Finset.mul_sum, ← mul_div_assoc, mul_left_comm]

private lemma five_sixths_add_sixth : (5 / 6 : ℝ≥0∞) + 1 / 6 = 1 := by
  rw [ENNReal.div_add_div_same, show (5 : ℝ≥0∞) + 1 = 6 by norm_num]
  exact ENNReal.div_self (by norm_num) (by norm_num)

private lemma five_sixths_split (t : ℝ≥0∞) : 5 / 6 * t + 1 / 6 * t = t := by
  rw [← add_mul, five_sixths_add_sixth, one_mul]

private lemma five_sixths_le {t : ℝ≥0∞} (ht : 1 ≤ t) : 5 / 6 * t + 1 / 6 ≤ t :=
  calc 5 / 6 * t + 1 / 6 = 5 / 6 * t + 1 / 6 * 1 := by rw [mul_one]
    _ ≤ 5 / 6 * t + 1 / 6 * t := by gcongr
    _ = t := five_sixths_split t

private lemma five_sixths_le' {t : ℝ≥0∞} (ht : 6 ≤ t) : 5 / 6 * (t + 1) + 1 / 6 ≤ t :=
  calc 5 / 6 * (t + 1) + 1 / 6
      = 5 / 6 * t + (5 / 6 + 1 / 6) := by ring
    _ = 5 / 6 * t + 1 / 6 * 6 := by
        rw [five_sixths_add_sixth, one_div, ENNReal.inv_mul_cancel (by norm_num) (by norm_num)]
    _ ≤ 5 / 6 * t + 1 / 6 * t := by gcongr
    _ = t := five_sixths_split t

/-- Away from `lo = 0`, the children's total rank equals the parent's rank *exactly, for every
  pivot* — the interval partitions. Summed over the `hi - lo + 1` pivots: -/
private lemma weightedBSTRank_sum_pos {lo hi : Nat} (h1 : 1 ≤ lo) (hle : lo ≤ hi) :
    ∑ x ∈ Finset.Icc lo hi, (weightedBSTRank (lo, x - 1) + weightedBSTRank (x + 1, hi))
      = (hi - lo + 1) * weightedBSTRank (lo, hi) := by
  have hterm : ∀ x ∈ Finset.Icc lo hi,
      weightedBSTRank (lo, x - 1) + weightedBSTRank (x + 1, hi)
        = weightedBSTRank (lo, hi) := by
    intro x hx
    rw [Finset.mem_Icc] at hx
    have hlo : ¬(lo = 0) := by omega
    have hx1 : ¬(x + 1 = 0) := by omega
    simp only [weightedBSTRank, if_neg hlo, if_neg hx1]
    omega
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, Nat.card_Icc, smul_eq_mul]
  congr 1
  omega

/-- At `lo = 0` the pivot `x = 0` recurses on `(0, 0)` — an *unshrunk* child — and the
  children's total rank exceeds the parent's by exactly 1 at that pivot (and only there). -/
private lemma weightedBSTRank_sum_zero (hi : Nat) :
    ∑ x ∈ Finset.Icc 0 hi, (weightedBSTRank (0, x - 1) + weightedBSTRank (x + 1, hi))
      = (hi + 1) * weightedBSTRank (0, hi) + 1 := by
  have hsplit : Finset.Icc 0 hi = insert 0 (Finset.Icc 1 hi) := by
    ext y
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have h0 : (0 : Nat) ∉ Finset.Icc 1 hi := by simp
  have hhead : weightedBSTRank (0, 0 - 1) + weightedBSTRank (0 + 1, hi)
      = weightedBSTRank (0, hi) + 1 := by
    simp only [weightedBSTRank, if_neg (by omega : ¬(0 + 1 = 0))]
    omega
  have htail : ∀ x ∈ Finset.Icc 1 hi,
      weightedBSTRank (0, x - 1) + weightedBSTRank (x + 1, hi)
        = weightedBSTRank (0, hi) := by
    intro x hx
    rw [Finset.mem_Icc] at hx
    simp only [weightedBSTRank, if_neg (by omega : ¬(x + 1 = 0))]
    omega
  rw [hsplit, Finset.sum_insert h0, hhead, Finset.sum_congr rfl htail, Finset.sum_const,
    Nat.card_Icc, smul_eq_mul]
  have : hi + 1 - 1 = hi := by omega
  rw [this]
  ring

private theorem genWeightedBST_drift (p : Nat × Nat) :
    weightedBSTLevel (fun q => (weightedBSTRank q : ℝ≥0∞)) p + 1 / 6
      ≤ (weightedBSTRank p : ℝ≥0∞) := by
  obtain ⟨lo, hi⟩ := p
  have hrank1 : (1 : ℝ≥0∞) ≤ (weightedBSTRank (lo, hi) : ℝ≥0∞) := by
    exact_mod_cast (show 1 ≤ weightedBSTRank (lo, hi) by simp only [weightedBSTRank]; omega)
  unfold weightedBSTLevel
  by_cases hgt : lo > hi
  · rw [if_pos hgt, zero_add]
    exact (ENNReal.div_le_of_le_mul (by norm_num)).trans hrank1
  · push Not at hgt
    rw [if_neg (by omega)]
    simp only
    by_cases hlo : lo = 0
    · subst hlo
      have hcast : (∑ x ∈ Finset.Icc 0 hi,
            ((weightedBSTRank (0, x - 1) : ℝ≥0∞) + (weightedBSTRank (x + 1, hi) : ℝ≥0∞)))
          = ((hi + 1 : ℕ) : ℝ≥0∞) * (weightedBSTRank (0, hi) : ℝ≥0∞) + 1 := by
        exact_mod_cast congrArg (Nat.cast (R := ℝ≥0∞)) (weightedBSTRank_sum_zero hi)
      have hne0 : ((hi + 1 : ℕ) : ℝ≥0∞) ≠ 0 := by
        exact_mod_cast (Nat.succ_ne_zero hi)
      have h6 : (6 : ℝ≥0∞) ≤ (weightedBSTRank (0, hi) : ℝ≥0∞) := by
        exact_mod_cast (show 6 ≤ weightedBSTRank (0, hi) by
          simp only [weightedBSTRank, reduceIte]; omega)
      rw [Nat.sub_zero, hcast, ENNReal.add_div, mul_div_assoc,
        ENNReal.mul_div_cancel hne0 (ENNReal.natCast_ne_top _)]
      calc 5 / 6 * ((weightedBSTRank (0, hi) : ℝ≥0∞) + 1 / ((hi + 1 : ℕ) : ℝ≥0∞)) + 1 / 6
          ≤ 5 / 6 * ((weightedBSTRank (0, hi) : ℝ≥0∞) + 1) + 1 / 6 := by
            gcongr
            exact ENNReal.div_le_of_le_mul
              (by rw [one_mul]; exact Nat.one_le_cast.mpr hi.succ_pos)
        _ ≤ (weightedBSTRank (0, hi) : ℝ≥0∞) := five_sixths_le' h6
    · have hcast : (∑ x ∈ Finset.Icc lo hi,
            ((weightedBSTRank (lo, x - 1) : ℝ≥0∞) + (weightedBSTRank (x + 1, hi) : ℝ≥0∞)))
          = ((hi - lo + 1 : ℕ) : ℝ≥0∞) * (weightedBSTRank (lo, hi) : ℝ≥0∞) := by
        exact_mod_cast congrArg (Nat.cast (R := ℝ≥0∞))
          (weightedBSTRank_sum_pos (by omega) hgt)
      have hne0 : ((hi - lo + 1 : ℕ) : ℝ≥0∞) ≠ 0 := by
        exact_mod_cast (Nat.succ_ne_zero (hi - lo))
      rw [hcast, mul_div_assoc, ENNReal.mul_div_cancel hne0 (ENNReal.natCast_ne_top _)]
      exact five_sixths_le hrank1

private lemma div6_split (M : ℝ≥0∞) : (1 + 5 * M) / 6 = 1 / 6 + 5 / 6 * M := by
  rw [ENNReal.add_div, ENNReal.mul_div_right_comm]

private theorem genWeightedBST_mass_ge (lo hi : Nat) (hle : lo ≤ hi) :
    (Tree.genWeightedBST lo hi : SPMF (Tree Nat)).mass
      ≥ 1 / 6 + 5 / 6 * ((∑ x ∈ Finset.Icc lo hi,
            (Tree.genWeightedBST lo (x - 1) : SPMF (Tree Nat)).mass
              * (Tree.genWeightedBST (x + 1) hi : SPMF (Tree Nat)).mass)
          / ((hi - lo + 1 : ℕ) : ℝ≥0∞)) := by
  conv_lhs => rw [Tree.genWeightedBST]
  rw [dif_neg (by omega)]
  rw [mass_frequency]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, mass_pure,
    Nat.cast_one, Nat.cast_ofNat, add_zero, mul_one]
  rw [show ((1 + 5 : ℕ) : ℝ≥0∞) = 6 by norm_num, div6_split]
  gcongr
  refine mass_bind_choose_ge hle fun a => ?_
  refine mass_bind_ge_mul le_rfl fun l => ?_
  rw [mass_bind_pure]

private theorem genWeightedBST_step (p : Nat × Nat) :
    1 - (Tree.genWeightedBST p.1 p.2 : SPMF (Tree Nat)).mass
      ≤ weightedBSTLevel
          (fun q => 1 - (Tree.genWeightedBST q.1 q.2 : SPMF (Tree Nat)).mass) p := by
  obtain ⟨lo, hi⟩ := p
  unfold weightedBSTLevel
  by_cases hgt : lo > hi
  · rw [if_pos hgt, Tree.genWeightedBST, dif_pos hgt]
    simp
  · push Not at hgt
    rw [if_neg (by omega)]
    simp only
    have hne0 : ((hi - lo + 1 : ℕ) : ℝ≥0∞) ≠ 0 := by
      exact_mod_cast (Nat.succ_ne_zero (hi - lo))
    have hcard : ((hi - lo + 1 : ℕ) : ℝ≥0∞) ≤ ((Finset.Icc lo hi).card : ℝ≥0∞) := by
      rw [Nat.card_Icc]
      norm_cast
      omega
    calc 1 - (Tree.genWeightedBST lo hi : SPMF (Tree Nat)).mass
        ≤ 5 / 6 * (1 - (∑ x ∈ Finset.Icc lo hi,
              (Tree.genWeightedBST lo (x - 1) : SPMF (Tree Nat)).mass
                * (Tree.genWeightedBST (x + 1) hi : SPMF (Tree Nat)).mass)
            / ((hi - lo + 1 : ℕ) : ℝ≥0∞)) :=
          ENNReal.one_sub_le_mul_one_sub (by rw [add_comm]; exact five_sixths_add_sixth)
            (ENNReal.div_lt_top (by norm_num) (by norm_num)).ne
            (genWeightedBST_mass_ge lo hi hgt)
      _ ≤ 5 / 6 * ((∑ x ∈ Finset.Icc lo hi,
              (1 - (Tree.genWeightedBST lo (x - 1) : SPMF (Tree Nat)).mass
                * (Tree.genWeightedBST (x + 1) hi : SPMF (Tree Nat)).mass))
            / ((hi - lo + 1 : ℕ) : ℝ≥0∞)) := by
          gcongr 5 / 6 * ?_
          exact ENNReal.one_sub_sum_div_le hne0 (ENNReal.natCast_ne_top _) hcard
            fun x _ => mul_le_one' (mass_le_one _) (mass_le_one _)
      _ ≤ 5 / 6 * ((∑ x ∈ Finset.Icc lo hi,
              ((1 - (Tree.genWeightedBST lo (x - 1) : SPMF (Tree Nat)).mass)
                + (1 - (Tree.genWeightedBST (x + 1) hi : SPMF (Tree Nat)).mass)))
            / ((hi - lo + 1 : ℕ) : ℝ≥0∞)) := by
          gcongr with x hx
          exact ENNReal.one_sub_mul_le_add (mass_le_one _) (mass_le_one _)

theorem Tree.genWeightedBST_terminates : SPMF.IsPMF (Tree.genWeightedBST lo hi) := by
  refine SPMF.IsPMF_of_ranking
    (fun p : Nat × Nat => (Tree.genWeightedBST p.1 p.2 : SPMF (Tree Nat)))
    levelOp_weightedBSTLevel
    (fun p => (weightedBSTRank p : ℝ≥0∞))
    (fun p => ENNReal.natCast_ne_top _)
    (ε := 1 / 6) (ENNReal.div_pos one_ne_zero (by norm_num))
    genWeightedBST_drift genWeightedBST_step (lo, hi)

theorem Tree.genWeightedBST_support :
    t ∈ SPMF.support (Tree.genWeightedBST lo hi) ↔ Tree.isBST lo hi t := by
  fun_induction Tree.isBST
    <;> rw [Tree.genWeightedBST]
    <;> split
    <;> simp
  · -- leaf, `lo ≤ hi`: witness the (weight-1) leaf branch of the `frequency`.
    exact ⟨1, fun _ => Pure.pure .leaf, Or.inl ⟨rfl, rfl⟩, one_pos, by simp⟩
  · -- node, `lo > hi`: no pivot fits.
    intros
    omega
  · -- node, `lo ≤ hi`: only the (weight-5) node branch can produce a `node`.
    constructor
    · rintro ⟨w, g, hbr, hw, hmem⟩
      rcases hbr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · simp at hmem
      · revert hmem
        simp
        grind
    · rintro ⟨h1, h2, hl, hr⟩
      refine ⟨5, _, Or.inr ⟨rfl, rfl⟩, by norm_num, ?_⟩
      simp
      grind

theorem Tree.genWeightedBST_cost :
    IsBounded (Tree.genWeightedBST lo hi) (fun t => 3 * t.size + 1) := by
  open Lean.Order in
  delta genWeightedBST
  apply (fix_induct (motive := fun (g : Nat → Nat → SPMF.Cost (Tree Nat)) =>
    ∀ lo hi, IsBounded (g lo hi) (fun t => 3 * t.size + 1)) _ ?admissible ?step)
  case admissible =>
    exact admissible_pi_apply _ fun _ => admissible_pi_apply _ fun _ => admissible_IsBounded _
  case step =>
    intro rec ih lo hi
    simp [IsBounded_iff] at *
    intro t n hn
    grind [
      size,
      SPMF.Cost.mem_support_frequency,
      SPMF.Cost.mem_support_bind_iff,
      SPMF.Cost.mem_support_choose_iff,
      SPMF.Cost.mem_support_pure_iff
    ]

instance {lo hi : Nat} : LawfulGenerator (Tree.genWeightedBST lo hi) (Tree.isBST lo hi)
    (fun t => 3 * t.size + 1) where
  support_iff := Tree.genWeightedBST_support
  is_pmf := Tree.genWeightedBST_terminates
  is_bounded := Tree.genWeightedBST_cost

end weighted_termination

/- `genBST` can be run in `IO`. -/
#guard_msgs(drop info) in
#eval (for _ in [0:20] do
  IO.println <| repr (← Tree.genBST 0 10) : IO Unit)

/- `genBST` can be run in `PlausibleGen`. -/
#guard_msgs(drop info) in
#eval (for _ in [0:20] do
  IO.println <| repr (← Plausible.Gen.run (Tree.genBST (G := Plausible.Gen) 0 10) 10) : IO Unit)

/- `genWeightedBST` can be run in `IO` and indeed generates
    non-empty trees more frequently than leaves (by inspection) -/
#guard_msgs(drop info) in
#eval (for _ in [0:10] do
  IO.println <| repr (← Tree.genWeightedBST 0 10) : IO Unit)

end BST
