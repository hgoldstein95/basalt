/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt.SPMF.Support
import Basalt.ENNRealAuto

open Lean.Order RandomChoice NNReal ENNReal MeasureTheory

/-!
# SPMF Mass and Termination

`SPMF.mass` (the total probability assigned to values, as opposed to divergence — always ≤ 1) and
`SPMF.IsPMF` (mass exactly 1), together with the mass lower-bound lemmas that almost-sure
termination proofs chain through.
-/

namespace SPMF

section mass

/-- The total mass of an SPMF. Always ≤ 1 by definition. -/
noncomputable def mass (p : SPMF α) : ℝ≥0∞ := ∑' a, p a

theorem mass_le_one (p : SPMF α) : p.mass ≤ 1 := p.tsum_coe

theorem mass_eq_zero_of_support_empty {p : SPMF α} (h : p.support = ∅) : p.mass = 0 := by
  unfold mass
  rw [ENNReal.tsum_eq_zero]
  intro a
  rw [apply_eq_zero_iff]
  exact Set.eq_empty_iff_forall_notMem.mp h a

@[simp]
theorem mass_pick {x y : SPMF α} :
    (pick (fun () => x) (fun () => y)).mass = (1/2 : ℝ≥0∞) * x.mass + (1/2 : ℝ≥0∞) * y.mass := tsum_pick

@[simp]
theorem mass_bot : Bot.bot (α := SPMF α).mass = 0 := by
  simp only [mass, ENNReal.tsum_eq_zero]
  solve_by_elim

theorem mass_eq_zero_iff {x : SPMF α} : x.mass = 0 ↔ x = Bot.bot := by
  constructor
  · intro h
    ext a
    have : ∑' a, x a = 0 := h
    exact (ENNReal.tsum_eq_zero.mp this) a
  · intro h
    simp [h]

@[simp]
theorem mass_pure (a : α) : (Pure.pure a : SPMF α).mass = 1 := by
  unfold mass
  simp only [Pure.pure, pure, DFunLike.coe]
  rw [tsum_eq_single a]
  · simp
  · intro a' ha'
    simp [ha']

@[simp]
theorem mass_bind_tsum {x : SPMF α} {f : α → SPMF β} :
    (x >>= f).mass = ∑' a, x a * (f a).mass := by
  unfold SPMF.mass
  simp only [Bind.bind, SPMF.bind, DFunLike.coe]
  rw [ENNReal.tsum_comm]
  simp_rw [ENNReal.tsum_mul_left]

@[simp]
theorem mass_choose (lo hi : Nat) (h : lo ≤ hi) :
    (choose lo hi h : SPMF (ULift {x : Nat // lo ≤ x ∧ x ≤ hi})).mass = 1 := by
  unfold mass
  let n : ℕ := hi - lo + 1
  have hn : n ≠ 0 := Nat.add_one_ne_zero _
  calc ∑' a, (choose lo hi h : SPMF (ULift {x : Nat // lo ≤ x ∧ x ≤ hi})) a
    _ = ∑' (_ : ULift {x : Nat // lo ≤ x ∧ x ≤ hi}), (1 / (n : ℝ≥0∞)) := rfl
    _ = (Finset.Icc lo hi).card * (1 / (n : ℝ≥0∞)) := tsum_subtype_Icc_const lo hi _
    _ = (n : ℝ≥0∞) * (1 / (n : ℝ≥0∞)) := by rw [card_Icc_eq lo hi h]
    _ = 1 := ENNReal.mul_div_cancel (Nat.cast_ne_zero.mpr hn) (ENNReal.natCast_ne_top n)

@[simp]
theorem mass_bind_pure {x : SPMF α} {f : α → β} :
    (x >>= fun a => Pure.pure (f a)).mass = x.mass := by
  classical
  unfold mass
  simp only [Bind.bind, bind, Pure.pure, pure, DFunLike.coe]
  rw [ENNReal.tsum_comm]
  congr 1
  ext a
  rw [tsum_eq_single (f a)]
  · simp
  · intro b hb
    simp only [mul_ite, mul_one, mul_zero]
    split_ifs with heq
    · simp_all
    · rfl

@[simp]
theorem mass_map {x : SPMF α} {f : α → β} :
    (f <$> x).mass = x.mass := by
  rw [map_eq_pure_bind]
  exact mass_bind_pure

@[simp]
theorem mass_chooseNat (lo hi : Nat) (h : lo ≤ hi) :
    (chooseNat lo hi h : SPMF Nat).mass = 1 := by
  unfold chooseNat
  rw [mass_map]
  exact mass_choose lo hi h

@[simp]
theorem mass_chooseInt (lo hi : Int) (h : lo ≤ hi) :
    (chooseInt lo hi h : SPMF Int).mass = 1 := by
  unfold chooseInt
  rw [mass_bind_pure]
  exact mass_chooseNat _ _ _

theorem mass_bind_const {x : SPMF α} {y : SPMF β} :
    (x >>= fun _ => y).mass = x.mass * y.mass := by
  unfold mass
  simp only [Bind.bind, bind, DFunLike.coe]
  rw [ENNReal.tsum_comm]
  simp_rw [ENNReal.tsum_mul_left]
  rw [← ENNReal.tsum_mul_right]

theorem mass_bind_of_forall_mass_eq {x : SPMF α} {f : α → SPMF β} {c : ℝ≥0∞}
    (hf : ∀ a, (f a).mass = c) : (x >>= f).mass = x.mass * c := by
  unfold mass at *
  simp only [Bind.bind, bind, DFunLike.coe]
  rw [ENNReal.tsum_comm]
  calc ∑' a, ∑' b, x a * (f a) b
    _ = ∑' a, x a * (∑' b, (f a) b) := by simp_rw [ENNReal.tsum_mul_left]
    _ = ∑' a, x a * c := by simp_rw [hf]
    _ = (∑' a, x a) * c := by rw [ENNReal.tsum_mul_right]

theorem mass_bind_of_const_mass {x : SPMF α} {f : α → SPMF β} {c : ℝ≥0∞}
    (hx : x.mass = 1) (hf : ∀ a, (f a).mass = c) :
    (x >>= f).mass = c := by
  unfold mass at *
  simp only [Bind.bind, bind, DFunLike.coe]
  rw [ENNReal.tsum_comm]
  calc ∑' a, ∑' b, x a * (f a) b
    _ = ∑' a, x a * (∑' b, (f a) b) := by simp_rw [ENNReal.tsum_mul_left]
    _ = ∑' a, x a * c := by simp_rw [hf]
    _ = c * ∑' a, x a := by rw [ENNReal.tsum_mul_right]; ring
    _ = c * 1 := by rw [hx]
    _ = c := by ring

theorem mass_bind {x : SPMF α} {f : α → SPMF β} (hf : ∀ a, (f a).mass = 1) :
    (x >>= f).mass = x.mass := by
  unfold mass at *
  simp only [Bind.bind, bind, DFunLike.coe]
  rw [ENNReal.tsum_comm]
  simp_rw [ENNReal.tsum_mul_left]
  calc ∑' a, x a * ∑' b, (f a) b
    _ = ∑' a, x a * 1 := by simp_rw [hf]
    _ = ∑' a, x a := by simp

theorem mass_bind_ge_mul {x : SPMF α} {f : α → SPMF β} {c d : ℝ≥0∞}
    (hx : x.mass ≥ c) (hf : ∀ a, (f a).mass ≥ d) : (x >>= f).mass ≥ c * d := by
  have h : (x >>= f).mass ≥ x.mass * d := by
    simp only [mass, Bind.bind, bind, DFunLike.coe]
    rw [ENNReal.tsum_comm]
    simp [ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_right]
    gcongr with a; exact hf a
  calc (x >>= f).mass ≥ x.mass * d := h
    _ ≥ c * d := by gcongr

theorem mass_bind_ge_of_isPMF {x : SPMF α} (hx : x.mass = 1)
    {f : α → SPMF β} {c : ℝ≥0∞}
    (hf : ∀ a, (f a).mass ≥ c) : (x >>= f).mass ≥ c := by
  have := mass_bind_ge_mul (c := 1) (d := c) hx.symm.le hf
  simpa using this

theorem mass_ge_iInf {ι : Type*} (g : ι → SPMF α) (i : ι) :
    (g i).mass ≥ ⨅ j, (g j).mass :=
  iInf_le (fun j => (g j).mass) i

/-- Lower-bound the mass of a generator that draws a pivot with `choose` and continues: the mass is
at least the *average* over the range of a per-pivot lower bound. -/
theorem mass_bind_choose_ge {lo hi : Nat} (h : lo ≤ hi)
    {f : ULift {x : Nat // lo ≤ x ∧ x ≤ hi} → SPMF α} {m : Nat → ℝ≥0∞}
    (hf : ∀ a, (f a).mass ≥ m a.down.val) :
    (choose lo hi h >>= f).mass
      ≥ (∑ x ∈ Finset.Icc lo hi, m x) / ((hi - lo + 1 : ℕ) : ℝ≥0∞) := by
  rw [mass_bind_tsum]
  calc ∑' a, (choose lo hi h : SPMF _) a * (f a).mass
      ≥ ∑' (a : ULift {x : Nat // lo ≤ x ∧ x ≤ hi}),
          (1 / ((hi - lo + 1 : ℕ) : ℝ≥0∞)) * m a.down.val := by
        refine ENNReal.tsum_le_tsum fun a => ?_
        rw [choose_apply lo hi h a]
        exact mul_le_mul' le_rfl (hf a)
    _ = (1 / ((hi - lo + 1 : ℕ) : ℝ≥0∞)) *
          ∑' (a : ULift {x : Nat // lo ≤ x ∧ x ≤ hi}), m a.down.val := ENNReal.tsum_mul_left
    _ = (1 / ((hi - lo + 1 : ℕ) : ℝ≥0∞)) * ∑ x ∈ Finset.Icc lo hi, m x := by
        rw [tsum_subtype_Icc]
    _ = (∑ x ∈ Finset.Icc lo hi, m x) / ((hi - lo + 1 : ℕ) : ℝ≥0∞) := by
        rw [one_div, mul_comm, div_eq_mul_inv]

/-- `chooseNat` form of `mass_bind_choose_ge`. -/
theorem mass_bind_chooseNat_ge {lo hi : Nat} (h : lo ≤ hi)
    {f : Nat → SPMF α} {m : Nat → ℝ≥0∞}
    (hf : ∀ x, lo ≤ x → x ≤ hi → (f x).mass ≥ m x) :
    (chooseNat lo hi h >>= f).mass
      ≥ (∑ x ∈ Finset.Icc lo hi, m x) / ((hi - lo + 1 : ℕ) : ℝ≥0∞) := by
  unfold chooseNat
  rw [bind_map_left]
  exact mass_bind_choose_ge h fun a => hf a.down.val a.down.property.1 a.down.property.2

/-- `chooseInt` form of `mass_bind_choose_ge`. The average is over the `Int` interval; the shift by
`lo` that defines `chooseInt` is undone by reindexing the sum. -/
theorem mass_bind_chooseInt_ge {lo hi : Int} (h : lo ≤ hi)
    {f : Int → SPMF α} {m : Int → ℝ≥0∞}
    (hf : ∀ x, lo ≤ x → x ≤ hi → (f x).mass ≥ m x) :
    (chooseInt lo hi h >>= f).mass
      ≥ (∑ x ∈ Finset.Icc lo hi, m x) / (((hi - lo + 1).toNat : ℕ) : ℝ≥0∞) := by
  have hreindex : ∑ k ∈ Finset.Icc 0 (hi - lo).toNat, m (lo + (k : Int))
      = ∑ x ∈ Finset.Icc lo hi, m x := by
    refine Finset.sum_nbij' (fun k => lo + (k : Int)) (fun x => (x - lo).toNat)
      (fun k hk => ?_) (fun x hx => ?_) (fun k hk => ?_) (fun x hx => ?_) (fun k hk => rfl)
    · simp only [Finset.mem_Icc] at hk ⊢; omega
    · simp only [Finset.mem_Icc] at hx ⊢; omega
    · simp only [Finset.mem_Icc] at hk; omega
    · simp only [Finset.mem_Icc] at hx; omega
  have hcard : ((hi - lo).toNat - 0 + 1 : ℕ) = ((hi - lo + 1).toNat : ℕ) := by omega
  unfold chooseInt
  simp only [LawfulMonad.bind_assoc, LawfulMonad.pure_bind]
  refine le_of_eq_of_le ?_
    (mass_bind_chooseNat_ge (Nat.zero_le _) fun k _ _ => hf _ (by omega) (by omega))
  rw [hreindex, hcard]

/-- A `tsum` over `α` commutes with a weighted `List.sum`. -/
private theorem tsum_map_weighted (gs : List (Nat × (Unit → SPMF α))) :
    ∑' a, (gs.map fun p => (p.1 : ℝ≥0∞) * (p.2 ()) a).sum
      = (gs.map fun p => (p.1 : ℝ≥0∞) * (p.2 ()).mass).sum := by
  induction gs with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, ih]
    rfl

/-- The mass of a weighted choice is the weighted average of the branch masses. -/
@[simp]
theorem mass_frequency
    {gs : List (Nat × (Unit → SPMF α))} (h : 0 < (gs.map Prod.fst).sum) :
    (frequency gs h : SPMF α).mass
      = (gs.map fun p => (p.1 : ℝ≥0∞) * (p.2 ()).mass).sum / ((gs.map Prod.fst).sum : ℝ≥0∞) := by
  have hm : (frequency gs h : SPMF α).mass = ∑' a, frequency gs h a := rfl
  rw [hm]
  simp only [frequency_apply, div_eq_mul_inv]
  rw [ENNReal.tsum_mul_right, tsum_map_weighted]

/-- Lower-bound form of `mass_frequency`, for termination proofs: inside a `partial_fixpoint` one
only ever has a *lower bound* on a recursive branch's mass, never an equality. -/
theorem mass_frequency_ge {gs : List (Nat × (Unit → SPMF α))}
    (h : 0 < (gs.map Prod.fst).sum)
    {f : (Nat × (Unit → SPMF α)) → ℝ≥0∞}
    (hgs : ∀ p ∈ gs, (p.2 ()).mass ≥ f p) :
    (frequency gs h : SPMF α).mass
      ≥ (gs.map fun p => (p.1 : ℝ≥0∞) * f p).sum / ((gs.map Prod.fst).sum : ℝ≥0∞) := by
  rw [mass_frequency h]
  refine ENNReal.div_le_div_right ?_ _
  refine List.sum_le_sum fun p hp => ?_
  gcongr
  exact hgs p hp

end mass

section is_pmf

/-- An SPMF is a PMF if the mass sums to exactly 1.

This means that the probability of non-termination is vanishingly small, and therefore that the
generator almost-surely terminates. -/
def IsPMF (p : SPMF α) : Prop := p.mass = 1

theorem IsPMF_pick {x y : SPMF α} (hx : IsPMF x) (hy : IsPMF y) : IsPMF (pick (fun () => x) (fun () => y)) := by
  unfold IsPMF mass at *
  rw [tsum_pick, hx, hy]
  simp only [mul_one]
  exact ENNReal.add_halves 1

theorem IsPMF_pure (a : α) : IsPMF (Pure.pure a : SPMF α) := mass_pure a

theorem IsPMF_choose (lo hi : Nat) (h : lo ≤ hi) :
    IsPMF (choose lo hi h : SPMF (ULift {x : Nat // lo ≤ x ∧ x ≤ hi})) :=
  mass_choose lo hi h

theorem IsPMF_chooseNat (lo hi : Nat) (h : lo ≤ hi) :
    IsPMF (chooseNat lo hi h : SPMF Nat) :=
  mass_chooseNat lo hi h

theorem IsPMF_chooseInt (lo hi : Int) (h : lo ≤ hi) :
    IsPMF (chooseInt lo hi h : SPMF Int) :=
  mass_chooseInt lo hi h

theorem IsPMF_bind_pure {x : SPMF α} {f : α → β} (hx : IsPMF x) :
    IsPMF (x >>= fun a => Pure.pure (f a)) := by
  unfold IsPMF
  rw [mass_bind_pure, hx]

theorem IsPMF_bind {x : SPMF α} {f : α → SPMF β} (hx : IsPMF x) (hf : ∀ a, IsPMF (f a)) :
    IsPMF (x >>= f) := by
  unfold IsPMF
  rw [mass_bind hf, hx]

theorem IsPMF_coin {r : Rat} : IsPMF (RandomChoice.coin r) := by
  unfold coin
  apply IsPMF_bind
  . apply IsPMF_choose
  . intro ⟨x, ⟨_, hle⟩⟩
    dsimp
    split_ifs <;> apply IsPMF_pure

theorem IsPMF_map {x : SPMF α} {f : α → β} (hx : IsPMF x) :
    IsPMF (f <$> x) := by
  unfold IsPMF
  rw [mass_map]
  assumption

theorem IsPMF_bind_of_support {x : SPMF α} {f : α → SPMF β}
    (hx : IsPMF x) (hf : ∀ a ∈ x.support, IsPMF (f a)) :
    IsPMF (x >>= f) := by
  unfold IsPMF mass at *
  simp only [Bind.bind, bind, DFunLike.coe]
  rw [ENNReal.tsum_comm]
  calc ∑' a, ∑' b, x a * f a b
    _ = ∑' a, x a * (∑' b, f a b) := by
      simp_rw [ENNReal.tsum_mul_left]
    _ = ∑' a, x a * 1 := by
        apply tsum_congr
        intro a
        by_cases ha : a ∈ x.support
        · rw [hf a ha]
        · have h_zero_mass : x a = 0 := by
            apply (apply_eq_zero_iff x a).mpr
            assumption
          simp [h_zero_mass]
    _ = ∑' a, x a := by simp
    _ = 1 := by assumption

theorem IsPMF_elements [Inhabited α] (xs : List α) (hne : xs ≠ []) :
    IsPMF (elements xs hne) := by
  simp only [elements]
  apply IsPMF_bind
  apply IsPMF_map
  apply IsPMF_choose
  intro ⟨ i, ⟨ hge, hle ⟩⟩
  apply IsPMF_pure

theorem IsPMF_biasedOptionGen {r : Rat} (hg : IsPMF g) :
    IsPMF (biasedOptionGen r g) := by
  unfold biasedOptionGen
  apply IsPMF_bind
  . apply IsPMF_coin
  . intro b
    cases b <;> dsimp
    . apply IsPMF_pure
    . apply IsPMF_bind_pure
      assumption

theorem IsPMF_optionGen (hg : IsPMF g) : IsPMF (optionGen g) := by
  unfold optionGen
  apply IsPMF_biasedOptionGen
  assumption

theorem IsPMF_oneOf {gs : List (Unit → SPMF α)} (hne : gs ≠ []) (hgs : ∀ g ∈ gs, IsPMF (g ())) :
    IsPMF (oneOf gs hne) := by
  unfold oneOf Helpers.oneOfAux
  apply IsPMF_bind_of_support
  . apply IsPMF_map
    apply IsPMF_choose
  . intro ⟨ i, hge, hle ⟩ helem
    simp at helem
    have h_lt : i < gs.length := by
      rw [Nat.lt_iff_add_one_le]
      refine Nat.add_le_of_le_sub ?_ hle
      apply Nat.one_le_iff_ne_zero.mpr
      apply Nat.ne_zero_iff_zero_lt.mpr
      apply List.length_pos_iff.mpr
      assumption
    dsimp
    apply hgs
    apply List.getElem_mem

private theorem sum_weights_of_IsPMF {gs : List (Nat × (Unit → SPMF α))}
    (hgs : ∀ p ∈ gs, 0 < p.1 → IsPMF (p.2 ())) :
    (gs.map fun p => (p.1 : ℝ≥0∞) * (p.2 ()).mass).sum = ((gs.map Prod.fst).sum : ℝ≥0∞) := by
  induction gs with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.map_cons, List.sum_cons, Nat.cast_add]
    rw [ih (fun p hp => hgs p (List.mem_cons_of_mem _ hp))]
    congr 1
    rcases Nat.eq_zero_or_pos hd.1 with hz | hpos
    · simp [hz]
    · have hm : (hd.2 ()).mass = 1 := hgs hd List.mem_cons_self hpos
      rw [hm, mul_one]

theorem IsPMF_frequency {gs : List (Nat × (Unit → SPMF α))}
    (h : 0 < (gs.map Prod.fst).sum)
    (hgs : ∀ p ∈ gs, 0 < p.1 → IsPMF (p.2 ())) :
    IsPMF (frequency gs h) := by
  unfold IsPMF
  rw [mass_frequency h, sum_weights_of_IsPMF hgs]
  exact ENNReal.div_self (Nat.cast_ne_zero.mpr h.ne') (ENNReal.natCast_ne_top _)

theorem IsPMF_vectorOf {g : SPMF α} (hg : IsPMF g) :
    IsPMF (vectorOf n g) := by
  induction n with
  | zero =>
    simp [vectorOf]
    apply IsPMF_pure
  | succ n IH =>
    rw [vectorOf_succ]
    apply IsPMF_bind
    . assumption
    . intro x
      apply IsPMF_bind
      . assumption
      . intro xs
        apply IsPMF_pure

theorem IsPMF_listOfMaxLength {g : SPMF α} (hg : IsPMF g) :
    IsPMF (listOfMaxLength n g) := by
  unfold listOfMaxLength
  apply IsPMF_bind
  . apply IsPMF_map
    apply IsPMF_choose
  . intro ⟨x, hge, hle⟩
    dsimp
    apply IsPMF_vectorOf
    assumption

/-- A general fixpoint principle for proving almost-sure termination.

If the mass of each generator satisfies `mass ≥ F(inf mass)` and `F` is such that
`c ≤ 1 ∧ c ≥ F c → c = 1`, then all generators are PMFs. -/
theorem IsPMF_of_mass_fixpoint {ι : Type*} {α : Type*} [Nonempty ι]
    (g : ι → SPMF α) (F : ℝ≥0∞ → ℝ≥0∞)
    (hF : ∀ c : ℝ≥0∞, c ≤ 1 → c ≥ F c → c = 1)
    (h_step : ∀ i, (⨅ j, (g j).mass) ≤ 1 → (g i).mass ≥ F (⨅ j, (g j).mass)) :
    ∀ i, IsPMF (g i) := by
  intro i
  unfold IsPMF
  apply le_antisymm (g i).tsum_coe
  have hc_le : (⨅ j, (g j).mass) ≤ 1 := (iInf_le _ i).trans (g i).tsum_coe
  have hc_ge_F : (⨅ j, (g j).mass) ≥ F (⨅ j, (g j).mass) := le_iInf (fun j => h_step j hc_le)
  calc (1 : ℝ≥0∞) = ⨅ j, (g j).mass := (hF _ hc_le hc_ge_F).symm
    _ ≤ (g i).mass := iInf_le _ i

end is_pmf

end SPMF
