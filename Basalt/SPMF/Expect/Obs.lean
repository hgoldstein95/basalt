/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt.Obs.Combinators
import Basalt.Obs.Spec
import Basalt.SPMF.Expect.Basic

open RandomChoice NNReal ENNReal

/-!
# The Expectation Observation

`expect` as an observation into `WP ℝ≥0∞`, how the average presents for each shape of choice, and
the expectation equation of each combinator, which is its `Obs.map_*` lemma read through one of
those presentations.
-/

/-- In `ℝ≥0∞` a uniform choice is the average, written as `SPMF`'s `choose` computes it so that
`expectObs` preserves `choose` by `rfl`. -/
noncomputable def Mix.average : Mix.{u} ℝ≥0∞ where
  mix lo hi F := ∑' a, (1 / ((hi - lo + 1 : ℕ) : ℝ≥0∞)) * F a

namespace Mix

/-! ## Presentations of the average, one per shape of choice -/

theorem range_average (lo hi : Nat) (m : Nat → ℝ≥0∞) :
    Mix.average.mix lo hi (fun a : ULift.{u} {x : Nat // lo ≤ x ∧ x ≤ hi} => m a.down.val)
      = (∑ x ∈ Finset.Icc lo hi, m x) / ((hi - lo + 1 : ℕ) : ℝ≥0∞) := by
  show ∑' a : ULift.{u} {x : Nat // lo ≤ x ∧ x ≤ hi}, _ * m a.down.val = _
  rw [ENNReal.tsum_mul_left, one_div, mul_comm, div_eq_mul_inv]
  exact congrArg (· * _) (SPMF.tsum_subtype_Icc lo hi m)

theorem binary_average (F : ULift.{u} {x : Nat // 0 ≤ x ∧ x ≤ 1} → ℝ≥0∞) :
    Mix.average.mix 0 1 F = (1/2 : ℝ≥0∞) * F ⟨⟨0, by omega⟩⟩ + (1/2 : ℝ≥0∞) * F ⟨⟨1, by omega⟩⟩ := by
  have hF : F = fun a => (fun n : Nat => if n = 0 then F ⟨⟨0, by omega⟩⟩ else F ⟨⟨1, by omega⟩⟩)
      a.down.val := by
    funext ⟨⟨n, h0, h1⟩⟩
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h1 with rfl | rfl <;> simp
  refine (congrArg (Mix.average.mix 0 1) hF).trans ((range_average 0 1 fun n : Nat =>
    if n = 0 then F ⟨⟨0, by omega⟩⟩ else F ⟨⟨1, by omega⟩⟩).trans ?_)
  have hIcc : Finset.Icc 0 1 = ({0, 1} : Finset ℕ) := by decide
  rw [hIcc, Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [if_pos, Nat.one_ne_zero, if_false]
  norm_num
  rw [ENNReal.add_div]
  congr 1 <;> rw [ENNReal.div_eq_inv_mul]

private theorem sum_ite_lt {d : Nat} {k : ℤ} (hd : 0 < d) (h0 : 0 ≤ k) (hk : k ≤ d)
    (t e : ℝ≥0∞) :
    ∑ n ∈ Finset.Icc 0 (d - 1), (if (n : ℤ) < k then t else e)
      = (k.toNat : ℝ≥0∞) * t + ((d - k.toNat : ℕ) : ℝ≥0∞) * e := by
  have hkd : k.toNat ≤ d := by omega
  have hIcc : Finset.Icc 0 (d - 1) = Finset.range d := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_range]
    omega
  rw [hIcc, Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (Nat.zero_le k.toNat) hkd]
  have hfirst : ∑ n ∈ Finset.Ico 0 k.toNat, (if (n : ℤ) < k then t else e)
      = (k.toNat : ℝ≥0∞) * t := by
    have hall : ∀ n ∈ Finset.Ico 0 k.toNat, (if (n : ℤ) < k then t else e) = t := by
      intro n hn
      have := (Finset.mem_Ico.mp hn).2
      rw [if_pos (by omega)]
    rw [Finset.sum_congr rfl hall, Finset.sum_const, Nat.card_Ico, Nat.sub_zero, nsmul_eq_mul]
  have hsecond : ∑ n ∈ Finset.Ico k.toNat d, (if (n : ℤ) < k then t else e)
      = ((d - k.toNat : ℕ) : ℝ≥0∞) * e := by
    have hall : ∀ n ∈ Finset.Ico k.toNat d, (if (n : ℤ) < k then t else e) = e := by
      intro n hn
      have := (Finset.mem_Ico.mp hn).1
      rw [if_neg (by omega)]
    rw [Finset.sum_congr rfl hall, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
  rw [hfirst, hsecond]

theorem threshold_average {d : Nat} {k : ℤ} (hd : 0 < d) (h0 : 0 ≤ k) (hk : k ≤ d)
    (t e : ℝ≥0∞) :
    Mix.average.mix 0 (d - 1)
        (fun a : ULift.{u} {x : Nat // 0 ≤ x ∧ x ≤ d - 1} => if (a.down.val : ℤ) < k then t else e)
      = (k.toNat : ℝ≥0∞) / (d : ℝ≥0∞) * t + ((d - k.toNat : ℕ) : ℝ≥0∞) / (d : ℝ≥0∞) * e := by
  rw [range_average 0 (d - 1) fun n => if (n : ℤ) < k then t else e, sum_ite_lt hd h0 hk]
  have hd' : d - 1 - 0 + 1 = d := by omega
  rw [hd', ENNReal.add_div]
  congr 1 <;> rw [div_eq_mul_inv, div_eq_mul_inv, mul_right_comm]

private theorem sum_range_getD (l : List ℝ≥0∞) :
    ∑ n ∈ Finset.range l.length, l.getD n 0 = l.sum := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    rw [List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, ih, List.sum_cons]
    exact add_comm _ _

theorem index_average {γ : Type v} (l : List γ) (hne : l ≠ []) (F : γ → ℝ≥0∞) :
    Mix.average.mix 0 (l.length - 1)
        (fun a : ULift.{u} {x : Nat // 0 ≤ x ∧ x ≤ l.length - 1} =>
          F (l[a.down.val]'(Obs.idx_lt hne a.down.property)))
      = (l.map F).sum / (l.length : ℝ≥0∞) := by
  have hlen := List.length_pos_iff.mpr hne
  have hF : (fun a : ULift.{u} {x : Nat // 0 ≤ x ∧ x ≤ l.length - 1} =>
        F (l[a.down.val]'(Obs.idx_lt hne a.down.property)))
      = fun a => (fun n : Nat => (l.map F).getD n 0) a.down.val := by
    funext ⟨⟨i, _, hi⟩⟩
    have hi' : i < l.length := by omega
    simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi']
  refine (congrArg (Mix.average.mix 0 (l.length - 1)) hF).trans ((range_average 0 _ fun n : Nat => (l.map F).getD n 0).trans ?_)
  have hIcc : Finset.Icc 0 (l.length - 1) = Finset.range (l.map F).length := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_range, List.length_map]
    omega
  have hT : l.length - 1 - 0 + 1 = l.length := by omega
  rw [hIcc, hT, sum_range_getD]

/-- Summing `selectD` over every offset counts each entry `(w, x)` exactly `w` times. -/
private theorem sum_selectD (l : List (Nat × ℝ≥0∞)) (d : ℝ≥0∞) :
    ∑ n ∈ Finset.range ((l.map Prod.fst).sum), Obs.selectD l n d
      = (l.map fun p => (p.1 : ℝ≥0∞) * p.2).sum := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    obtain ⟨k, x⟩ := hd
    simp only [List.map_cons, List.sum_cons, Obs.selectD]
    rw [Finset.range_eq_Ico,
      ← Finset.sum_Ico_consecutive _ (Nat.zero_le k) (Nat.le_add_right k _)]
    congr 1
    · rw [Finset.sum_congr rfl (fun n hn => if_pos (Finset.mem_Ico.mp hn).2),
        Finset.sum_const, Nat.card_Ico, Nat.sub_zero, nsmul_eq_mul]
    · rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left, ← ih]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [if_neg (by omega), Nat.add_sub_cancel_left]

theorem select_average (l : List (Nat × ℝ≥0∞)) {T : Nat} (hT : T = (l.map Prod.fst).sum)
    (hpos : 0 < T) (d : ℝ≥0∞) :
    Mix.average.mix 0 (T - 1)
        (fun a : ULift.{u} {x : Nat // 0 ≤ x ∧ x ≤ T - 1} => Obs.selectD l a.down.val d)
      = (l.map fun p => (p.1 : ℝ≥0∞) * p.2).sum / ((T : ℕ) : ℝ≥0∞) := by
  rw [range_average 0 (T - 1) fun n => Obs.selectD l n d]
  have hIcc : Finset.Icc 0 (T - 1) = Finset.range T := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_range]
    omega
  have hT' : T - 1 - 0 + 1 = T := by omega
  rw [hIcc, hT', hT, sum_selectD]

end Mix

namespace SPMF

/-- The expectation observation. -/
noncomputable def expectObs : Obs SPMF.{u} (WP Mix.average) where
  spec g := fun f => expect g f
  map_pure a := by funext f; exact expect_pure a f
  map_bind x k := by funext f; exact expect_bind x k f
  map_choose _ _ _ := rfl

section expect

/-- Expectation over a uniform `choose` is the average over the range. The summand is taken in
`Nat` form `m` (with `hm` bridging) so callers avoid `choose`'s `ULift` subtype. -/
theorem expect_choose {lo hi : Nat} (h : lo ≤ hi)
    (f : ULift.{u} {x : Nat // lo ≤ x ∧ x ≤ hi} → ℝ≥0∞) (m : Nat → ℝ≥0∞)
    (hm : ∀ a, f a = m a.down.val) :
    expect (choose lo hi h : SPMF _) f
      = (∑ x ∈ Finset.Icc lo hi, m x) / ((hi - lo + 1 : ℕ) : ℝ≥0∞) := by
  obtain rfl : f = fun a => m a.down.val := funext hm
  exact Mix.range_average lo hi m

theorem expect_pick (x y : SPMF α) (f : α → ℝ≥0∞) :
    expect (pick (fun () => x) (fun () => y)) f
      = (1/2 : ℝ≥0∞) * expect x f + (1/2 : ℝ≥0∞) * expect y f :=
  (congrFun (expectObs.map_pick (fun () => x) (fun () => y)) f).trans (Mix.binary_average _)

theorem expect_chooseNat {lo hi : Nat} (h : lo ≤ hi) (f : Nat → ℝ≥0∞) :
    expect (chooseNat lo hi h) f
      = (∑ x ∈ Finset.Icc lo hi, f x) / ((hi - lo + 1 : ℕ) : ℝ≥0∞) :=
  (congrFun (expectObs.map_chooseNat lo hi h) f).trans (Mix.range_average lo hi f)

/-- Expectation through a uniform `chooseNat` pivot is the average of the per-pivot
expectations. -/
theorem expect_bind_chooseNat {lo hi : Nat} (h : lo ≤ hi)
    {g : Nat → SPMF α} (f : α → ℝ≥0∞) :
    expect (chooseNat lo hi h >>= g) f
      = (∑ x ∈ Finset.Icc lo hi, expect (g x) f) / ((hi - lo + 1 : ℕ) : ℝ≥0∞) := by
  rw [expect_bind, expect_chooseNat]

theorem expect_chooseInt {lo hi : Int} (h : lo ≤ hi) (f : Int → ℝ≥0∞) :
    expect (chooseInt lo hi h) f
      = (∑ x ∈ Finset.Icc lo hi, f x) / (((hi - lo + 1).toNat : ℕ) : ℝ≥0∞) := by
  have hreindex : ∑ k ∈ Finset.Icc 0 (hi - lo).toNat, f (lo + (k : Int))
      = ∑ x ∈ Finset.Icc lo hi, f x := by
    refine Finset.sum_nbij' (fun k => lo + (k : Int)) (fun x => (x - lo).toNat)
      (fun k hk => ?_) (fun x hx => ?_) (fun k hk => ?_) (fun x hx => ?_) (fun k hk => rfl)
    · simp only [Finset.mem_Icc] at hk ⊢; omega
    · simp only [Finset.mem_Icc] at hx ⊢; omega
    · simp only [Finset.mem_Icc] at hk; omega
    · simp only [Finset.mem_Icc] at hx; omega
  have hcard : ((hi - lo).toNat - 0 + 1 : ℕ) = ((hi - lo + 1).toNat : ℕ) := by omega
  refine (congrFun (expectObs.map_chooseInt lo hi h) f).trans ?_
  rw [← hreindex, ← hcard]
  exact Mix.range_average 0 (hi - lo).toNat fun k => f (lo + (k : Int))

/-- `chooseInt` form of `expect_bind_chooseNat`. -/
theorem expect_bind_chooseInt {lo hi : Int} (h : lo ≤ hi)
    {g : Int → SPMF α} (f : α → ℝ≥0∞) :
    expect (chooseInt lo hi h >>= g) f
      = (∑ x ∈ Finset.Icc lo hi, expect (g x) f) / (((hi - lo + 1).toNat : ℕ) : ℝ≥0∞) := by
  rw [expect_bind, expect_chooseInt]

/-- The expectation over a uniform element is the average. -/
theorem expect_elements {xs : List α} (hne : xs ≠ []) (f : α → ℝ≥0∞) :
    expect (elements xs hne) f = (xs.map f).sum / (xs.length : ℝ≥0∞) :=
  (congrFun (expectObs.map_elements xs hne) f).trans (Mix.index_average xs hne f)

/-- The expectation over a uniform choice is the average of the branch expectations. -/
theorem expect_oneOf {gs : List (Unit → SPMF α)} (hne : gs ≠ []) (f : α → ℝ≥0∞) :
    expect (oneOf gs hne) f = (gs.map fun g => expect (g ()) f).sum / (gs.length : ℝ≥0∞) :=
  (congrFun (expectObs.map_oneOf gs hne) f).trans
    (Mix.index_average gs hne fun g => expect (g ()) f)

/-- The expectation over a weighted choice is the weighted average of the branch expectations. -/
theorem expect_frequency {gs : List (Nat × (Unit → SPMF α))}
    (h : 0 < (gs.map Prod.fst).sum) (f : α → ℝ≥0∞) :
    expect (frequency gs h) f
      = (gs.map fun p => (p.1 : ℝ≥0∞) * expect (p.2 ()) f).sum
          / (((gs.map Prod.fst).sum : ℕ) : ℝ≥0∞) := by
  refine (congrFun (expectObs.map_frequency gs h) f).trans ?_
  simp only [Obs.select, WP.choose_bind_apply, Obs.selectD_map (fun w : WP Mix.average α => w f), List.map_map]
  refine (Mix.select_average _ ?_ h _).trans ?_
  · simp [Function.comp_def]
  · simp [Function.comp_def, expectObs]

end expect

section apply

/-- Branch `j` of `oneOf` fires with probability `1 / gs.length`. -/
@[simp]
theorem oneOf_apply
    (gs : List (Unit → SPMF α)) (h : gs ≠ []) (a : α) :
    oneOf gs h a
      = (gs.map fun p => (p ()) a).sum / (gs.length : ℝ≥0∞) := by
  simp only [← prob_singleton]
  exact expect_oneOf h _

/-- Branch `j` of `frequency` fires with probability `wⱼ / Σᵢ wᵢ`. -/
@[simp]
theorem frequency_apply
    (gs : List (Nat × (Unit → SPMF α))) (h : 0 < (gs.map Prod.fst).sum) (a : α) :
    frequency gs h a
      = (gs.map fun p => (p.1 : ℝ≥0∞) * (p.2 ()) a).sum / ((gs.map Prod.fst).sum : ℝ≥0∞) := by
  simp only [← prob_singleton]
  exact expect_frequency h _

end apply

section prob

theorem prob_pick (x y : SPMF α) (E : Set α) :
    prob (pick (fun () => x) (fun () => y)) E
      = (1/2 : ℝ≥0∞) * prob x E + (1/2 : ℝ≥0∞) * prob y E := by
  unfold prob
  rw [expect_pick]

theorem prob_frequency {gs : List (Nat × (Unit → SPMF α))}
    (h : 0 < (gs.map Prod.fst).sum) (E : Set α) :
    prob (frequency gs h) E
      = (gs.map fun p => (p.1 : ℝ≥0∞) * prob (p.2 ()) E).sum
          / (((gs.map Prod.fst).sum : ℕ) : ℝ≥0∞) := by
  unfold prob
  exact expect_frequency h _

end prob

section coin

theorem coin_num_bounds {r : Rat} (h0 : 0 ≤ r) (h1 : r ≤ 1) : 0 ≤ r.num ∧ r.num ≤ (r.den : ℤ) := by
  refine ⟨Rat.num_nonneg.mpr h0, ?_⟩
  rcases lt_or_eq_of_le h1 with h | h
  · exact (Rat.num_lt_denom_iff.mpr h).le
  · subst h
    norm_num

/-- The coin lands `true` with probability `r.num / r.den` and `false` with the rest. -/
theorem expect_coin {r : Rat} (h0 : 0 ≤ r) (h1 : r ≤ 1) (f : Bool → ℝ≥0∞) :
    expect (coin r : SPMF Bool) f
      = (r.num.toNat : ℝ≥0∞) / (r.den : ℝ≥0∞) * f true
        + ((r.den - r.num.toNat : ℕ) : ℝ≥0∞) / (r.den : ℝ≥0∞) * f false := by
  obtain ⟨hnum, hle⟩ := coin_num_bounds h0 h1
  refine (congrFun (expectObs.map_coin r) f).trans ?_
  simp only [coin, WP.choose_bind_apply, WP.ite_apply]
  exact Mix.threshold_average r.den_pos hnum hle (f true) (f false)

theorem coin_apply_true {r : Rat} (h0 : 0 ≤ r) (h1 : r ≤ 1) :
    (coin r : SPMF Bool) true = (r.num.toNat : ℝ≥0∞) / (r.den : ℝ≥0∞) := by
  rw [← prob_singleton]
  unfold prob
  rw [expect_coin h0 h1]
  simp [Set.indicator]

theorem coin_apply_false {r : Rat} (h0 : 0 ≤ r) (h1 : r ≤ 1) :
    (coin r : SPMF Bool) false = ((r.den - r.num.toNat : ℕ) : ℝ≥0∞) / (r.den : ℝ≥0∞) := by
  rw [← prob_singleton]
  unfold prob
  rw [expect_coin h0 h1]
  simp [Set.indicator]

end coin

end SPMF
