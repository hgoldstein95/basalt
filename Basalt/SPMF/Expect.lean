/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt.SPMF.Termination

open RandomChoice NNReal ENNReal

/-!
# Expected Values and Event Probabilities

`SPMF.expect` (the expected value of an `ℝ≥0∞`-valued function under a generator) and `SPMF.prob`
(the probability of an event), with a compositional algebra mirroring the `mass_*` family.
-/

namespace SPMF

section expect

/-- The expected value of `f` under `p`. `mass` is the special case `f = 1`. -/
noncomputable def expect (p : SPMF α) (f : α → ℝ≥0∞) : ℝ≥0∞ := ∑' a, p a * f a

@[simp]
theorem expect_pure (a : α) (f : α → ℝ≥0∞) :
    expect (Pure.pure a : SPMF α) f = f a := by
  unfold expect
  rw [tsum_eq_single a]
  · simp
  · intro a' ha'
    simp [ha']

/-- The tower rule. -/
theorem expect_bind (x : SPMF α) (g : α → SPMF β) (f : β → ℝ≥0∞) :
    expect (x >>= g) f = expect x (fun a => expect (g a) f) := by
  unfold expect
  simp only [bind_apply]
  calc ∑' b, (∑' a, x a * g a b) * f b
      = ∑' b, ∑' a, x a * (g a b * f b) := by
        congr 1; ext b
        rw [← ENNReal.tsum_mul_right]
        congr 1; ext a
        rw [mul_assoc]
    _ = ∑' a, ∑' b, x a * (g a b * f b) := ENNReal.tsum_comm
    _ = ∑' a, x a * ∑' b, g a b * f b := by
        congr 1; ext a
        rw [ENNReal.tsum_mul_left]

theorem expect_map (x : SPMF α) (h : α → β) (f : β → ℝ≥0∞) :
    expect (h <$> x) f = expect x (f ∘ h) := by
  rw [← LawfulMonad.bind_pure_comp, expect_bind]
  simp only [expect_pure]
  rfl

@[simp]
theorem expect_one (p : SPMF α) : expect p (fun _ => 1) = p.mass := by
  unfold expect mass; simp

theorem expect_const (p : SPMF α) (c : ℝ≥0∞) :
    expect p (fun _ => c) = p.mass * c := by
  unfold expect mass
  rw [← ENNReal.tsum_mul_right]

theorem expect_mono {p : SPMF α} {f g : α → ℝ≥0∞} (h : ∀ a, f a ≤ g a) :
    expect p f ≤ expect p g :=
  ENNReal.tsum_le_tsum fun a => by gcongr; exact h a

theorem expect_mono_support {p : SPMF α} {f g : α → ℝ≥0∞}
    (h : ∀ a ∈ p.support, f a ≤ g a) : expect p f ≤ expect p g := by
  unfold expect
  refine ENNReal.tsum_le_tsum fun a => ?_
  by_cases ha : a ∈ p.support
  · exact mul_le_mul_right (h a ha) _
  · rw [(apply_eq_zero_iff p a).mpr ha]
    simp

theorem expect_add (p : SPMF α) (f g : α → ℝ≥0∞) :
    expect p (fun a => f a + g a) = expect p f + expect p g := by
  unfold expect
  rw [← ENNReal.tsum_add]
  congr 1; ext a; rw [mul_add]

theorem expect_mul_left (p : SPMF α) (c : ℝ≥0∞) (f : α → ℝ≥0∞) :
    expect p (fun a => c * f a) = c * expect p f := by
  unfold expect
  rw [← ENNReal.tsum_mul_left]
  congr 1; ext a; ring

/-- Off-support values of `f` don't matter, so a `sound_complete` law lets `f` be understood on
valid values only. -/
theorem expect_congr_support {p : SPMF α} {f g : α → ℝ≥0∞}
    (h : ∀ a ∈ p.support, f a = g a) : expect p f = expect p g := by
  unfold expect
  refine tsum_congr fun a => ?_
  by_cases ha : a ∈ p.support
  · rw [h a ha]
  · rw [(apply_eq_zero_iff p a).mpr ha, zero_mul, zero_mul]

theorem expect_le_of_support {p : SPMF α} {f : α → ℝ≥0∞} {c : ℝ≥0∞}
    (h : ∀ a ∈ p.support, f a ≤ c) : expect p f ≤ c :=
  calc expect p f ≤ expect p (fun _ => c) := expect_mono_support h
    _ = p.mass * c := expect_const p c
    _ ≤ 1 * c := mul_le_mul_left (mass_le_one p) c
    _ = c := one_mul c

/-- Expectation over a uniform `choose` is the average over the range. The summand is taken in
`Nat` form `m` (with `hm` bridging) so callers avoid `choose`'s `ULift` subtype. -/
theorem expect_choose {lo hi : Nat} (h : lo ≤ hi)
    (f : ULift.{u} {x : Nat // lo ≤ x ∧ x ≤ hi} → ℝ≥0∞) (m : Nat → ℝ≥0∞)
    (hm : ∀ a, f a = m a.down.val) :
    expect (choose lo hi h : SPMF _) f
      = (∑ x ∈ Finset.Icc lo hi, m x) / ((hi - lo + 1 : ℕ) : ℝ≥0∞) := by
  unfold expect
  calc ∑' a, (choose lo hi h : SPMF _) a * f a
      = ∑' (a : ULift {x : Nat // lo ≤ x ∧ x ≤ hi}),
          (1 / ((hi - lo + 1 : ℕ) : ℝ≥0∞)) * m a.down.val := by
        refine tsum_congr fun a => ?_
        rw [choose_apply lo hi h a, hm a]
    _ = (1 / ((hi - lo + 1 : ℕ) : ℝ≥0∞))
          * ∑' (a : ULift {x : Nat // lo ≤ x ∧ x ≤ hi}), m a.down.val :=
        ENNReal.tsum_mul_left
    _ = (1 / ((hi - lo + 1 : ℕ) : ℝ≥0∞)) * ∑ x ∈ Finset.Icc lo hi, m x := by
        rw [tsum_subtype_Icc]
    _ = _ := by rw [one_div, mul_comm, div_eq_mul_inv]

theorem expect_pick (x y : SPMF α) (f : α → ℝ≥0∞) :
    expect (pick (fun () => x) (fun () => y)) f
      = (1/2 : ℝ≥0∞) * expect x f + (1/2 : ℝ≥0∞) * expect y f := by
  unfold RandomChoice.pick
  rw [expect_bind]
  rw [expect_choose (Nat.zero_le 1) _
    (fun n => if n == 0 then expect x f else expect y f)
    (fun a => by by_cases h : (a.down.val == 0) = true <;> simp [h])]
  have hIcc : Finset.Icc 0 1 = ({0, 1} : Finset ℕ) := by decide
  rw [hIcc, Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [Nat.sub_zero, beq_self_eq_true, if_pos, Nat.one_ne_zero, beq_iff_eq]
  norm_num
  rw [ENNReal.add_div]
  congr 1 <;> rw [ENNReal.div_eq_inv_mul]

private theorem tsum_sum_weighted_mul (gs : List (Nat × (Unit → SPMF α))) (f : α → ℝ≥0∞) :
    ∑' a, (gs.map fun p => (p.1 : ℝ≥0∞) * (p.2 ()) a).sum * f a
      = (gs.map fun p => (p.1 : ℝ≥0∞) * expect (p.2 ()) f).sum := by
  induction gs with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.map_cons, List.sum_cons]
    simp_rw [add_mul]
    rw [ENNReal.tsum_add, ih]
    congr 1
    unfold expect
    rw [← ENNReal.tsum_mul_left]
    congr 1; ext a; ring

/-- The expectation over a weighted choice is the weighted average of the branch expectations. -/
theorem expect_frequency {gs : List (Nat × (Unit → SPMF α))}
    (h : 0 < (gs.map Prod.fst).sum) (f : α → ℝ≥0∞) :
    expect (frequency gs h) f
      = (gs.map fun p => (p.1 : ℝ≥0∞) * expect (p.2 ()) f).sum
          / (((gs.map Prod.fst).sum : ℕ) : ℝ≥0∞) := by
  calc expect (frequency gs h) f
      = ∑' a, (gs.map fun p => (p.1 : ℝ≥0∞) * (p.2 ()) a).sum * f a
          * ((((gs.map Prod.fst).sum : ℕ) : ℝ≥0∞))⁻¹ := by
        refine tsum_congr fun a => ?_
        rw [frequency_apply, div_eq_mul_inv, mul_right_comm]
    _ = (∑' a, (gs.map fun p => (p.1 : ℝ≥0∞) * (p.2 ()) a).sum * f a)
          * ((((gs.map Prod.fst).sum : ℕ) : ℝ≥0∞))⁻¹ := ENNReal.tsum_mul_right
    _ = _ := by rw [tsum_sum_weighted_mul, ← div_eq_mul_inv]

end expect

section prob

/-- The probability that a draw from `p` lands in `E`. -/
noncomputable def prob (p : SPMF α) (E : Set α) : ℝ≥0∞ := expect p (E.indicator 1)

theorem prob_eq_tsum_ite (p : SPMF α) (E : Set α) [DecidablePred (· ∈ E)] :
    prob p E = ∑' a, if a ∈ E then p a else 0 := by
  unfold prob expect
  refine tsum_congr fun a => ?_
  by_cases h : a ∈ E <;> simp [Set.indicator, h]

@[simp]
theorem prob_singleton (p : SPMF α) (a : α) : prob p {a} = p a := by
  unfold prob expect
  rw [tsum_eq_single a]
  · simp [Set.indicator]
  · intro b hb
    simp [Set.indicator, hb]

theorem prob_pure (a : α) (E : Set α) [Decidable (a ∈ E)] :
    prob (Pure.pure a : SPMF α) E = if a ∈ E then 1 else 0 := by
  unfold prob
  rw [expect_pure]
  by_cases h : a ∈ E <;> simp [Set.indicator, h]

/-- The law of total probability. -/
theorem prob_bind (x : SPMF α) (g : α → SPMF β) (E : Set β) :
    prob (x >>= g) E = expect x (fun a => prob (g a) E) := by
  unfold prob
  rw [expect_bind]

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

theorem prob_le_mass (p : SPMF α) (E : Set α) : prob p E ≤ p.mass := by
  rw [← expect_one]
  refine expect_mono fun a => ?_
  by_cases h : a ∈ E <;> simp [Set.indicator, h]

theorem prob_mono {p : SPMF α} {E F : Set α} (h : E ⊆ F) : prob p E ≤ prob p F := by
  refine expect_mono fun a => ?_
  by_cases ha : a ∈ E
  · simp [Set.indicator, ha, h ha]
  · simp [Set.indicator, ha]

/-- Zero probability is a support statement, so the `mem_support_*_iff` lemmas discharge it. -/
theorem prob_eq_zero_iff (p : SPMF α) (E : Set α) :
    prob p E = 0 ↔ ∀ a ∈ p.support, a ∉ E := by
  unfold prob expect
  rw [ENNReal.tsum_eq_zero]
  constructor
  · intro h a ha hE
    have := h a
    rw [mul_eq_zero] at this
    rcases this with h0 | h0
    · exact ha h0
    · simp [Set.indicator, hE] at h0
  · intro h a
    by_cases ha : a ∈ p.support
    · simp [Set.indicator, h a ha]
    · rw [(apply_eq_zero_iff p a).mpr ha, zero_mul]

/-- Markov's inequality, product form. -/
theorem mul_prob_le_expect (p : SPMF α) (f : α → ℝ≥0∞) (c : ℝ≥0∞) :
    c * prob p {a | c ≤ f a} ≤ expect p f := by
  unfold prob
  rw [← expect_mul_left]
  refine expect_mono fun a => ?_
  by_cases h : c ≤ f a
  · simp [Set.indicator, h]
  · simp [Set.indicator, h]

/-- Markov's inequality, division form. -/
theorem prob_le_expect_div (p : SPMF α) (f : α → ℝ≥0∞) {c : ℝ≥0∞}
    (hc0 : c ≠ 0) (hct : c ≠ ⊤) :
    prob p {a | c ≤ f a} ≤ expect p f / c := by
  rw [ENNReal.le_div_iff_mul_le (Or.inl hc0) (Or.inl hct), mul_comm]
  exact mul_prob_le_expect p f c

end prob

section coin

private theorem sum_ite_lt_num (r : Rat) (hnum : 0 ≤ r.num) (hle : r.num ≤ (r.den : ℤ))
    (t e : ℝ≥0∞) :
    ∑ n ∈ Finset.Icc 0 (r.den - 1), (if (n : ℤ) < r.num then t else e)
      = (r.num.toNat : ℝ≥0∞) * t + ((r.den - r.num.toNat : ℕ) : ℝ≥0∞) * e := by
  have hden : 0 < r.den := r.den_pos
  have hkd : r.num.toNat ≤ r.den := by omega
  have hIcc : Finset.Icc 0 (r.den - 1) = Finset.range r.den := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_range]
    omega
  rw [hIcc, Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (Nat.zero_le r.num.toNat) hkd]
  have hfirst : ∑ n ∈ Finset.Ico 0 r.num.toNat, (if (n : ℤ) < r.num then t else e)
      = (r.num.toNat : ℝ≥0∞) * t := by
    have hall : ∀ n ∈ Finset.Ico 0 r.num.toNat, (if (n : ℤ) < r.num then t else e) = t := by
      intro n hn
      have := (Finset.mem_Ico.mp hn).2
      rw [if_pos (by omega)]
    rw [Finset.sum_congr rfl hall, Finset.sum_const, Nat.card_Ico, Nat.sub_zero, nsmul_eq_mul]
  have hsecond : ∑ n ∈ Finset.Ico r.num.toNat r.den, (if (n : ℤ) < r.num then t else e)
      = ((r.den - r.num.toNat : ℕ) : ℝ≥0∞) * e := by
    have hall : ∀ n ∈ Finset.Ico r.num.toNat r.den, (if (n : ℤ) < r.num then t else e) = e := by
      intro n hn
      have := (Finset.mem_Ico.mp hn).1
      rw [if_neg (by omega)]
    rw [Finset.sum_congr rfl hall, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
  rw [hfirst, hsecond]

/-- The coin lands `true` with probability `r.num / r.den` and `false` with the rest. -/
theorem expect_coin {r : Rat} (h0 : 0 ≤ r) (h1 : r ≤ 1) (f : Bool → ℝ≥0∞) :
    expect (coin r : SPMF Bool) f
      = (r.num.toNat : ℝ≥0∞) / (r.den : ℝ≥0∞) * f true
        + ((r.den - r.num.toNat : ℕ) : ℝ≥0∞) / (r.den : ℝ≥0∞) * f false := by
  have hnum : 0 ≤ r.num := Rat.num_nonneg.mpr h0
  have hle : r.num ≤ (r.den : ℤ) := by
    rcases lt_or_eq_of_le h1 with h | h
    · exact (Rat.num_lt_denom_iff.mpr h).le
    · subst h
      norm_num
  unfold RandomChoice.coin
  rw [expect_bind]
  rw [expect_choose (Nat.zero_le _) _
    (fun n => if (n : ℤ) < r.num then f true else f false)
    (fun a => by by_cases h : ((a.down.val : ℤ) < r.num) <;> simp [h])]
  rw [sum_ite_lt_num r hnum hle]
  have hd : r.den - 1 - 0 + 1 = r.den := by have := r.den_pos; omega
  rw [hd, ENNReal.add_div]
  congr 1 <;> rw [div_eq_mul_inv, div_eq_mul_inv, mul_right_comm]

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

section admissibility

/-- Only *upper* bounds on expectations are admissible: the fixpoint iteration starts at `⊥`,
where every expectation is `0`, so a lower bound cannot ride `fix_induct` — prove exact laws by
inducting on an index of the event instead (`prob_listOf_length`). -/
theorem admissible_expect_le (f : α → ℝ≥0∞) (B : ℝ≥0∞) :
    Lean.Order.admissible (fun (p : SPMF α) => expect p f ≤ B) := by
  intro c hc ih
  by_cases hne : ∃ p, c p
  case neg =>
    push Not at hne
    have hz : ∀ a, (Lean.Order.CCPO.csup hc) a = 0 := by
      intro a
      rw [csup_apply hc a]
      simp [hne]
    unfold expect
    simp [hz]
  case pos =>
    calc expect (Lean.Order.CCPO.csup hc) f
        = ∑' a, (⨆ p, ⨆ (_ : c p), p a) * f a := by
          unfold expect
          exact tsum_congr fun a => by rw [csup_apply hc a]
      _ = ∑' a, ⨆ p, ⨆ (_ : c p), p a * f a := by
          refine tsum_congr fun a => ?_
          rw [ENNReal.iSup_mul]
          congr 1
          ext p
          rw [ENNReal.iSup_mul]
      _ = ⨆ s : Finset α, ∑ a ∈ s, ⨆ p, ⨆ (_ : c p), p a * f a := ENNReal.tsum_eq_iSup_sum
      _ ≤ ⨆ s : Finset α, ⨆ p, ⨆ (_ : c p), ∑ a ∈ s, p a * f a := by
          refine iSup_mono fun s => ?_
          simp_rw [iSup_subtype']
          rw [ENNReal.finsetSum_iSup]
          intro ⟨p, hp⟩ ⟨q, hq⟩
          rcases hc p q hp hq with h | h
          · exact ⟨⟨q, hq⟩, fun a => ⟨mul_le_mul_left (h a) _, le_rfl⟩⟩
          · exact ⟨⟨p, hp⟩, fun a => ⟨le_rfl, mul_le_mul_left (h a) _⟩⟩
      _ ≤ ⨆ p, ⨆ (_ : c p), expect p f := by
          refine iSup_le fun s => iSup₂_mono fun p hp => ?_
          exact ENNReal.sum_le_tsum s
      _ ≤ B := iSup₂_le ih

end admissibility

section combinators

/-- A fixed-length draw lands entirely in `E` with probability `prob g E ^ n`. -/
theorem prob_vectorOf_all {g : SPMF α} (E : Set α) (n : Nat) :
    prob (vectorOf n g) {xs | ∀ x ∈ xs, x ∈ E} = prob g E ^ n := by
  classical
  induction n with
  | zero =>
    rw [show vectorOf 0 g = (Pure.pure [] : SPMF (List α)) from rfl, prob_pure,
      if_pos (by intro y hy; simp at hy), pow_zero]
  | succ n ih =>
    rw [vectorOf_succ, prob_bind]
    have hpt : ∀ (x : α) (xs : List α),
        prob (Pure.pure (x :: xs) : SPMF (List α)) {xs | ∀ y ∈ xs, y ∈ E}
          = E.indicator 1 x * ({xs : List α | ∀ y ∈ xs, y ∈ E}).indicator 1 xs := by
      intro x xs
      rw [prob_pure]
      by_cases hx : x ∈ E <;> by_cases hxs : ∀ y ∈ xs, y ∈ E <;>
        simp [Set.indicator, hx, hxs]
    calc expect g (fun x =>
            prob (vectorOf n g >>= fun xs => Pure.pure (x :: xs)) {xs | ∀ y ∈ xs, y ∈ E})
        = expect g (fun x => E.indicator 1 x * prob g E ^ n) := by
          refine expect_congr_support fun x _ => ?_
          rw [prob_bind]
          calc expect (vectorOf n g)
                (fun xs => prob (Pure.pure (x :: xs) : SPMF (List α)) {xs | ∀ y ∈ xs, y ∈ E})
              = expect (vectorOf n g)
                  (fun xs => E.indicator 1 x
                    * ({xs : List α | ∀ y ∈ xs, y ∈ E}).indicator 1 xs) :=
                expect_congr_support fun xs _ => hpt x xs
            _ = E.indicator 1 x
                  * expect (vectorOf n g) (({xs : List α | ∀ y ∈ xs, y ∈ E}).indicator 1) :=
                expect_mul_left _ _ _
            _ = E.indicator 1 x * prob g E ^ n := by
                exact congrArg (E.indicator 1 x * ·) ih
      _ = expect g (fun x => prob g E ^ n * E.indicator 1 x) := by
          congr 1
          funext x
          ring
      _ = prob g E ^ n * expect g (E.indicator 1) := expect_mul_left _ _ _
      _ = prob g E ^ (n + 1) := (pow_succ _ _).symm

/-- The length of a `listOf` draw is geometrically distributed. -/
theorem prob_listOf_length (g : SPMF α) (hg : IsPMF g) (k : Nat) :
    prob (listOf g) {xs | xs.length = k} = (1/2 : ℝ≥0∞) ^ (k + 1) := by
  induction k with
  | zero =>
    rw [listOf, prob_pick, prob_pure]
    simp only [Set.mem_ofPred_eq, List.length_nil]
    have hz : prob (g >>= fun x => listOf g >>= fun xs => Pure.pure (x :: xs))
        {xs | xs.length = 0} = 0 := by
      rw [prob_eq_zero_iff]
      intro a ha
      simp only [mem_support_bind_iff, mem_support_pure_iff] at ha
      obtain ⟨x, hx, xs, hxs, rfl⟩ := ha
      simp
    rw [hz]
    norm_num
  | succ k ih =>
    rw [listOf, prob_pick, prob_pure]
    simp only [Set.mem_ofPred_eq, List.length_nil]
    rw [if_neg (by omega)]
    have hstep : prob (g >>= fun x => listOf g >>= fun xs => Pure.pure (x :: xs))
        {xs | xs.length = k + 1} = (1/2 : ℝ≥0∞) ^ (k + 1) := by
      rw [prob_bind]
      have hinner : ∀ x : α,
          prob (listOf g >>= fun xs => Pure.pure (x :: xs)) {xs | xs.length = k + 1}
            = (1/2 : ℝ≥0∞) ^ (k + 1) := by
        intro x
        rw [prob_bind]
        have hpt : ∀ xs : List α,
            prob (Pure.pure (x :: xs) : SPMF (List α)) {xs | xs.length = k + 1}
              = ({xs : List α | xs.length = k}).indicator 1 xs := by
          intro xs
          rw [prob_pure]
          by_cases h : xs.length = k
          · simp [Set.indicator, h]
          · rw [if_neg (by simp; omega)]
            simp [Set.indicator, h]
        calc expect (listOf g)
              (fun xs => prob (Pure.pure (x :: xs) : SPMF (List α)) {xs | xs.length = k + 1})
            = expect (listOf g) (({xs : List α | xs.length = k}).indicator 1) :=
              expect_congr_support fun xs _ => hpt xs
          _ = (1/2 : ℝ≥0∞) ^ (k + 1) := ih
      calc expect g (fun x =>
              prob (listOf g >>= fun xs => Pure.pure (x :: xs)) {xs | xs.length = k + 1})
          = expect g (fun _ => (1/2 : ℝ≥0∞) ^ (k + 1)) :=
            expect_congr_support fun x _ => hinner x
        _ = g.mass * (1/2 : ℝ≥0∞) ^ (k + 1) := expect_const _ _
        _ = (1/2 : ℝ≥0∞) ^ (k + 1) := by rw [hg, one_mul]
    rw [hstep, mul_zero, zero_add, pow_succ]
    ring

/-- No `IsPMF` hypothesis: missing mass only lowers the expectation. -/
theorem expect_listOf_length_le (g : SPMF α) :
    expect (listOf g) (fun xs => (xs.length : ℝ≥0∞)) ≤ 1 := by
  delta listOf
  apply Lean.Order.fix_induct
    (motive := fun (p : SPMF (List α)) => expect p (fun xs => (xs.length : ℝ≥0∞)) ≤ 1)
    _ ?admissible ?step
  case admissible => exact admissible_expect_le _ _
  case step =>
    intro listOf_rec ih
    rw [expect_pick, expect_pure, expect_bind]
    simp only [List.length_nil, Nat.cast_zero, mul_zero, zero_add]
    have hinner : ∀ x : α,
        expect (listOf_rec >>= fun xs => Pure.pure (x :: xs))
          (fun xs => (xs.length : ℝ≥0∞)) ≤ 2 := by
      intro x
      rw [expect_bind]
      calc expect listOf_rec
            (fun xs => expect (Pure.pure (x :: xs) : SPMF (List α))
              (fun xs => (xs.length : ℝ≥0∞)))
          = expect listOf_rec (fun xs => (xs.length : ℝ≥0∞) + 1) := by
            refine expect_congr_support fun xs _ => ?_
            rw [expect_pure]
            push_cast [List.length_cons]
            ring
        _ = expect listOf_rec (fun xs => (xs.length : ℝ≥0∞))
              + expect listOf_rec (fun _ => 1) := expect_add _ _ _
        _ ≤ 1 + 1 := add_le_add ih (by rw [expect_one]; exact mass_le_one _)
        _ = 2 := by norm_num
    have half : ∀ E : ℝ≥0∞, E ≤ 2 → (1/2 : ℝ≥0∞) * E ≤ 1 := by
      intro E hE
      calc (1/2 : ℝ≥0∞) * E ≤ (1/2 : ℝ≥0∞) * 2 := mul_le_mul_right hE _
        _ = 1 := by
          rw [one_div]
          exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)
    apply half
    refine le_trans (expect_mono fun x => hinner x) ?_
    rw [expect_const]
    calc g.mass * 2 ≤ 1 * 2 := mul_le_mul_left (mass_le_one g) _
      _ = 2 := by norm_num

end combinators

end SPMF
