/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt.SPMF.Termination

open ENNReal

/-!
# Ranking-Function Termination

A reusable criterion for almost-sure termination of recursive generators, with an expected-size
bound as a byproduct.

Model a recursive generator as an unfold over a seed space `ι`: one step at seed `i` makes a
weighted choice, and each branch recurses on a (possibly random) list of child seeds. Abstract
one step as a *level operator* `A : (ι → ℝ≥0∞) → (ι → ℝ≥0∞)`, where `A e i` is the expected
total of `e` over the child seeds of one step at `i`.

Given a **ranking function** `φ : ι → ℝ≥0∞` whose expected value drops by at least `ε` at every
step (`A φ i + ε ≤ φ i`), the generator terminates with probability 1 from every seed
(`IsPMF_of_ranking`), and the expected number of unfolding steps from seed `i` is at most
`φ i / ε` (`LevelOp.tsum_iterate_le`).

The proof lives entirely in `ℝ≥0∞` — a Knaster–Tarski-style bound on the partial sums plus the
observation that a series whose terms all dominate a positive constant sums to `⊤`. No
martingales, no measure theory, no limits.

## Main Definitions

- `SPMF.LevelOp` — the algebraic laws a level operator must satisfy.
- `SPMF.IsPMF_of_ranking` — the general termination theorem.
- `SPMF.IsPMF_of_subcritical` — the static-seed corollary: a generator whose one-step deficit
  shrinks by a factor `m < 1` (mean offspring below 1) is a PMF.
- `SPMF.IsPMF_of_critical` — the boundary case (`m = 1`): a single-seed wrapper around
  `IsPMF_of_mass_fixpoint`, for generators whose only mass fixed point below 1 is 1 itself.
- `ENNReal.one_sub_prod_le_sum_one_sub` — the union bound *"the chance that some child diverges
  is at most the sum of the chances that each does"*, used to discharge `hstep` for branches
  that make several recursive calls.
-/

namespace SPMF

section level_op

variable {ι : Type*}

/-- A *level operator* abstracts one step of a recursive generator's unfolding: `A e i` is the
  expected total of `e` over the child seeds spawned by one step at seed `i`. -/
structure LevelOp (A : (ι → ℝ≥0∞) → (ι → ℝ≥0∞)) : Prop where
  mono : ∀ e f, e ≤ f → A e ≤ A f
  add : ∀ e f, A (e + f) = A e + A f
  smul : ∀ (r : ℝ≥0∞) (e), A (fun i => r * e i) = fun i => r * A e i

namespace LevelOp

variable {A : (ι → ℝ≥0∞) → (ι → ℝ≥0∞)}

theorem map_zero (hA : LevelOp A) : A 0 = 0 := by
  have h := hA.smul 0 0
  simpa [Pi.zero_def] using h

theorem map_sum (hA : LevelOp A) {β : Type*} (s : Finset β) (f : β → ι → ℝ≥0∞) :
    A (∑ b ∈ s, f b) = ∑ b ∈ s, A (f b) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hA.map_zero
  | insert b s hb ih => rw [Finset.sum_insert hb, Finset.sum_insert hb, hA.add, ih]

/-- Division by `ε` commutes with a level operator. -/
theorem map_div (hA : LevelOp A) (φ : ι → ℝ≥0∞) (ε : ℝ≥0∞) :
    A (fun j => φ j / ε) = fun i => A φ i / ε := by
  have h := hA.smul ε⁻¹ φ
  calc A (fun j => φ j / ε)
      = A (fun j => ε⁻¹ * φ j) := by
        congr 1; funext j; rw [div_eq_mul_inv, mul_comm]
    _ = fun i => ε⁻¹ * A φ i := h
    _ = fun i => A φ i / ε := by
        funext i; rw [div_eq_mul_inv, mul_comm]

/-- The partial sums of the expected level sizes `A^[k] 1` are uniformly bounded by `φ/ε`:
  `φ/ε` is a pre-fixed point of `X ↦ 1 + A X`, and the partial sums climb toward it from below. -/
theorem sum_iterate_le (hA : LevelOp A) (φ : ι → ℝ≥0∞) {ε : ℝ≥0∞}
    (hε0 : ε ≠ 0) (hε_top : ε ≠ ⊤) (hdrift : ∀ i, A φ i + ε ≤ φ i) (n : ℕ) :
    ∑ k ∈ Finset.range n, A^[k] (fun _ => 1) ≤ fun i => φ i / ε := by
  have hpre : ∀ i, A (fun j => φ j / ε) i + 1 ≤ φ i / ε := by
    intro i
    rw [congrFun (hA.map_div φ ε) i]
    calc A φ i / ε + 1
        = A φ i / ε + ε / ε := by rw [ENNReal.div_self hε0 hε_top]
      _ = (A φ i + ε) / ε := by rw [ENNReal.div_add_div_same]
      _ ≤ φ i / ε := by gcongr; exact hdrift i
  induction n with
  | zero => simp only [Finset.range_zero, Finset.sum_empty]; exact fun _ => zero_le _
  | succ n ih =>
    rw [Finset.sum_range_succ']
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
    rw [← hA.map_sum]
    intro i
    simp only [Pi.add_apply]
    calc A (∑ k ∈ Finset.range n, A^[k] fun _ => 1) i + 1
        ≤ A (fun j => φ j / ε) i + 1 := by gcongr; exact hA.mono _ _ ih i
      _ ≤ φ i / ε := hpre i

/-- **The expected-size bound.** `∑ₖ A^[k] 1 i` is the expected total number of unfolding steps
  taken from seed `i` (level `k` contributes its expected number of seeds); an `ε`-drifting
  ranking function bounds it by `φ i / ε`. -/
theorem tsum_iterate_le (hA : LevelOp A) (φ : ι → ℝ≥0∞) {ε : ℝ≥0∞}
    (hε0 : ε ≠ 0) (hε_top : ε ≠ ⊤) (hdrift : ∀ i, A φ i + ε ≤ φ i) (i : ι) :
    ∑' k, A^[k] (fun _ => 1) i ≤ φ i / ε := by
  rw [ENNReal.tsum_eq_iSup_nat]
  refine iSup_le fun n => ?_
  have h := hA.sum_iterate_le φ hε0 hε_top hdrift n i
  simpa [Finset.sum_apply] using h

/-- The expected total number of unfolding steps of a level operator from seed `i`: level `k`
  contributes its expected number of seeds, `A^[k] 1 i`. -/
noncomputable def expectedSteps (A : (ι → ℝ≥0∞) → (ι → ℝ≥0∞)) (i : ι) : ℝ≥0∞ :=
  ∑' k, A^[k] (fun _ => 1) i

/-- The drift certificate bounds the expected number of unfolding steps by `φ/ε`. -/
theorem expectedSteps_le (hA : LevelOp A) (φ : ι → ℝ≥0∞) {ε : ℝ≥0∞}
    (hε0 : ε ≠ 0) (hε_top : ε ≠ ⊤) (hdrift : ∀ i, A φ i + ε ≤ φ i) (i : ι) :
    expectedSteps A i ≤ φ i / ε :=
  hA.tsum_iterate_le φ hε0 hε_top hdrift i

/-- For the static-seed operator with mean offspring `m`, the expected number of steps is
  the geometric sum `1/(1-m)`. -/
theorem expectedSteps_const_mul (m : ℝ≥0∞) (i : ι) :
    expectedSteps (fun e j => m * e j) i = (1 - m)⁻¹ := by
  have hiter : ∀ k, (fun (e : ι → ℝ≥0∞) j => m * e j)^[k] (fun _ => 1) = fun _ => m ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ_apply', ih]
      funext j
      rw [pow_succ, mul_comm]
  unfold expectedSteps
  rw [tsum_congr fun k => congrFun (hiter k) i]
  exact ENNReal.tsum_geometric m

end LevelOp

/-- **Ranking-function termination.** Let `g : ι → SPMF α` be a family of generators indexed by
  a seed, let `A` be a level operator describing the expected child seeds of one unfolding step,
  and let `φ` be a ranking function whose expected value drops by at least `ε > 0` at every step.
  If one unfolding of `g` is dominated by `A` in deficit form (`hstep`), then every `g i`
  terminates almost surely. -/
theorem IsPMF_of_ranking {ι : Type*} {α : Type*} (g : ι → SPMF α)
    {A : (ι → ℝ≥0∞) → (ι → ℝ≥0∞)} (hA : LevelOp A)
    (φ : ι → ℝ≥0∞) (hφ_top : ∀ i, φ i ≠ ⊤) {ε : ℝ≥0∞} (hε : 0 < ε)
    (hdrift : ∀ i, A φ i + ε ≤ φ i)
    (hstep : ∀ i, 1 - (g i).mass ≤ A (fun j => 1 - (g j).mass) i) :
    ∀ i, IsPMF (g i) := by
  intro i
  have hε_top : ε ≠ ⊤ := by
    intro htop
    apply hφ_top i
    have h := hdrift i
    rw [htop, add_top, top_le_iff] at h
    exact h
  -- The divergence probability from each seed.
  set d : ι → ℝ≥0∞ := fun j => 1 - (g j).mass
  -- `d` is dominated by every level: `d ≤ A^[k] 1`.
  have hd_le : ∀ k, d ≤ A^[k] (fun _ => 1) := by
    intro k
    induction k with
    | zero => intro j; simpa using tsub_le_self
    | succ k ih =>
      intro j
      calc d j ≤ A d j := hstep j
        _ ≤ A (A^[k] fun _ => 1) j := hA.mono _ _ ih j
        _ = A^[k + 1] (fun _ => 1) j := by rw [Function.iterate_succ_apply']
  -- The series `∑ₖ A^[k] 1 i` is finite, so a constant lower bound on its terms must be zero.
  have hd0 : d i = 0 := by
    by_contra hne
    have hsum : (⊤ : ℝ≥0∞) ≤ φ i / ε := by
      calc (⊤ : ℝ≥0∞) = ∑' (_ : ℕ), d i := (ENNReal.tsum_const_eq_top_of_ne_zero hne).symm
        _ ≤ ∑' k, A^[k] (fun _ => 1) i := ENNReal.tsum_le_tsum fun k => hd_le k i
        _ ≤ φ i / ε := hA.tsum_iterate_le φ hε.ne' hε_top hdrift i
    exact (ENNReal.div_lt_top (hφ_top i) hε.ne').ne (top_le_iff.mp hsum)
  -- Zero divergence probability means mass 1.
  have hmass : 1 ≤ (g i).mass := tsub_eq_zero_iff_le.mp hd0
  exact le_antisymm (g i).tsum_coe hmass

end level_op

end SPMF

namespace ENNReal

/-- `1 - 1/2 = 1/2` in `ℝ≥0∞`. -/
theorem one_sub_half : (1 : ℝ≥0∞) - 1 / 2 = 1 / 2 := by
  rw [one_div, ENNReal.one_sub_inv_two]

private theorem list_prod_le_one {xs : List ℝ≥0∞} (h : ∀ x ∈ xs, x ≤ 1) : xs.prod ≤ 1 := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    rw [List.prod_cons]
    exact mul_le_one' (h x List.mem_cons_self) (ih fun y hy => h y (List.mem_cons_of_mem x hy))

/-- **The union bound**: the chance that some element of a product falls short of 1 is at most
  the sum of the individual shortfalls. Applied to generator masses: the chance that some child
  diverges is at most the sum of the chances that each does. This is the only probabilistic idea
  in the ranking-function development. -/
theorem one_sub_prod_le_sum_one_sub (xs : List ℝ≥0∞) (h : ∀ x ∈ xs, x ≤ 1) :
    1 - xs.prod ≤ (xs.map (1 - ·)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx : x ≤ 1 := h x List.mem_cons_self
    have hxs : ∀ y ∈ xs, y ≤ 1 := fun y hy => h y (List.mem_cons_of_mem x hy)
    simp only [List.prod_cons, List.map_cons, List.sum_cons]
    calc 1 - x * xs.prod
        ≤ (1 - x) + (x - x * xs.prod) := tsub_le_tsub_add_tsub
      _ = (1 - x) + x * (1 - xs.prod) := by
          congr 1
          rw [ENNReal.mul_sub fun _ _ => (lt_of_le_of_lt hx one_lt_top).ne, mul_one]
      _ ≤ (1 - x) + 1 * (1 - xs.prod) := by gcongr
      _ ≤ (1 - x) + (xs.map (1 - ·)).sum := by rw [one_mul]; gcongr; exact ih hxs

/-- Binary form of the union bound, for a branch making two recursive calls. -/
theorem one_sub_mul_le_add {a b : ℝ≥0∞} (ha : a ≤ 1) (hb : b ≤ 1) :
    1 - a * b ≤ (1 - a) + (1 - b) := by
  have h := one_sub_prod_le_sum_one_sub [a, b] (by simp [ha, hb])
  simpa using h

/-- **Deficit splitting** for one unfolding step: a generator whose mass is at least
  `w + m * X` — escape branches carrying weight `w`, recursive continuation of mass `X`
  weighted `m`, with `w + m = 1` — has divergence probability at most `m * (1 - X)`.
  This is the standard first move when discharging the `hstep` obligation of
  `SPMF.IsPMF_of_ranking` or `SPMF.IsPMF_of_subcritical`. -/
theorem one_sub_le_mul_one_sub {g w m X : ℝ≥0∞} (hwm : w + m = 1) (hm : m ≠ ⊤)
    (hmass : w + m * X ≤ g) : 1 - g ≤ m * (1 - X) := by
  have h1w : 1 - w = m :=
    ENNReal.sub_eq_of_eq_add ((le_self_add.trans hwm.le).trans_lt ENNReal.one_lt_top).ne
      (by rw [← hwm, add_comm])
  calc 1 - g ≤ 1 - (w + m * X) := tsub_le_tsub_left hmass 1
    _ = 1 - w - m * X := by rw [tsub_add_eq_tsub_tsub]
    _ = m * 1 - m * X := by rw [h1w, mul_one]
    _ = m * (1 - X) := (ENNReal.mul_sub fun _ _ => hm).symm

/-- **Averaged union bound**: if a step draws one of `s.card ≥ n` continuations uniformly
  (each of mass `m x ≤ 1`), the deficit of the average is at most the average of the
  deficits. Pairs with `SPMF.mass_bind_choose_ge` for generators that draw a uniform pivot. -/
theorem one_sub_sum_div_le {β : Type*} {s : Finset β} {m : β → ℝ≥0∞} {n : ℝ≥0∞}
    (hn0 : n ≠ 0) (hntop : n ≠ ⊤) (hns : n ≤ s.card) (hm : ∀ x ∈ s, m x ≤ 1) :
    1 - (∑ x ∈ s, m x) / n ≤ (∑ x ∈ s, (1 - m x)) / n := by
  rw [tsub_le_iff_right, ENNReal.div_add_div_same]
  calc (1 : ℝ≥0∞) = n / n := (ENNReal.div_self hn0 hntop).symm
    _ ≤ (∑ x ∈ s, ((1 - m x) + m x)) / n := by
        gcongr
        calc n ≤ (s.card : ℝ≥0∞) := hns
          _ = ∑ _x ∈ s, (1 : ℝ≥0∞) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
          _ ≤ _ := Finset.sum_le_sum fun x hx => (tsub_add_cancel_of_le (hm x hx)).ge
    _ = _ := by rw [Finset.sum_add_distrib]

end ENNReal

namespace SPMF

section corollaries

/-- **Subcritical termination** (the static-seed regime). If one unfolding of `g` shrinks the
  divergence probability by a factor `m < 1` — for a `frequency` over branches with weights `wⱼ` and
  `hⱼ` recursive calls, `m = Σⱼ wⱼ·hⱼ / Σⱼ wⱼ` is the mean offspring — then `g` is a PMF.  -/
theorem IsPMF_of_subcritical {α : Type*} {g : SPMF α} {m : ℝ≥0∞} (hm : m < 1)
    (hstep : 1 - g.mass ≤ m * (1 - g.mass)) : IsPMF g := by
  have h1m : 1 - m ≠ 0 := fun h0 => absurd (tsub_eq_zero_iff_le.mp h0) (not_le.mpr hm)
  refine IsPMF_of_ranking (ι := Unit) (fun _ => g)
    (A := fun e _ => m * e ()) ⟨?_, ?_, ?_⟩ (fun _ => (1 - m)⁻¹) (fun _ => ?_) (ε := 1)
    one_pos (fun _ => ?_) (fun _ => hstep) ()
  · intro e f hef _
    exact mul_le_mul' le_rfl (hef ())
  · intro e f
    funext _
    exact mul_add m (e ()) (f ())
  · intro r e
    funext _
    exact mul_left_comm m r (e ())
  · finiteness
  · -- drift: `m * (1-m)⁻¹ + 1 ≤ (1-m)⁻¹`, with equality — the geometric series bound is tight.
    show m * (1 - m)⁻¹ + 1 ≤ (1 - m)⁻¹
    have hm1 : m ≤ 1 := hm.le
    have hmlt : m.toReal < 1 := by
      simpa using (ENNReal.toReal_lt_toReal (by finiteness) ENNReal.one_ne_top).mpr hm
    ennreal_to_real
    have hne : (1 : ℝ) - m.toReal ≠ 0 := by linarith
    exact le_of_eq (by field_simp; ring)

/-- Mass form of `IsPMF_of_subcritical`: what one reads off directly from unfolding a
  generator whose non-recursive branches carry total probability `1 - m`. -/
theorem IsPMF_of_subcritical_mass {α : Type*} {g : SPMF α} {m : ℝ≥0∞} (hm : m < 1)
    (hstep : (1 - m) + m * g.mass ≤ g.mass) : IsPMF g := by
  have hm_top : m ≠ ⊤ := (hm.trans one_lt_top).ne
  refine IsPMF_of_subcritical hm ?_
  calc 1 - g.mass
      ≤ 1 - ((1 - m) + m * g.mass) := tsub_le_tsub_left hstep 1
    _ = (1 - (1 - m)) - m * g.mass := by rw [tsub_add_eq_tsub_tsub]
    _ = m - m * g.mass := by rw [ENNReal.sub_sub_cancel one_ne_top hm.le]
    _ = m * (1 - g.mass) := by
        rw [ENNReal.mul_sub fun _ _ => hm_top, mul_one]

/-- A `c ≤ 1` whose deficit shrinks by a factor `m < 1` must be `1`. -/
theorem _root_.ENNReal.eq_one_of_deficit_le_mul {c m : ℝ≥0∞} (hm : m < 1) (hle : c ≤ 1)
    (h : 1 - c ≤ m * (1 - c)) : c = 1 := by
  by_contra hne
  have hpos : 0 < 1 - c :=
    pos_iff_ne_zero.mpr fun h0 => hne (le_antisymm hle (tsub_eq_zero_iff_le.mp h0))
  have htop : (1 : ℝ≥0∞) - c ≠ ⊤ := (tsub_le_self.trans_lt one_lt_top).ne
  have hlt : (1 : ℝ≥0∞) - c < 1 - c :=
    calc 1 - c ≤ m * (1 - c) := h
      _ = (1 - c) * m := mul_comm _ _
      _ < (1 - c) * 1 := ENNReal.mul_lt_mul_right hpos.ne' htop hm
      _ = 1 - c := mul_one _
  exact absurd hlt (lt_irrefl _)

/-- **Family form of subcritical termination**, for a subcritical generator whose recursion
  re-indexes the seed. One unfolding must bound the mass below by `(1 - m) + m * X` where `X`
  is the family infimum of the masses; recursive occurrences are bounded by `mass_ge_iInf`. -/
theorem IsPMF_of_subcritical_mass_family {ι : Type*} {α : Type*} [Nonempty ι]
    (g : ι → SPMF α) {m : ℝ≥0∞} (hm : m < 1)
    (hstep : ∀ i, (1 - m) + m * (⨅ j, (g j).mass) ≤ (g i).mass) :
    ∀ i, IsPMF (g i) := by
  have hm_top : m ≠ ⊤ := (hm.trans one_lt_top).ne
  refine IsPMF_of_mass_fixpoint g (fun c => (1 - m) + m * c) ?_ (fun i _ => hstep i)
  intro c hle hge
  refine ENNReal.eq_one_of_deficit_le_mul hm hle ?_
  calc 1 - c
      ≤ 1 - ((1 - m) + m * c) := tsub_le_tsub_left hge 1
    _ = (1 - (1 - m)) - m * c := by rw [tsub_add_eq_tsub_tsub]
    _ = m - m * c := by rw [ENNReal.sub_sub_cancel one_ne_top hm.le]
    _ = m * (1 - c) := by rw [ENNReal.mul_sub fun _ _ => hm_top, mul_one]

/-- **Critical termination** (the `m = 1` boundary). A single-seed wrapper around
  `IsPMF_of_mass_fixpoint`: if the mass satisfies `F g.mass ≤ g.mass` for an `F` whose only
  fixed-or-below point in `[0, 1]` is `1`, then `g` is a PMF. This is the classical extinction
  argument; it proves termination but — unlike the subcritical case — comes with no
  expected-size bound, and indeed a critical generator's expected size is infinite. -/
theorem IsPMF_of_critical {α : Type*} {g : SPMF α} (F : ℝ≥0∞ → ℝ≥0∞)
    (hF : ∀ c : ℝ≥0∞, c ≤ 1 → F c ≤ c → c = 1)
    (hstep : F g.mass ≤ g.mass) : IsPMF g := by
  haveI : Nonempty Unit := ⟨()⟩
  refine IsPMF_of_mass_fixpoint (fun _ : Unit => g) F ?_ ?_ ()
  · intro c hle hge
    exact hF c hle hge
  · intro _ _
    simpa [iInf_const] using hstep

/-- **Family form of critical termination**, for a critical generator whose recursion
  re-indexes the seed: one unfolding must bound the mass below by `F` of the family infimum
  of the masses. Like `IsPMF_of_critical`, it comes with no expected-size bound. -/
theorem IsPMF_of_critical_family {ι : Type*} {α : Type*} [Nonempty ι]
    (g : ι → SPMF α) (F : ℝ≥0∞ → ℝ≥0∞)
    (hF : ∀ c : ℝ≥0∞, c ≤ 1 → F c ≤ c → c = 1)
    (hstep : ∀ i, F (⨅ j, (g j).mass) ≤ (g i).mass) :
    ∀ i, IsPMF (g i) :=
  IsPMF_of_mass_fixpoint g F (fun c hle hge => hF c hle hge) (fun i _ => hstep i)

end corollaries

section combinators

variable {α : Type*}

/-- If a generator `g` is an SPMF, then `listOf g` is also an SPMF. -/
theorem IsPMF_listOf {g : SPMF α} (hg : IsPMF g) :
    IsPMF (listOf g) := by
  -- Total probability of non-recursive branches is 1/2, hence `m := 1/2`
  refine IsPMF_of_subcritical_mass (m := 1 / 2) (by norm_num) ?_
  rw [ENNReal.one_sub_half]
  conv_rhs => rw [listOf]
  simp only [mass_pick, mass_pure, mul_one]
  gcongr
  apply mass_bind_ge_of_isPMF hg
  intro x
  rw [mass_bind_pure]

/-- If a generator `g` is an SPMF, then `nonEmptyListOf g` is also an SPMF. -/
theorem IsPMF_nonEmptyListOf {g : SPMF α} (hg : IsPMF g) :
    IsPMF (nonEmptyListOf g) := by
  -- Total probability of non-recursive branches is 1/2, hence `m := 1/2`
  refine IsPMF_of_subcritical_mass (m := 1 / 2) (by norm_num) ?_
  rw [ENNReal.one_sub_half]
  conv_rhs => rw [nonEmptyListOf]
  -- In the base case, we have `g >>= fun x => pure [x]`,
  -- whose mass is `g.mass = 1` by assumption
  have hg' : g.mass = 1 := hg
  simp only [mass_pick, mass_bind_pure, hg', mul_one]
  gcongr
  apply mass_bind_ge_of_isPMF
  . assumption
  . intro x
    rw [mass_bind_pure]

end combinators

end SPMF
