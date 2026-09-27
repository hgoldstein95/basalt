/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt.SPMF.Cost
import Basalt.SPMF.CostErasure
import Basalt.SPMF.Expect.Obs
import Basalt.SPMF.Termination

/-!
# Generator Correctness Properties

The basic, mostly orthogonal, correctness properties a PBT generator may have, as plain predicates
— there is no bundle: which of them apply depends on the generator, and you prove the ones that do.
Each but the bundle `IsSoundAndComplete` and `IsCostFaithful`, which relates two interpretations,
is defined in the form a reader checks, and restated by `<Law>.iff_obs` on an observation, the form
a walk proves; `<Law>.obs` restates a fact for passing to one.
-/

open scoped ENNReal

/-- Every value `g` can produce satisfies `P`. A size-bounded generator is sound and deliberately
not complete. -/
def IsSoundFor (g : SPMF α) (P : α → Prop) : Prop :=
  ∀ a ∈ SPMF.support g, P a

theorem IsSoundFor.iff_obs {g : SPMF α} {P : α → Prop} : IsSoundFor g P ↔ SPMF.alwaysObs.spec g P :=
  Iff.rfl

theorem IsSoundFor.obs {g : SPMF α} {P : α → Prop} (h : IsSoundFor g P) :
    SPMF.alwaysObs.spec g P :=
  h

/-- Every value satisfying `P` is one `g` can produce. -/
def IsCompleteFor (g : SPMF α) (P : α → Prop) : Prop :=
  ∀ a, P a → a ∈ SPMF.support g

theorem IsCompleteFor.iff_obs {g : SPMF α} {P : α → Prop} :
    IsCompleteFor g P ↔ ∀ a, P a → SPMF.mayObs.spec g (· = a) :=
  forall_congr' fun _ => imp_congr_right fun _ => SPMF.mem_support_iff_may

theorem IsCompleteFor.obs {g : SPMF α} {P : α → Prop} (h : IsCompleteFor g P) :
    ∀ a, P a → SPMF.mayObs.spec g (· = a) :=
  iff_obs.mp h

/-- Completeness by strong induction on a measure `μ` of seed and value: each step may assume
completeness for every seed and value of smaller measure. -/
theorem IsCompleteFor.of_measure {σ α : Type} {gen : σ → SPMF α} {P : σ → α → Prop}
    (μ : σ → α → Nat)
    (step : ∀ n, (∀ s a, μ s a < n → P s a → a ∈ (gen s).support) →
      ∀ s a, μ s a < n + 1 → P s a → a ∈ (gen s).support) (s : σ) :
    IsCompleteFor (gen s) (P s) := by
  have : ∀ n s a, μ s a < n → P s a → a ∈ (gen s).support := by
    intro n
    induction n with
    | zero => intro _ _ h; omega
    | succ n ih => exact step n ih
  exact fun a => this _ s a (Nat.lt_succ_self _)

/-- The values `g` can produce are exactly those satisfying `P`. -/
structure IsSoundAndComplete (g : SPMF α) (P : α → Prop) : Prop where
  intro ::
  sound : IsSoundFor g P
  complete : IsCompleteFor g P

theorem IsSoundAndComplete.of_support_eq {g g' : SPMF α} {P : α → Prop}
    (h : SPMF.support g' = SPMF.support g) (hg : IsSoundAndComplete g P) :
    IsSoundAndComplete g' P :=
  ⟨fun a ha => hg.sound a (h ▸ ha), fun a hP => h ▸ hg.complete a hP⟩

/-- `g` terminates with probability 1: its mass is 1, so every infinite path has probability 0. It
need not terminate structurally. -/
def IsAlmostSurelyTerminating (g : SPMF α) : Prop :=
  g.mass = 1

theorem IsAlmostSurelyTerminating.iff_obs {g : SPMF α} :
    IsAlmostSurelyTerminating g ↔ 1 ≤ SPMF.expectObs.spec g fun _ => 1 := by
  show g.mass = 1 ↔ 1 ≤ SPMF.expect g fun _ => 1
  rw [SPMF.expect_one]
  exact ⟨fun h => h.ge, le_antisymm (SPMF.mass_le_one g)⟩

theorem IsAlmostSurelyTerminating.obs {g : SPMF α} (h : IsAlmostSurelyTerminating g) :
    1 ≤ SPMF.expectObs.spec g fun _ => 1 :=
  iff_obs.mp h

/-- If one unfolding of the family `g` bounds its masses below by `T c` whenever `c` bounds them
below, and `T` has least fixed point `1`, every member terminates. -/
theorem IsAlmostSurelyTerminating.of_lfpIsOne {ι : Type*} (g : ι → SPMF α)
    {T : (ι → ℝ≥0∞) → (ι → ℝ≥0∞)} (hT : SPMF.LfpIsOne T)
    (hstep : ∀ c ≤ 1, (∀ j, c j ≤ SPMF.expectObs.spec (g j) fun _ => 1) →
      ∀ i, T c i ≤ SPMF.expectObs.spec (g i) fun _ => 1) :
    ∀ i, IsAlmostSurelyTerminating (g i) :=
  SPMF.mass_eq_one_of_lfpIsOne g hT fun c hc hrec i =>
    (hstep c hc (fun j => (hrec j).trans_eq (SPMF.expect_one _).symm) i).trans_eq
      (SPMF.expect_one _)

/-- The criterion with one bound `c` for every member of the family. -/
theorem IsAlmostSurelyTerminating.of_lfpIsOne_uniform {ι : Type*} (g : ι → SPMF α)
    {F : ℝ≥0∞ → ℝ≥0∞} (hF : SPMF.LfpIsOne F)
    (hstep : ∀ c ≤ 1, (∀ j, c ≤ SPMF.expectObs.spec (g j) fun _ => 1) →
      ∀ i, F c ≤ SPMF.expectObs.spec (g i) fun _ => 1) :
    ∀ i, IsAlmostSurelyTerminating (g i) :=
  SPMF.mass_eq_one_of_lfpIsOne_uniform g hF fun c hc hrec i =>
    (hstep c hc (fun j => (hrec j).trans_eq (SPMF.expect_one _).symm) i).trans_eq
      (SPMF.expect_one _)

/-- Producing `v` takes at most `c v` random choices. -/
def IsCostBounded (g : SPMF.Cost α) (c : α → Nat) : Prop :=
  ∀ p ∈ SPMF.support g, p.2 ≤ c p.1

theorem IsCostBounded.iff_obs {g : SPMF.Cost α} {c : α → Nat} :
    IsCostBounded g c ↔ SPMF.Cost.alwaysObs.spec g fun v n_v => n_v ≤ c v :=
  Iff.rfl

theorem IsCostBounded.obs {g : SPMF.Cost α} {c : α → Nat} (h : IsCostBounded g c) :
    SPMF.Cost.alwaysObs.spec g fun v n_v => n_v ≤ c v :=
  h

theorem IsCostBounded.mono {g : SPMF.Cost α} {c₁ c₂ : α → Nat} (h : IsCostBounded g c₁)
    (hc : ∀ a, c₁ a ≤ c₂ a) : IsCostBounded g c₂ :=
  fun p hp => (h p hp).trans (hc p.1)

/-- Producing a value takes at most `B` random choices on average. Unlike `IsCostBounded`, a run may
spend choices its value does not show — a retry, an absorbed duplicate — as long as the average
stays within `B`. A run that never returns has no mass, so this says nothing of termination: with
`IsAlmostSurelyTerminating` and a finite `B`, the generator terminates positively almost surely. -/
def IsExpectedCostBounded (g : SPMF.Cost α) (B : ℝ≥0∞) : Prop :=
  SPMF.expect g (fun p => (p.2 : ℝ≥0∞)) ≤ B

theorem IsExpectedCostBounded.iff_obs {g : SPMF.Cost α} {B : ℝ≥0∞} :
    IsExpectedCostBounded g B ↔ SPMF.Cost.expectObs.spec g (fun _ n => (n : ℝ≥0∞)) ≤ B :=
  Iff.rfl

theorem IsExpectedCostBounded.obs {g : SPMF.Cost α} {B : ℝ≥0∞} (h : IsExpectedCostBounded g B) :
    SPMF.Cost.expectObs.spec g (fun _ n => (n : ℝ≥0∞)) ≤ B :=
  h

theorem IsExpectedCostBounded.mono {g : SPMF.Cost α} {B₁ B₂ : ℝ≥0∞}
    (h : IsExpectedCostBounded g B₁) (hB : B₁ ≤ B₂) : IsExpectedCostBounded g B₂ :=
  h.trans hB

/-- No finite bound holds of a generator whose expected cost `E` is at least `a + E`, for `a > 0`:
what one unfolding of a critical generator shows. -/
theorem IsExpectedCostBounded.not_of_step {g : SPMF.Cost α} {a B : ℝ≥0∞} (ha : a ≠ 0)
    (hB : B ≠ ⊤)
    (hstep : a + SPMF.Cost.expectObs.spec g (fun _ n => (n : ℝ≥0∞))
      ≤ SPMF.Cost.expectObs.spec g fun _ n => (n : ℝ≥0∞)) :
    ¬ IsExpectedCostBounded g B := fun h => by
  have hE := iff_obs.mp h
  generalize SPMF.Cost.expectObs.spec g (fun _ n => (n : ℝ≥0∞)) = E at hstep hE
  exact ha (nonpos_iff_eq_zero.mp (ENNReal.le_of_add_le_add_right (ne_top_of_le_ne_top hB hE)
    (hstep.trans_eq (zero_add E).symm)))

/-- `gen` at `SPMF.Cost`, its costs dropped, has its `SPMF` distribution, so a law stated at one
interpretation can be read at the other. It is a free theorem, which Lean cannot prove once for
every generator: each field is proved by `walk fixpoint`, with a callee's law passed by its
fields. -/
structure IsCostFaithful (gen : {G : Type → Type} → [Gen G] → G α) : Prop where
  erasedLe : SPMF.Cost.ErasedLe gen gen
  leErased : SPMF.Cost.LeErased gen gen

/-- An expectation of the value alone is the same at both interpretations. -/
theorem IsCostFaithful.expect_eq {gen : {G : Type → Type} → [Gen G] → G α}
    (h : IsCostFaithful gen) (f : α → ℝ≥0∞) :
    SPMF.Cost.expectObs.spec (gen (G := SPMF.Cost)) (fun a _ => f a)
      = SPMF.expectObs.spec (gen (G := SPMF)) f :=
  le_antisymm (h.erasedLe f) (h.leErased f)

/-- A terminating generator has mass `1` at `SPMF.Cost` too: the fact a lower bound on an expected
cost needs of it. -/
theorem IsCostFaithful.one_le_mass {gen : {G : Type → Type} → [Gen G] → G α}
    (h : IsCostFaithful gen) (ht : IsAlmostSurelyTerminating (gen (G := SPMF))) :
    1 ≤ SPMF.Cost.expectObs.spec (gen (G := SPMF.Cost)) fun _ _ => 1 :=
  (IsAlmostSurelyTerminating.obs ht).trans_eq (h.expect_eq fun _ => 1).symm

/-- A cost bound `c` on each value gives a bound on the expected cost: `c`'s expectation, which is
an expectation of the value alone and so may be computed at `SPMF`. -/
theorem IsExpectedCostBounded.of_costBounded {gen : {G : Type → Type} → [Gen G] → G α}
    (hf : IsCostFaithful gen) {c : α → Nat} (hc : IsCostBounded (gen (G := SPMF.Cost)) c) :
    IsExpectedCostBounded (gen (G := SPMF.Cost))
      (SPMF.expect (gen (G := SPMF)) fun a => (c a : ℝ≥0∞)) :=
  (SPMF.expect_mono_support fun p hp => by
    show (p.2 : ℝ≥0∞) ≤ c p.1; exact_mod_cast hc p hp).trans_eq
    (hf.expect_eq fun a => (c a : ℝ≥0∞))
