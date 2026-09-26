/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt.SPMF.Cost
import Basalt.SPMF.Expect.Obs
import Basalt.SPMF.Termination

/-!
# Generator Correctness Properties

The basic, mostly orthogonal, correctness properties a PBT generator may have, as plain predicates
— there is no bundle: which of them apply depends on the generator, and you prove the ones that do.
Each but the bundle `IsSoundAndComplete` is defined in the form a reader checks, and restated by
`<Law>.iff_obs` on an observation, the form a walk proves; `<Law>.obs` restates a fact for passing
to one.
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
