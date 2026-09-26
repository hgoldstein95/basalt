/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt.SPMF.Cost
import Basalt.SPMF.Failure

/-!
# Generator Correctness Properties

The basic, mostly orthogonal, correctness properties a PBT generator may have, as plain predicates
— there is no bundle: which of them apply depends on the generator, and you prove the ones that do.
-/

/-- Every value `g` can produce satisfies `P`. A size-bounded generator is sound and deliberately
not complete. -/
def IsSound (g : SPMF α) (P : α → Prop) : Prop :=
  ∀ a ∈ SPMF.support g, P a

/-- Every value satisfying `P` is one `g` can produce. -/
def IsCompleteFor (g : SPMF α) (P : α → Prop) : Prop :=
  ∀ a, P a → a ∈ SPMF.support g

/-- The values `g` can produce are exactly those satisfying `P`. -/
structure IsSoundAndComplete (g : SPMF α) (P : α → Prop) : Prop where
  intro ::
  sound : IsSound g P
  complete : IsCompleteFor g P

theorem IsSoundAndComplete.of_support_eq {g g' : SPMF α} {P : α → Prop}
    (h : SPMF.support g' = SPMF.support g) (hg : IsSoundAndComplete g P) :
    IsSoundAndComplete g' P :=
  ⟨fun a ha => hg.sound a (h ▸ ha), fun a hP => h ▸ hg.complete a hP⟩

/-- `g` terminates with probability 1: its mass is 1, so every infinite path has probability 0. It
need not terminate structurally. -/
abbrev IsAlmostSurelyTerminating (g : SPMF α) : Prop :=
  SPMF.IsPMF g

/-- Producing `v` takes at most `c v` random choices. -/
def IsCostBounded (g : SPMF.Cost α) (c : α → Nat) : Prop :=
  ∀ p ∈ SPMF.support g, p.2 ≤ c p.1

theorem IsCostBounded.mono {g : SPMF.Cost α} {c₁ c₂ : α → Nat} (h : IsCostBounded g c₁)
    (hc : ∀ a, c₁ a ≤ c₂ a) : IsCostBounded g c₂ :=
  fun p hp => (h p hp).trans (hc p.1)

/-- A partial generator never fails: all of its mass is on successes. -/
def IsFilterFree (g : SPMF (Option α)) : Prop :=
  SPMF.massSome g = 1

/-- A partial generator succeeds with positive probability: rejection sampling from it is safe. -/
def IsProductive (g : SPMF (Option α)) : Prop :=
  0 < SPMF.massSome g

/-- One value the generator can produce makes it productive: `massSome` sums over every success. -/
theorem IsProductive.of_mem_support {g : SPMF (Option α)} {a : α}
    (h : some a ∈ SPMF.support g) : IsProductive g :=
  ((SPMF.apply_pos_iff g (some a)).mpr h).trans_le (ENNReal.le_tsum (f := fun a => g (some a)) a)

theorem IsFilterFree.isProductive {g : SPMF (Option α)} (h : IsFilterFree g) :
    IsProductive g := by
  rw [IsProductive, h]; exact zero_lt_one

/-- Filter-freedom as a single value of `g`, for a generator that terminates: without `mass = 1`,
missing mass could be divergence rather than filtering. -/
theorem IsFilterFree_iff_massNone_eq_zero {g : SPMF (Option α)} (hmass : g.mass = 1) :
    IsFilterFree g ↔ SPMF.massNone g = 0 := by
  have hsplit := SPMF.mass_split g
  rw [hmass] at hsplit
  constructor
  · intro h
    rw [IsFilterFree] at h
    rw [h] at hsplit
    have hsplit' : (1 : ENNReal) + 0 = 1 + SPMF.massNone g := by simpa using hsplit
    exact ((ENNReal.add_right_inj (by finiteness)).mp hsplit').symm
  · intro h
    rw [h, add_zero] at hsplit
    exact hsplit.symm
