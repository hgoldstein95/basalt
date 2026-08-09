/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt.Gen
import Basalt.SPMF
import Basalt.SPMF.Cost
import Basalt.SPMF.Failure

/-!
# Generator Correctness Properties

The basic, mostly orthogonal, correctness properties a PBT generator may have, as plain `def`s —
there is no bundle: which of them apply depends on the generator, and you prove the ones that do.
-/

/-- We say that a generator `g` `IsSoundAndComplete` with respect to a predicate `P` if, when
  interpreted as an `SPMF`, all values in the support of `g` satisfy `P` and all values satisfying
  `P` are in the support of `g`. -/
def IsSoundAndComplete (g : SPMF α) (P : α → Prop) : Prop :=
  ∀ a, a ∈ SPMF.support g ↔ P a

/-- Soundness and completeness transfers along a support equation. -/
theorem IsSoundAndComplete.of_support_eq {g g' : SPMF α} {P : α → Prop}
    (h : SPMF.support g' = SPMF.support g) (hg : IsSoundAndComplete g P) :
    IsSoundAndComplete g' P :=
  fun a => (h ▸ Iff.rfl : a ∈ SPMF.support g' ↔ a ∈ SPMF.support g).trans (hg a)

/-- We say that a generator `g` `IsAlmostSurelyTerminating` if, when interpreted as an `SPMF`, its
mass sums to 1 (i.e., it is a true `PMF`): every infinite path through the generator has probability
0. This does not require structural termination. -/
def IsAlmostSurelyTerminating (g : SPMF α) : Prop :=
  SPMF.IsPMF g

/-- We say that a generator `g` `IsCostBounded` with respect to a cost function `c` if, when
  generating a value `v`, the generator makes at most `c v` choices. -/
def IsCostBounded (g : SPMF.Cost α) (c : α → Nat) : Prop :=
  IsBounded g c

/-- A partial generator `IsFilterFree` if all of its mass lands on *successful* outcomes: it never
  actually fails.  -/
def IsFilterFree (g : SPMF (Option α)) : Prop :=
  SPMF.massSome g = 1

/-- A partial generator `IsProductive` if it succeeds with positive probability.  Proving this shows
  that rejection sampling is safe. -/
def IsProductive (g : SPMF (Option α)) : Prop :=
  0 < SPMF.massSome g

/-- A single reachable outcome makes a generator productive. `massSome` is a sum over *all* successes,
  so a lower bound needs only one of them — this is the cheap route to `IsProductive`, and the reason
  productivity is a much weaker ask than filter-freedom. -/
theorem IsProductive_of_apply_pos {g : SPMF (Option α)} {a : α} (h : 0 < g (some a)) :
    IsProductive g :=
  lt_of_lt_of_le h (ENNReal.le_tsum a)

/-- `IsProductive` from support membership — the form a `support` characterization hands you
  directly, so exhibiting one value the generator can produce discharges it. -/
theorem IsProductive_of_mem_support {g : SPMF (Option α)} {a : α}
    (h : some a ∈ SPMF.support g) : IsProductive g :=
  IsProductive_of_apply_pos ((SPMF.apply_pos_iff g (some a)).mpr h)

/-- Filter-freedom is strictly stronger than productivity. -/
theorem IsProductive_of_IsFilterFree {g : SPMF (Option α)} (h : IsFilterFree g) :
    IsProductive g := by
  rw [IsProductive, h]; exact zero_lt_one

/-- For an almost-surely-terminating generator, filter-freedom is exactly "never *explicitly* fails".
  This is the form worth proving: `massNone` is a single value of `g`, whereas `massSome` is a sum
  over the whole success set. The hypothesis is what separates the two failure modes — without
  `mass = 1`, missing mass could be divergence rather than filtering. -/
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
