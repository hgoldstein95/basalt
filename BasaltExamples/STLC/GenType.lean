/-
Copyright (c) 2026 Harrison Goldstein & Ernest Ng. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein & Ernest Ng
-/
import Basalt
import Basalt.PlausibleGen
import BasaltExamples.STLC.Syntax

open RandomChoice SPMF List

/-!
# Arbitrary STLC Types

The `genType` generator produces an arbitrary `Ty`, along with proofs that it is complete,
terminates, and is cost-bounded by `Ty.size`.
-/

/-- Generates an arbitrary type. -/
def genType [Gen G] : G Ty :=
  pick
    (fun _ => pure .Bool)
    (fun _ => do
      let τ1 ← genType
      let τ2 ← genType
      return .Fun τ1 τ2)
partial_fixpoint

/-- `genType` can produce every type. -/
theorem genType_support : τ ∈ SPMF.support (genType (G := SPMF)) := by
  induction τ with
  | Bool => rw [genType]; simp
  | Fun τ1 τ2 ih1 ih2 =>
    rw [genType]
    support_simp [Ty.Fun.injEq]
    exact Or.inr ⟨τ1, ih1, τ2, ih2, rfl, rfl⟩

/-- `genType` terminates with probability 1 -/
theorem genType_terminates : SPMF.IsPMF (genType (G := SPMF)) := by
  refine SPMF.IsPMF_of_critical (F := fun c => 1 / 2 + 1 / 2 * c ^ 2)
    (fun c hle hge => ?_) ?_
  · rw [← ENNReal.toReal_eq_one_iff]
    ennreal_to_real at hge
    ennreal_to_real at hle
    norm_num at hge hle
    nlinarith [sq_nonneg (c.toReal - 1)]
  · conv_rhs => rw [genType]
    simp only [SPMF.mass_pick, SPMF.mass_pure, mul_one]
    gcongr
    rw [sq]
    refine SPMF.mass_bind_ge_mul (le_refl _) (fun τ1 => ?_)
    rw [SPMF.mass_bind_pure]

/-- `genType` makes at most `τ.size` random choices to produce `τ`. -/
theorem genType_cost : IsBounded (genType (G := SPMF.Cost)) (fun τ => τ.size) := by
  open Lean.Order in
  delta genType
  apply fix_induct
    (motive := fun (g : SPMF.Cost Ty) => IsBounded g (fun τ => τ.size)) _ ?admissible ?step
  case admissible => apply admissible_IsBounded
  case step =>
    intro genType_rec ih
    rw [IsBounded_iff]
    rintro ⟨τ, n⟩ hmem
    cost_support_simp at hmem
    obtain ⟨m, rfl, h | h⟩ := hmem
    · obtain ⟨rfl, rfl⟩ := h
      simp [Ty.size]
    · obtain ⟨τ1, n1, n2, hτ1, ⟨τ2, n3, n4, hτ2, ⟨rfl, hn4⟩, hn2⟩, hm⟩ := h
      have h1 : n1 ≤ τ1.size := ih (τ1, n1) hτ1
      have h2 : n3 ≤ τ2.size := ih (τ2, n3) hτ2
      show 1 + m ≤ (Ty.Fun τ1 τ2).size
      simp only [Ty.size]
      omega
