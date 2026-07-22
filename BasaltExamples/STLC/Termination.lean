/-
Copyright (c) 2026 Harrison Goldstein & Ernest Ng. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein & Ernest Ng
-/
import Basalt
import Basalt.PlausibleGen
import BasaltExamples.STLC.Syntax
import BasaltExamples.STLC.GenType
import BasaltExamples.STLC.GenTerm

open RandomChoice SPMF List ENNReal

/-!
# Almost-Sure Termination for `genTerm`

This file proves `genTerm.terminates`: `genTerm Γ τ` terminates with probability 1.

## The regime

`genTerm` (`BasaltExamples/STLC/GenTerm.lean`) is a `oneOf` over up to four branches, and its
recursion *re-indexes the seed* (the pair `(Γ, τ)`): the `App` branch recurses at `(Γ, argTy.Fun τ)`
and `(Γ, argTy)`, and the `Abs` branch at `(τ1 :: Γ, τ2)`. So termination uses a `_family` criterion.

Reading the mean offspring off the branch lists (each branch weighted `1 / #branches`):

* **vars ≠ [], `Bool`**  — `[genZero, elements, App, genBool]`, offspring `(0 + 0 + 2 + 0)/4 = 1/2`.
* **vars ≠ [], `Fun`**   — `[genZero, elements, App, Abs]`,     offspring `(0 + 0 + 2 + 1)/4 = 3/4`.
* **vars = [],  `Bool`** — `[genZero, App, genBool]`,           offspring `(0 + 2 + 0)/3 = 2/3`.
* **vars = [],  `Fun`**  — `[genZero, App, Abs]`,               offspring `(0 + 2 + 1)/3 = 1`.

The last case has mean offspring exactly `1`, so `genTerm` is **critical**: it terminates almost
surely, but (like `Tree.genHeap` and `AllTwoTree.genTree`) has infinite expected size. Termination
therefore goes through `SPMF.IsPMF_of_critical_family` rather than the subcritical criterion.

## The lower-bounding function `F`

`IsPMF_of_critical_family` needs a single `F` with `F c ≤ (g i).mass` for *every* seed `i`, whose
only fixed-or-below point in `[0, 1]` is `1`. We use

```
F c = 1/3 + 1/3 · c + 1/3 · c²
```

which is the exact one-step bound for the critical case above (`genZero`'s mass is `1`, the two
recursive `App` calls contribute `c²`, and the single `Abs` call contributes `c`). One checks
`F c ≤ (branch average)` for all four branch lists when `c ≤ 1`, and `F c = c ∧ c ≤ 1 → c = 1`
(the fixed-point equation is `(c - 1)² = 0`).

`oneOf` has no equality mass lemma, so the lower bound comes from `SPMF.mass_oneOf_ge` (the `oneOf`
analogue of `mass_frequency_ge`, in `Basalt/SPMF/Termination.lean`): a uniform `oneOf` is bounded
below by the average of any per-branch lower bounds. Every branch bound is then supplied to it, one
per index.
-/

/-- `genBool` terminates with probability 1 (a single coin flip). -/
theorem genBool_terminates : SPMF.IsPMF (genBool (G := SPMF)) := by
  unfold genBool Bool.arbitrary
  apply IsPMF_map
  apply IsPMF_pick <;> apply IsPMF_pure

/-- `genZero Γ τ` terminates with probability 1: the `Abs` wrapping is pure and the recursion is
structural in `τ`, bottoming out at the terminating `genBool`. -/
theorem genZero_terminates (Γ : Ctx) (τ : Ty) : SPMF.IsPMF (genZero (G := SPMF) Γ τ) := by
  induction τ generalizing Γ with
  | Bool => unfold genZero; exact genBool_terminates
  | Fun τ1 τ2 _ IH2 =>
    unfold genZero
    apply IsPMF_bind_pure
    exact IH2 (τ1 :: Γ)

/-- The seed `(Γ, τ)` is nonempty, as required by the family termination criterion. -/
instance : Nonempty (Ctx × Ty) := ⟨(([] : Ctx), Ty.Bool)⟩

/-- `genTerm Γ τ` terminates with probability 1.

    Proof: critical family termination. The recursion re-indexes the seed `(Γ, τ)`, and the worst
    case (empty variable set at a function type) has mean offspring exactly `1`, so we use
    `SPMF.IsPMF_of_critical_family` with `F c = (1 + c + c²)/3`. One unfolding exposes a `oneOf`;
    `mass_oneOf_ge` reduces its mass to the average of the branch bounds — `genZero`/`genBool`
    (mass `1`), `elements` (mass `1`), the `App` branch (`≥ c²`, two recursive calls after a
    terminating `genType`), and the `Abs` branch (`≥ c`, one recursive call) — which dominates `F`
    in every configuration. -/
theorem genTerm.terminates (Γ : Ctx) (τ : Ty) :
    IsAlmostSurelyTerminating (genTerm (G := SPMF) Γ τ) := by
  -- The family of generators, indexed by the seed `(Γ, τ)`.
  set g : Ctx × Ty → SPMF Term := fun j => genTerm j.1 j.2 with hg_def
  have hg : ∀ j, g j = genTerm j.1 j.2 := fun _ => rfl
  suffices h : ∀ j : Ctx × Ty, SPMF.IsPMF (g j) from h (Γ, τ)
  refine SPMF.IsPMF_of_critical_family g (F := fun c => 1 / 3 + 1 / 3 * c + 1 / 3 * c ^ 2)
    (fun c hle hstep => ?_) ?_
  · -- `F c ≤ c ∧ c ≤ 1 → c = 1`: the fixed-point equation reduces to `(c - 1)² = 0`.
    rw [← ENNReal.toReal_eq_one_iff]
    have hct : c ≠ ⊤ := ne_top_of_le_ne_top one_ne_top hle
    ennreal_to_real at hstep
    have hx0 : 0 ≤ c.toReal := ENNReal.toReal_nonneg
    nlinarith [sq_nonneg (c.toReal - 1), hstep]
  · -- Step: one unfolding lower-bounds the mass by `F` of the family infimum `c`.
    intro j
    obtain ⟨Γ, τ⟩ := j
    set c := ⨅ j, (g j).mass with hc_def
    have hc1 : c ≤ 1 := (iInf_le _ (Γ, τ)).trans (mass_le_one _)
    have hct : c ≠ ⊤ := ne_top_of_le_ne_top one_ne_top hc1
    -- The `Abs`/`genBool` branch bound, proved before the `τ`-dependent facts so that `cases τ`
    -- does not drag them into the match motive.
    have hAbs : ((match τ with
        | Ty.Bool => genBool
        | Ty.Fun τ1 τ2 => do
            let e ← genTerm (τ1 :: Γ) τ2
            Pure.pure (Term.Abs τ1 e) : SPMF Term)).mass ≥ c := by
      cases τ with
      | Bool => rw [genBool_terminates]; exact hc1
      | Fun τ1 τ2 =>
        rw [mass_bind_pure, ← hg (τ1 :: Γ, τ2)]
        exact mass_ge_iInf g (τ1 :: Γ, τ2)
    -- `genZero` is a PMF, so its branch has mass 1.
    have hZero : (genZero (G := SPMF) Γ τ).mass = 1 := genZero_terminates Γ τ
    -- The `App` branch: a terminating `genType` followed by two recursive calls, hence `≥ c * c`.
    have hApp : (do
        let argTy ← genType (G := SPMF)
        let e1 ← genTerm Γ (argTy.Fun τ)
        let e2 ← genTerm Γ argTy
        Pure.pure (e1.App e2)).mass ≥ c * c := by
      apply mass_bind_ge_of_isPMF genType_terminates
      intro argTy
      refine mass_bind_ge_mul ?_ (fun e1 => ?_)
      · rw [← hg (Γ, argTy.Fun τ)]; exact mass_ge_iInf g (Γ, argTy.Fun τ)
      · rw [mass_bind_pure, ← hg (Γ, argTy)]; exact mass_ge_iInf g (Γ, argTy)
    -- Unfold one step and split on whether the context has a variable of the right type.
    rw [hg (Γ, τ)]
    show (genTerm (G := SPMF) Γ τ).mass ≥ _
    conv_lhs => rw [genTerm.eq_def]
    simp only []
    split
    · -- vars ≠ [] : four branches `[genZero, elements, App, Abs/genBool]`.
      rename_i hne
      refine le_trans ?_ (mass_oneOf_ge _ (m := fun i => [1, 1, c * c, c].getD i 0) ?_)
      · -- `F c ≤ (1 + 1 + c² + c)/4`, i.e. `(c + 2)(1 - c) ≥ 0`.
        have hsum : (∑ i ∈ Finset.Icc 0 (4 - 1), (fun i => [(1 : ENNReal), 1, c * c, c].getD i 0) i)
            = 1 + 1 + c * c + c := by
          rw [show (Finset.Icc 0 (4 - 1)) = {0, 1, 2, 3} by decide]; simp [List.getD]; ring
        simp only [List.length_cons, List.length_nil] at hsum ⊢
        rw [hsum, show ((4 : ℕ) : ENNReal) = 4 by norm_num]
        ennreal_to_real
        have hx1 : c.toReal ≤ 1 := (ENNReal.toReal_le_toReal hct one_ne_top).mpr hc1
        have hx0 : 0 ≤ c.toReal := ENNReal.toReal_nonneg
        nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ c.toReal + 2)
          (by linarith : (0 : ℝ) ≤ 1 - c.toReal)]
      · -- Each of the four branches meets its bound.
        intro i hi
        simp only [List.length_cons, List.length_nil] at hi
        match i, hi with
        | 0, _ => exact hZero.ge
        | 1, _ => exact (IsPMF_elements (varsWithType Γ τ) hne).ge
        | 2, _ => exact hApp
        | 3, _ => exact hAbs
    · -- vars = [] : three branches `[genZero, App, Abs/genBool]` — the critical case.
      refine le_trans ?_ (mass_oneOf_ge _ (m := fun i => [1, c * c, c].getD i 0) ?_)
      · -- `F c = (1 + c² + c)/3` exactly.
        have hsum : (∑ i ∈ Finset.Icc 0 (3 - 1), (fun i => [(1 : ENNReal), c * c, c].getD i 0) i)
            = 1 + c * c + c := by
          rw [show (Finset.Icc 0 (3 - 1)) = {0, 1, 2} by decide]; simp [List.getD]; ring
        simp only [List.length_cons, List.length_nil] at hsum ⊢
        rw [hsum, show ((3 : ℕ) : ENNReal) = 3 by norm_num]
        ennreal_to_real
        have hx1 : c.toReal ≤ 1 := (ENNReal.toReal_le_toReal hct one_ne_top).mpr hc1
        have hx0 : 0 ≤ c.toReal := ENNReal.toReal_nonneg
        nlinarith [sq_nonneg c.toReal]
      · -- Each of the three branches meets its bound.
        intro i hi
        simp only [List.length_cons, List.length_nil] at hi
        match i, hi with
        | 0, _ => exact hZero.ge
        | 1, _ => exact hApp
        | 2, _ => exact hAbs
