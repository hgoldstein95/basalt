/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt.SPMF.Mass
import Basalt.Tactic.Average
import Basalt.Walk.Entry

/-!
# Computing Mass Lower Bounds

The structural half of a termination proof. Mass is the expectation of `1`, so `mass_bound` is the
walk of `Basalt/Obs/Ordered.lean` for a lower bound on `SPMF.expectObs` at that postexpectation,
leaving a goal that is pure `ℝ≥0∞` arithmetic. What is specific to the judgment is here: how a fact
about a sub-generator's mass is used.
-/

open ENNReal RandomChoice Lean Meta Elab Tactic

namespace SPMF

/-! ## Leaves

A fact bounds a sub-generator's mass; the walk arrives with the postexpectation its continuation
computed. -/

/-- Chaining rule: a known-terminating generator has mass `1`. -/
theorem le_mass_of_isPMF {x : SPMF α} (h : IsPMF x) : (1 : ℝ≥0∞) ≤ x.mass := h.ge

/-- At the postexpectation `1`, which is where a generator's last draw is met. -/
theorem le_spec_one_of_le_mass {x : SPMF α} {p : α → ℝ≥0∞} {c : ℝ≥0∞} (hx : c ≤ x.mass)
    (hp : ∀ a, p a = 1) : c ≤ expectObs.spec x p := by
  show c ≤ expect x p
  rw [funext hp, expect_one]
  exact hx

theorem le_spec_of_le_mass {x : SPMF α} {p : α → ℝ≥0∞} {c d : ℝ≥0∞} (hx : c ≤ x.mass)
    (hp : ∀ a, p a = d) : c * d ≤ expectObs.spec x p := by
  show c * d ≤ expect x p
  rw [funext hp, expect_const]
  gcongr

theorem le_spec_of_isPMF {x : SPMF α} {p : α → ℝ≥0∞} {d : ℝ≥0∞} (hx : IsPMF x)
    (hp : ∀ a, p a = d) : d ≤ expectObs.spec x p :=
  (one_mul d).ge.trans (le_spec_of_le_mass hx.ge hp)

/-- The fallback for a continuation whose bound depends on the value drawn: a fact about the mass
alone can only be used with the worst case over every value. -/
theorem le_spec_iInf_of_le_mass {x : SPMF α} {p : α → ℝ≥0∞} {c : ℝ≥0∞} (hx : c ≤ x.mass) :
    c * ⨅ a, p a ≤ expectObs.spec x p :=
  (le_spec_of_le_mass hx fun _ => rfl).trans (expect_mono fun a => iInf_le p a)

@[inherit_doc le_spec_iInf_of_le_mass]
theorem le_spec_iInf_of_isPMF {x : SPMF α} {p : α → ℝ≥0∞} (hx : IsPMF x) :
    ⨅ a, p a ≤ expectObs.spec x p :=
  (one_mul _).ge.trans (le_spec_iInf_of_le_mass hx.ge)

end SPMF

namespace Basalt.MassBound

open Basalt.Walk

/-- `mass_bound` replaces a goal `c ≤ (gen …).mass` by the `ℝ≥0∞` inequality `c ≤ b`, where `b` is
the bound it computes by walking `gen`'s syntax: a draw's postexpectation is the bound its
continuation computed. Recursive occurrences are closed from the local context, callees from their
`.terminates` law; any other fact can be passed as `mass_bound [h₁, h₂]`. -/
syntax (name := massBoundTac) "mass_bound" (" [" term,* "]")? : tactic

elab_rules : tactic
  | `(tactic| mass_bound $[[$args,*]]?) => withMainContext do
    let goal ← getMainGoal
    let ty ← whnfR (← goal.getType)
    let bad := m!"mass_bound: expected a goal `_ ≤ (gen …).mass`, got{indentExpr ty}"
    unless ty.isAppOfArity ``LE.le 4 do throwError bad
    let rhs ← whnfR (ty.getArg! 3)
    unless rhs.isAppOfArity ``SPMF.mass 2 do throwError bad
    let g := rhs.getArg! 1
    -- `SPMF.expect g (fun _ => 1) = g.mass`
    let one ← mkAppOptM ``SPMF.expect_one #[none, g]
    let some (_, lhs, _) := (← inferType one).eq? | throwError bad
    let (bound, structural, rest) ←
      computeBound ((args.map (·.getElems)).getD #[]) ``SPMF.expectObs true g (lhs.getArg! 2)
    let arith ← mkFreshExprMVar (mkApp2 ty.appFn!.appFn! (ty.getArg! 2) bound)
    goal.assign (← mkAppM ``le_of_le_of_eq #[← mkAppM ``le_trans #[arith, structural], one])
    replaceMainGoal (← (arith.mvarId! :: rest).mapM fun g => tidy g)

end Basalt.MassBound

namespace SPMF

/-! ## The list combinators

They take a bound on their element generator's mass, and their own is used at the postexpectation
the walk arrives with: exactly when that is constant, and otherwise at its worst case over every
list, as `le_spec_iInf_of_le_mass` does for a leaf. The unbounded-length ones (`le_spec_listOf`,
`le_spec_nonEmptyListOf`, in `MassFixpoint.lean`) only turn a terminating element generator into a
terminating list generator. -/

private theorem pow_le_mass_vectorOf {n : Nat} {g : SPMF α} {c : ℝ≥0∞} (hg : c ≤ g.mass) :
    c ^ n ≤ (vectorOf n g : SPMF (List α)).mass := by
  induction n with
  | zero => exact (pow_zero c).trans_le (mass_pure _).ge
  | succ n ih =>
    rw [vectorOf_succ]
    mass_bound
    rw [pow_succ']

@[gen_rule]
theorem le_spec_vectorOf {n : Nat} {g : SPMF α} {c d : ℝ≥0∞} {p : List α → ℝ≥0∞}
    (hg : c ≤ expectObs.spec g fun _ => 1) (hp : ∀ a, p a = d) :
    c ^ n * d ≤ expectObs.spec (vectorOf n g) p :=
  le_spec_of_le_mass (pow_le_mass_vectorOf (hg.trans_eq (expect_one g))) hp

/-- The fallback for a postexpectation that depends on the list drawn. -/
@[gen_rule]
theorem le_spec_vectorOf_iInf {n : Nat} {g : SPMF α} {c : ℝ≥0∞} {p : List α → ℝ≥0∞}
    (hg : c ≤ expectObs.spec g fun _ => 1) :
    c ^ n * ⨅ a, p a ≤ expectObs.spec (vectorOf n g) p :=
  le_spec_iInf_of_le_mass (pow_le_mass_vectorOf (hg.trans_eq (expect_one g)))

private theorem pow_le_mass_listOfMaxLength {n : Nat} {g : SPMF α} {c : ℝ≥0∞} (hg : c ≤ g.mass) :
    min 1 c ^ n ≤ (listOfMaxLength n g : SPMF (List α)).mass := by
  unfold listOfMaxLength
  rw [← expect_one, expect_bind, expect_map]
  refine le_trans ?_ (Mix.le_average_range (h := Nat.zero_le n) (d := fun _ => min 1 c ^ n)
    fun k hk => ?_)
  · rw [Finset.sum_const, card_Icc_eq 0 n (Nat.zero_le n), nsmul_eq_mul, mul_comm,
      ENNReal.mul_div_cancel_right (by simp) (by simp)]
  · simp only [Function.comp_apply, expect_one]
    exact (pow_le_pow_right_of_le_one' (min_le_left 1 c) hk.2).trans
      ((pow_le_pow_left' (min_le_right 1 c) k).trans (pow_le_mass_vectorOf hg))

@[gen_rule]
theorem le_spec_listOfMaxLength {n : Nat} {g : SPMF α} {c d : ℝ≥0∞} {p : List α → ℝ≥0∞}
    (hg : c ≤ expectObs.spec g fun _ => 1) (hp : ∀ a, p a = d) :
    min 1 c ^ n * d ≤ expectObs.spec (listOfMaxLength n g) p :=
  le_spec_of_le_mass (pow_le_mass_listOfMaxLength (hg.trans_eq (expect_one g))) hp

@[gen_rule, inherit_doc le_spec_vectorOf_iInf]
theorem le_spec_listOfMaxLength_iInf {n : Nat} {g : SPMF α} {c : ℝ≥0∞} {p : List α → ℝ≥0∞}
    (hg : c ≤ expectObs.spec g fun _ => 1) :
    min 1 c ^ n * ⨅ a, p a ≤ expectObs.spec (listOfMaxLength n g) p :=
  le_spec_iInf_of_le_mass (pow_le_mass_listOfMaxLength (hg.trans_eq (expect_one g)))

end SPMF
