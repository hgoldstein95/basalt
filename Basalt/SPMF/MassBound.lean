/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt.SPMF.Expect
import Basalt.SPMF.Walk

/-!
# Computing Mass Lower Bounds

The structural half of a termination proof: `mass_bound` walks a generator's syntax and *computes* a
lower bound on its mass from the `@[gen_rule]` rules, leaving a goal that is pure `ℝ≥0∞`
arithmetic.
-/

open ENNReal RandomChoice Lean Meta Elab Tactic

namespace SPMF

/-! ## The rules

At least one per combinator. Each says: given a lower bound on every sub-generator's mass, here is
the lower bound on this combinator's. `mass_bound` chains them, so the bounds are metavariables when
the rule is applied and the conclusion is what *computes* the answer. -/

/-- Chaining rule: a known-terminating callee contributes `1`. Also the bridge the `mass_bound`
tactic uses for a `<callee>.terminates` law it finds by name. -/
theorem le_mass_of_isPMF {x : SPMF α} (h : IsPMF x) : (1 : ℝ≥0∞) ≤ x.mass := h.ge

@[gen_rule]
theorem le_mass_pure {a : α} : (1 : ℝ≥0∞) ≤ (Pure.pure a : SPMF α).mass := (mass_pure a).ge

@[gen_rule]
theorem le_mass_bind {x : SPMF α} {f : α → SPMF β} {c d : ℝ≥0∞}
    (hx : c ≤ x.mass) (hf : ∀ a, d ≤ (f a).mass) : c * d ≤ (x >>= f).mass :=
  mass_bind_ge_mul hx hf

/-- The fallback for a bind whose continuation's bound depends on the drawn value, as a recursive call
on a seed computed from it does, when the draw is a uniform pivot: the bound is the average over the
range. -/
@[gen_rule]
theorem le_mass_bind_chooseNat {lo hi : Nat} {h : lo ≤ hi} {f : Nat → SPMF α}
    {d : Nat → ℝ≥0∞} (hf : ∀ a, d a ≤ (f a).mass) :
    (∑ x ∈ Finset.Icc lo hi, d x) / ((hi - lo + 1 : ℕ) : ℝ≥0∞)
      ≤ (chooseNat lo hi h >>= f).mass := by
  rw [← expect_one, expect_bind_chooseNat]
  simp only [expect_one]
  gcongr with x
  exact hf x

@[gen_rule, inherit_doc le_mass_bind_chooseNat]
theorem le_mass_bind_chooseInt {lo hi : Int} {h : lo ≤ hi} {f : Int → SPMF α}
    {d : Int → ℝ≥0∞} (hf : ∀ a, d a ≤ (f a).mass) :
    (∑ x ∈ Finset.Icc lo hi, d x) / (((hi - lo + 1).toNat : ℕ) : ℝ≥0∞)
      ≤ (chooseInt lo hi h >>= f).mass := by
  rw [← expect_one, expect_bind_chooseInt]
  simp only [expect_one]
  gcongr with x
  exact hf x

/-- The last fallback for a bind whose continuation's bound depends on the drawn value: a bound
outside the draw can only be the worst case over every value. -/
@[gen_rule]
theorem le_mass_bind_iInf {g : SPMF α} {f : α → SPMF β} {c : ℝ≥0∞} {d : α → ℝ≥0∞}
    (hg : c ≤ g.mass) (hf : ∀ a, d a ≤ (f a).mass) : c * ⨅ x, d x ≤ (g >>= f).mass :=
  le_mass_bind hg fun a => (iInf_le d a).trans (hf a)

@[gen_rule]
theorem le_mass_map {x : SPMF α} {f : α → β} {c : ℝ≥0∞} (hx : c ≤ x.mass) :
    c ≤ (f <$> x).mass := by rw [mass_map]; exact hx

@[gen_rule]
theorem le_mass_pick {x y : Unit → SPMF α} {c d : ℝ≥0∞}
    (hx : c ≤ (x ()).mass) (hy : d ≤ (y ()).mass) :
    (1/2 : ℝ≥0∞) * c + (1/2 : ℝ≥0∞) * d ≤ (pick x y).mass := by
  rw [show pick x y = pick (fun () => x ()) (fun () => y ()) from rfl, mass_pick]
  gcongr

/-- A conditional's bound is the conditional of its branches' bounds, which keeps the case split for
a bound that may depend on the seed (a shortcut on an exhausted seed has mass `1`). -/
@[gen_rule]
theorem le_mass_ite {p : Prop} [Decidable p] {x y : SPMF α} {c d : ℝ≥0∞}
    (hx : p → c ≤ x.mass) (hy : ¬p → d ≤ y.mass) :
    (if p then c else d) ≤ (if p then x else y).mass := by
  split <;> simp_all

@[gen_rule, inherit_doc le_mass_ite]
theorem le_mass_dite {p : Prop} [Decidable p] {x : p → SPMF α} {y : ¬p → SPMF α} {c d : ℝ≥0∞}
    (hx : ∀ h, c ≤ (x h).mass) (hy : ∀ h, d ≤ (y h).mass) :
    (if p then c else d) ≤ (if h : p then x h else y h).mass := by
  split <;> simp_all

/-- The fallback for a conditional on a drawn value, which the bound cannot mention: the `min` of
its branches' bounds. -/
@[gen_rule]
theorem le_mass_ite_min {p : Prop} [Decidable p] {x y : SPMF α} {c d : ℝ≥0∞}
    (hx : p → c ≤ x.mass) (hy : ¬p → d ≤ y.mass) : min c d ≤ (if p then x else y).mass := by
  split
  · exact (min_le_left _ _).trans (by simp_all)
  · exact (min_le_right _ _).trans (by simp_all)

@[gen_rule, inherit_doc le_mass_ite_min]
theorem le_mass_dite_min {p : Prop} [Decidable p] {x : p → SPMF α} {y : ¬p → SPMF α}
    {c d : ℝ≥0∞} (hx : ∀ h, c ≤ (x h).mass) (hy : ∀ h, d ≤ (y h).mass) :
    min c d ≤ (if h : p then x h else y h).mass := by
  split
  · exact (min_le_left _ _).trans (by simp_all)
  · exact (min_le_right _ _).trans (by simp_all)

@[gen_rule]
theorem le_mass_choose {lo hi : Nat} {h : lo ≤ hi} :
    (1 : ℝ≥0∞) ≤ (choose lo hi h : SPMF (ULift {x : Nat // lo ≤ x ∧ x ≤ hi})).mass :=
  (mass_choose lo hi h).ge

@[gen_rule]
theorem le_mass_chooseNat {lo hi : Nat} {h : lo ≤ hi} :
    (1 : ℝ≥0∞) ≤ (chooseNat lo hi h : SPMF Nat).mass := (mass_chooseNat lo hi h).ge

@[gen_rule]
theorem le_mass_chooseInt {lo hi : Int} {h : lo ≤ hi} :
    (1 : ℝ≥0∞) ≤ (chooseInt lo hi h : SPMF Int).mass := (mass_chooseInt lo hi h).ge

private theorem sum_le_sum_of_forall₂ {cs : List ℝ≥0∞} {gs : List (Unit → SPMF α)}
    (h : List.Forall₂ (fun c g => c ≤ (g ()).mass) cs gs) :
    cs.sum ≤ (gs.map fun g => (g ()).mass).sum := by
  induction h with
  | nil => simp
  | cons hc _ ih => simpa using add_le_add hc ih

/-- The branch bounds of a list combinator are collected pointwise, so that `mass_bound` can build
the list one `List.Forall₂.cons` at a time while the bounds are still metavariables.

The divisor is `cs.length`, not `gs.length`, although `Forall₂` makes them equal: it keeps the
computed bound free of the branches themselves, which under a `dite` carry the proof the branch was
taken and so may not escape it. -/
@[gen_rule]
theorem le_mass_oneOf {gs : List (Unit → SPMF α)} {hne : gs ≠ []} {cs : List ℝ≥0∞}
    (h : List.Forall₂ (fun c g => c ≤ (g ()).mass) cs gs) :
    cs.sum / (cs.length : ℝ≥0∞) ≤ (oneOf gs hne : SPMF α).mass := by
  rw [mass_oneOf, h.length_eq]
  exact ENNReal.div_le_div_right (sum_le_sum_of_forall₂ h) _

/-- Branch-wise mass lower bounds for a `frequency`, each paired with the weight it belongs to.
`List.Forall₂` would do, except that the weights would then have to be read back off the branches;
carrying them here is what keeps `le_mass_frequency`'s bound free of the branches themselves. -/
inductive WeightedBounds : List (Nat × ℝ≥0∞) → List (Nat × (Unit → SPMF α)) → Prop
  | nil : WeightedBounds [] []
  | cons {w : Nat} {c : ℝ≥0∞} {g : Unit → SPMF α} {cs gs}
      (h : c ≤ (g ()).mass) (hs : WeightedBounds cs gs) :
      WeightedBounds ((w, c) :: cs) ((w, g) :: gs)

theorem WeightedBounds.weights {cs : List (Nat × ℝ≥0∞)} {gs : List (Nat × (Unit → SPMF α))}
    (h : WeightedBounds cs gs) : (cs.map Prod.fst).sum = (gs.map Prod.fst).sum := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simpa using ih

theorem WeightedBounds.sum_le {cs : List (Nat × ℝ≥0∞)} {gs : List (Nat × (Unit → SPMF α))}
    (h : WeightedBounds cs gs) :
    (cs.map fun p => (p.1 : ℝ≥0∞) * p.2).sum
      ≤ (gs.map fun p => (p.1 : ℝ≥0∞) * (p.2 ()).mass).sum := by
  induction h with
  | nil => simp
  | cons hc _ ih => simpa using add_le_add (by gcongr) ih

@[gen_rule]
theorem le_mass_frequency {gs : List (Nat × (Unit → SPMF α))}
    {hw : 0 < (gs.map Prod.fst).sum} {cs : List (Nat × ℝ≥0∞)}
    (h : WeightedBounds cs gs) :
    (cs.map fun p => (p.1 : ℝ≥0∞) * p.2).sum / ((cs.map Prod.fst).sum : ℝ≥0∞)
      ≤ (frequency gs hw : SPMF α).mass := by
  rw [mass_frequency hw, h.weights]
  exact ENNReal.div_le_div_right h.sum_le _

@[gen_rule]
theorem le_mass_stopOrGo {n : Nat} {x y : Unit → SPMF α} {c d : ℝ≥0∞}
    (hx : c ≤ (x ()).mass) (hy : d ≤ (y ()).mass) :
    (c + ((n + 1 : ℕ) : ℝ≥0∞) * d) / ((1 + (n + 1) : ℕ) : ℝ≥0∞)
      ≤ (stopOrGo n x y : SPMF α).mass := by
  have h := le_mass_frequency (gs := [(1, x), (n + 1, y)])
    (hw := by simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; omega)
    (.cons hx (.cons hy .nil))
  simpa [stopOrGo] using h

end SPMF

namespace Basalt.MassBound

open Basalt.Walk

/-- `mass_bound` replaces a goal `c ≤ (gen …).mass` by the `ℝ≥0∞` inequality `c ≤ b`, where `b` is
the bound it computes by walking `gen`'s syntax with the `@[gen_rule]` rules. Recursive
occurrences are closed from the local context, callees from their `.terminates` law; any other fact
can be passed as `mass_bound [h₁, h₂]`. -/
syntax (name := massBoundTac) "mass_bound" (" [" term,* "]")? : tactic

elab_rules : tactic
  | `(tactic| mass_bound $[[$args,*]]?) => withMainContext do
    let goal ← getMainGoal
    let ty ← whnfR (← goal.getType)
    unless ty.isAppOfArity ``LE.le 4 do
      throwError "mass_bound: expected a goal `_ ≤ (gen …).mass`, got{indentExpr ty}"
    let bound ← mkFreshExprMVar (mkConst ``ENNReal)
    let structural ← mkFreshExprMVar (← mkAppM ``LE.le #[bound, ty.getArg! 3])
    if let some residual := (← walk ((args.map (·.getElems)).getD #[]) structural.mvarId!).head? then
      throwError "mass_bound: expected `_ ≤ SPMF.mass _`, got{indentExpr (← residual.getType)}"
    let arith ← mkFreshExprMVar (← mkAppM ``LE.le #[ty.getArg! 2, ← instantiateMVars bound])
    goal.assign (← mkAppM ``le_trans #[arith, structural])
    replaceMainGoal [arith.mvarId!]

end Basalt.MassBound

namespace SPMF

open RandomChoice

/-! ## Rules for the derived combinators

Proved with `mass_bound` itself where it applies. The list and option combinators take a general
sub-generator bound; the unbounded-length ones (`le_mass_listOf`, `le_mass_nonEmptyListOf`, in
`Termination.lean`) only turn a terminating element generator into a terminating list generator. -/

@[gen_rule]
theorem le_mass_coin {r : Rat} : (1 : ℝ≥0∞) ≤ (coin r : SPMF Bool).mass := by
  unfold coin
  mass_bound
  simp

/-- `elements` destructures its draw with a `match`, which no rule walks into. -/
@[gen_rule]
theorem le_mass_elements {xs : List α} {hne : xs ≠ []} :
    (1 : ℝ≥0∞) ≤ (elements xs hne : SPMF α).mass :=
  (one_mul 1).symm.le.trans (le_mass_bind (le_mass_map le_mass_choose) fun ⟨_, _, _⟩ => le_mass_pure)

@[gen_rule]
theorem le_mass_vectorOf {n : Nat} {g : SPMF α} {c : ℝ≥0∞} (hg : c ≤ g.mass) :
    c ^ n ≤ (vectorOf n g : SPMF (List α)).mass := by
  induction n with
  | zero => exact (pow_zero c).trans_le le_mass_pure
  | succ n ih =>
    rw [vectorOf_succ]
    mass_bound
    rw [pow_succ', mul_one]

@[gen_rule]
theorem le_mass_listOfMaxLength {n : Nat} {g : SPMF α} {c : ℝ≥0∞} (hg : c ≤ g.mass) :
    min 1 c ^ n ≤ (listOfMaxLength n g : SPMF (List α)).mass := by
  unfold listOfMaxLength
  refine le_trans ?_ (le_mass_bind (c := 1) (le_mass_map le_mass_choose) fun ⟨k, hk⟩ =>
    (pow_le_pow_right_of_le_one' (min_le_left 1 c) hk.2).trans
      ((pow_le_pow_left' (min_le_right 1 c) k).trans (le_mass_vectorOf hg)))
  rw [one_mul]

@[gen_rule]
theorem le_mass_biasedOptionGen {r : Rat} {g : SPMF α} {c : ℝ≥0∞} (hg : c ≤ g.mass) :
    min 1 c ≤ (biasedOptionGen r g : SPMF (Option α)).mass := by
  unfold biasedOptionGen
  mass_bound
  simp [min_comm]

@[gen_rule]
theorem le_mass_optionGen {g : SPMF α} {c : ℝ≥0∞} (hg : c ≤ g.mass) :
    min 1 c ≤ (optionGen g : SPMF (Option α)).mass :=
  le_mass_biasedOptionGen hg

end SPMF
