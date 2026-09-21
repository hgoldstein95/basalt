/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt.SPMF.Cost
import Basalt.Obs.Ordered
import Basalt.SPMF.Walk

/-!
# Computing Expectation Upper Bounds

`expect_bound` pushes a postexpectation through a generator with the rules of
`Basalt/Obs/Ordered.lean` and computes an upper bound on its expectation, leaving `ℝ≥0∞` arithmetic.
What is specific to expectation is here: how an average is bounded for each shape of choice, shared
by both interpretations, and how a fact about a sub-generator is used.
-/

open ENNReal RandomChoice Lean Meta Elab Tactic

instance : SPMF.expectObs.Monotone := ⟨fun _ _ _ h => SPMF.expect_mono h⟩

instance : SPMF.Cost.expectObs.MonotoneC := ⟨fun _ _ _ h => SPMF.expect_mono fun p => h p.1 p.2⟩

namespace Mix

/-! ## The average of bounds bounds the average -/

theorem average_mix_mono {lo hi : Nat} {F F' : ULift.{u} {x : Nat // lo ≤ x ∧ x ≤ hi} → ℝ≥0∞}
    (h : ∀ a, F a ≤ F' a) : Mix.average.mix lo hi F ≤ Mix.average.mix lo hi F' :=
  ENNReal.tsum_le_tsum fun a => by gcongr; exact h a

@[gen_rule]
theorem average_mix_le {lo hi : Nat} {F : ULift.{u} {x : Nat // lo ≤ x ∧ x ≤ hi} → ℝ≥0∞}
    {d : Nat → ℝ≥0∞} (h : ∀ x (hx : lo ≤ x ∧ x ≤ hi), F ⟨⟨x, hx⟩⟩ ≤ d x) :
    Mix.average.mix lo hi F ≤ (∑ x ∈ Finset.Icc lo hi, d x) / ((hi - lo + 1 : ℕ) : ℝ≥0∞) :=
  (average_mix_mono fun a => h a.down.val a.down.property).trans (range_average lo hi d).le

@[gen_rule]
theorem average_binary_le {t e c d : ℝ≥0∞} (ht : t ≤ c) (he : e ≤ d) :
    (Mix.average.{u}).binary t e ≤ (1/2 : ℝ≥0∞) * c + (1/2 : ℝ≥0∞) * d := by
  refine (average_mix_mono (F' := fun a => if (a.down.val == 0) = true then c else d)
    fun a => ?_).trans ((binary_average _).trans ?_).le
  · split <;> assumption
  · simp

@[gen_rule]
theorem average_threshold_le {d : Nat} {k : ℤ} {t e c c' : ℝ≥0∞} (hd : 0 < d) (h0 : 0 ≤ k)
    (hk : k ≤ d) (ht : t ≤ c) (he : e ≤ c') :
    (Mix.average.{u}).threshold d k t e
      ≤ (k.toNat : ℝ≥0∞) / (d : ℝ≥0∞) * c + ((d - k.toNat : ℕ) : ℝ≥0∞) / (d : ℝ≥0∞) * c' := by
  refine (average_mix_mono (F' := fun a => if (a.down.val : ℤ) < k then c else c')
    fun a => ?_).trans (threshold_average hd h0 hk c c').le
  split <;> assumption

private theorem sum_map_le {γ : Type v} {F : γ → ℝ≥0∞} {cs : List ℝ≥0∞} {l : List γ}
    (h : List.Forall₂ (fun c g => F g ≤ c) cs l) : (l.map F).sum ≤ cs.sum := by
  induction h with
  | nil => simp
  | cons hc _ ih => simpa using add_le_add hc ih

@[gen_rule]
theorem average_index_le {γ : Type v} {l : List γ} {hne : l ≠ []} {F : γ → ℝ≥0∞}
    {cs : List ℝ≥0∞} (h : List.Forall₂ (fun c g => F g ≤ c) cs l) :
    (Mix.average.{u}).index l hne F ≤ cs.sum / (cs.length : ℝ≥0∞) := by
  rw [h.length_eq]
  exact (index_average l hne F).le.trans (ENNReal.div_le_div_right (sum_map_le h) _)

/-- The fallback for a list that is not a literal, whose entries cannot be bounded one by one. -/
@[gen_rule]
theorem average_index_le_map {γ : Type v} {l : List γ} {hne : l ≠ []} {F : γ → ℝ≥0∞} :
    (Mix.average.{u}).index l hne F ≤ (l.map F).sum / (l.length : ℝ≥0∞) :=
  (index_average l hne F).le

/-- Branch-wise upper bounds for a weighted choice, each paired with its weight, so that the bound
computed from them is free of the branches themselves. -/
@[gen_branches]
inductive WeightedLE {γ : Type v} (F : γ → ℝ≥0∞) : List (Nat × ℝ≥0∞) → List (Nat × γ) → Prop
  | nil : WeightedLE F [] []
  | cons {w : Nat} {c : ℝ≥0∞} {g : γ} {cs gs} (h : F g ≤ c) (hs : WeightedLE F cs gs) :
      WeightedLE F ((w, c) :: cs) ((w, g) :: gs)

theorem WeightedLE.weights {γ : Type v} {F : γ → ℝ≥0∞} {cs gs} (h : WeightedLE F cs gs) :
    (cs.map Prod.fst).sum = (gs.map Prod.fst).sum := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simpa using ih

theorem WeightedLE.sum_le {γ : Type v} {F : γ → ℝ≥0∞} {cs gs} (h : WeightedLE F cs gs) :
    (gs.map fun p => (p.1 : ℝ≥0∞) * F p.2).sum ≤ (cs.map fun p => (p.1 : ℝ≥0∞) * p.2).sum := by
  induction h with
  | nil => simp
  | cons hc _ ih => simpa using add_le_add (by gcongr) ih

@[gen_rule]
theorem average_select_le {γ : Type v} {l : List (Nat × γ)} {hpos : 0 < (l.map Prod.fst).sum}
    {F : γ → ℝ≥0∞} {d : ℝ≥0∞} {cs : List (Nat × ℝ≥0∞)} (h : WeightedLE F cs l) :
    (Mix.average.{u}).select l hpos F d
      ≤ (cs.map fun p => (p.1 : ℝ≥0∞) * p.2).sum / ((cs.map Prod.fst).sum : ℝ≥0∞) := by
  rw [h.weights]
  refine (select_average (l.map fun p => (p.1, F p.2)) (by simp [Function.comp_def]) hpos d).le.trans
    ?_
  rw [List.map_map]
  exact ENNReal.div_le_div_right h.sum_le _

@[gen_rule]
theorem average_rangeInt_le {lo hi : ℤ} {h : lo ≤ hi} {F d : ℤ → ℝ≥0∞}
    (hF : ∀ x, lo ≤ x ∧ x ≤ hi → F x ≤ d x) :
    (Mix.average.{0}).rangeInt lo hi h F
      ≤ (∑ x ∈ Finset.Icc lo hi, d x) / (((hi - lo + 1).toNat : ℕ) : ℝ≥0∞) := by
  refine (average_mix_mono fun a => hF _ ⟨by omega, ?_⟩).trans ?_
  · have := a.down.property.2
    omega
  · exact ((congrFun (SPMF.expectObs.map_chooseInt lo hi h) d).symm.trans
      (SPMF.expect_chooseInt h d)).le

end Mix

/-! ## Leaves

A fact bounds a sub-generator's expectation under its own postexpectation `h`; the walk arrives with
`k + h`, and the missing mass only helps. -/

theorem SPMF.spec_le_add_of_expect_le {x : SPMF α} {h p : α → ℝ≥0∞} {k B : ℝ≥0∞}
    (hx : SPMF.expect x h ≤ B) (hp : ∀ a, p a = k + h a) : SPMF.expectObs.spec x p ≤ k + B := by
  show SPMF.expect x p ≤ k + B
  rw [funext hp, SPMF.expect_add, SPMF.expect_const]
  exact add_le_add (mul_le_of_le_one_left' (SPMF.mass_le_one x)) hx

theorem SPMF.Cost.spec_le_add_of_expect_le {x : SPMF.Cost α} {φ : α × Nat → ℝ≥0∞}
    {h p : α → Nat → ℝ≥0∞} {k B : ℝ≥0∞} (hx : SPMF.expect x φ ≤ B)
    (hφ : ∀ a n, φ (a, n) = h a n) (hp : ∀ a n, p a n = k + h a n) :
    SPMF.Cost.expectObs.spec x p ≤ k + B := by
  show SPMF.expect x (fun q => p q.1 q.2) ≤ k + B
  have hp' : (fun q : α × Nat => p q.1 q.2) = fun q => k + φ q :=
    funext fun q => by rw [hp, ← hφ]
  rw [hp', SPMF.expect_add, SPMF.expect_const]
  exact add_le_add (mul_le_of_le_one_left' (SPMF.mass_le_one x)) hx

namespace Basalt.ExpectBound

open Basalt.Walk

/-- `goal`, with metavariables instantiated and projections out of constructors reduced. -/
def tidy (goal : MVarId) : MetaM MVarId := goal.withContext do
  goal.setTag .anonymous
  goal.replaceTargetDefEq (← reduceCtorProjs (← goal.getType))

/-- Walk `goal`, `SPMF.expect g f ≤ B` at either interpretation, returning the arithmetic goal
`b ≤ B` for the bound `b` the walk computes, then whatever else the walk left. -/
def walkExpect (extras : Array Term) (goal : MVarId) : TermElabM (List MVarId) :=
  goal.withContext do
  let ty ← whnfR (← instantiateMVars (← goal.getType))
  let bad := m!"expect_bound: expected a goal `SPMF.expect (gen …) f ≤ B`, got{indentExpr ty}"
  unless ty.isAppOfArity ``LE.le 4 do throwError bad
  let mut lhs := ty.getArg! 2
  if lhs.isAppOf ``SPMF.Cost.expectedCost then
    lhs := ((← unfoldDefinition? lhs).getD lhs).headBeta
  unless lhs.isAppOfArity ``SPMF.expect 3 do throwError bad
  let g := lhs.getArg! 1
  let f := lhs.getArg! 2
  let gTy ← instantiateMVars (← inferType g)
  let (obs, post) ← if gTy.isAppOfArity ``SPMF.Cost 1 then do
      let (v, n) := match f with
        | .lam v _ _ _ => (v.eraseMacroScopes, Name.mkSimple s!"n_{v.eraseMacroScopes}")
        | _ => (`a, `n)
      let post ← withLocalDeclD v gTy.appArg! fun a => withLocalDeclD n (mkConst ``Nat) fun c => do
        mkLambdaFVars #[a, c] (← reduceCtorProjs (mkApp f (← mkAppM ``Prod.mk #[a, c])))
      pure (``SPMF.Cost.expectObs, post)
    else pure (``SPMF.expectObs, f)
  let spec := mkApp (← mkAppOptM ``Obs.spec
    #[none, none, none, none, none, none, some (mkConst obs [← getDecLevel gTy]), none, some g]) post
  unless ← isDefEq spec lhs do throwError bad
  let le := ty.appFn!.appFn!
  let bound ← mkFreshExprMVar (ty.getArg! 0)
  let structural ← mkFreshExprMVar (mkApp2 le spec bound)
  let rest ← walk extras structural.mvarId!
  let arith ← mkFreshExprMVar (mkApp2 le (← instantiateMVars bound) (ty.getArg! 3))
  goal.assign (← mkAppM ``le_trans #[structural, arith])
  (arith.mvarId! :: rest).mapM fun g => tidy g

/-- `expect_bound` replaces a goal `SPMF.expect (gen …) f ≤ B`, at `SPMF` or `SPMF.Cost` (where
`SPMF.Cost.expectedCost` is also accepted), by the `ℝ≥0∞` inequality `b ≤ B`, where `b` is the bound
it computes by pushing `f` through `gen`'s syntax. A recursive occurrence or a callee is bounded by a
hypothesis or by a fact passed as `expect_bound [h₁, h₂]`, stated under a postexpectation that
differs from the one the walk arrives with by a constant. -/
syntax (name := expectBoundTac) "expect_bound" (" [" term,* "]")? : tactic

elab_rules : tactic
  | `(tactic| expect_bound $[[$args,*]]?) => withMainContext do
    replaceMainGoal (← walkExpect ((args.map (·.getElems)).getD #[]) (← getMainGoal))

end Basalt.ExpectBound
