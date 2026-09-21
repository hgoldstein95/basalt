/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt.SPMF.Cost
import Basalt.SPMF.AverageBound
import Basalt.SPMF.Walk

/-!
# Computing Expectation Upper Bounds

`expect_bound` pushes a postexpectation through a generator with the rules of
`Basalt/Obs/Ordered.lean` and `Basalt/SPMF/AverageBound.lean`, and computes an upper bound on its
expectation, leaving `ℝ≥0∞` arithmetic. What is specific to the judgment is here: how a fact about
a sub-generator is used.
-/

open ENNReal RandomChoice Lean Meta Elab Tactic

instance : SPMF.Cost.expectObs.MonotoneC := ⟨fun _ _ _ h => SPMF.expect_mono fun p => h p.1 p.2⟩

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
