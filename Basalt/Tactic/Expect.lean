/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt.SPMF.Cost
import Basalt.Tactic.Average
import Basalt.Walk.Entry

/-!
# Computing Expectation Upper Bounds

`expect_bound` pushes a postexpectation through a generator with the rules of
`Basalt/Obs/Ordered.lean` and `Basalt/Tactic/Average.lean`, and computes an upper bound on its
expectation, leaving `ℝ≥0∞` arithmetic; `expect_fixpoint` first inducts over a recursive generator's
fixpoint. What is specific to the judgment is here: how a fact about a sub-generator is used.
-/

open ENNReal RandomChoice Lean Meta Elab Tactic

/-! ## Leaves

A fact bounds a sub-generator's expectation under its own postexpectation `h`; the walk arrives with
`k + h`, and the missing mass only helps. -/

@[obs_leaf]
theorem SPMF.expect_le_add_of_le {x : SPMF α} {h p : α → ℝ≥0∞} {k B : ℝ≥0∞}
    (hx : SPMF.expect x h ≤ B) (hp : ∀ a, p a = k + h a) : SPMF.expectObs.spec x p ≤ k + B := by
  show SPMF.expect x p ≤ k + B
  rw [funext hp, SPMF.expect_add, SPMF.expect_const]
  exact add_le_add (mul_le_of_le_one_left' (SPMF.mass_le_one x)) hx

@[obs_leaf]
theorem SPMF.Cost.expect_le_add_of_le {x : SPMF.Cost α} {φ : α × Nat → ℝ≥0∞}
    {h p : α → Nat → ℝ≥0∞} {k B : ℝ≥0∞} (hx : SPMF.expect x φ ≤ B)
    (hφ : ∀ a n, φ (a, n) = h a n) (hp : ∀ a n, p a n = k + h a n) :
    SPMF.Cost.expectObs.spec x p ≤ k + B := by
  show SPMF.expect x (fun q => p q.1 q.2) ≤ k + B
  have hp' : (fun q : α × Nat => p q.1 q.2) = fun q => k + φ q :=
    funext fun q => by rw [hp, ← hφ]
  rw [hp', SPMF.expect_add, SPMF.expect_const]
  exact add_le_add (mul_le_of_le_one_left' (SPMF.mass_le_one x)) hx

/-! ## The list combinators

A list combinator has no shape of choice for the walk to enter, so its rules here use only its
mass: exactly when the postexpectation is constant, and otherwise at its worst case over every
value, dually to `le_expect_iInf_of_le_mass` on the mass side. A rule that reads the element
generator's expectation is declared before these, and wins. -/

namespace SPMF

/-- What the missing mass buys: an expectation is at most its postexpectation's largest value,
whatever the generator. -/
theorem expect_le_of_const {x : SPMF α} {p : α → ℝ≥0∞} {d : ℝ≥0∞} (hp : ∀ a, p a = d) :
    SPMF.expectObs.spec x p ≤ d :=
  SPMF.expect_le_of_support fun a _ => (hp a).le

@[inherit_doc expect_le_of_const]
theorem expect_le_iSup {x : SPMF α} {p : α → ℝ≥0∞} : SPMF.expectObs.spec x p ≤ ⨆ a, p a :=
  SPMF.expect_le_of_support fun a _ => le_iSup p a

section listCombinators

variable {α : Type} {g : SPMF α} {p : List α → ℝ≥0∞} {d : ℝ≥0∞}

@[gen_rule] theorem expect_vectorOf_le_const {n : Nat} (hp : ∀ a, p a = d) :
    expectObs.spec (vectorOf n g) p ≤ d := expect_le_of_const hp

@[gen_rule] theorem expect_vectorOf_le_iSup {n : Nat} :
    expectObs.spec (vectorOf n g) p ≤ ⨆ a, p a := expect_le_iSup

@[gen_rule] theorem expect_listOfMaxLength_le_const {n : Nat} (hp : ∀ a, p a = d) :
    expectObs.spec (listOfMaxLength n g) p ≤ d := expect_le_of_const hp

@[gen_rule] theorem expect_listOfMaxLength_le_iSup {n : Nat} :
    expectObs.spec (listOfMaxLength n g) p ≤ ⨆ a, p a := expect_le_iSup

@[gen_rule] theorem expect_listOf_le_const (hp : ∀ a, p a = d) :
    expectObs.spec (listOf g) p ≤ d := expect_le_of_const hp

@[gen_rule] theorem expect_listOf_le_iSup : expectObs.spec (listOf g) p ≤ ⨆ a, p a :=
  expect_le_iSup

@[gen_rule] theorem expect_nonEmptyListOf_le_const (hp : ∀ a, p a = d) :
    expectObs.spec (nonEmptyListOf g) p ≤ d := expect_le_of_const hp

@[gen_rule] theorem expect_nonEmptyListOf_le_iSup :
    expectObs.spec (nonEmptyListOf g) p ≤ ⨆ a, p a := expect_le_iSup

end listCombinators

@[gen_rule] theorem expect_permutationOf_le_const {xs : List α}
    {p : { ys // xs.Perm ys } → ℝ≥0∞} {d : ℝ≥0∞} (hp : ∀ a, p a = d) :
    expectObs.spec (permutationOf xs) p ≤ d := expect_le_of_const hp

@[gen_rule] theorem expect_permutationOf_le_iSup {xs : List α}
    {p : { ys // xs.Perm ys } → ℝ≥0∞} : expectObs.spec (permutationOf xs) p ≤ ⨆ a, p a :=
  expect_le_iSup

end SPMF

/-! ## The cost interpretation

`vectorOf` draws a bounded number of times, so its expected cost is read off the element generator's
and its rule is exact. The other list combinators have only the last resorts below, which at the
postexpectation `expectedCost` uses are `⊤`; pass a bound to `expect_bound [h]`. For
`listOfMaxLength` an exact rule is `expectedCost_vectorOf_le` averaged over the length drawn, which
its `do` block presents as a `match` on the subtype rather than as a `chooseNat` bind. -/

namespace SPMF.Cost

variable {α : Type} {g : SPMF.Cost α} {b k d : ℝ≥0∞} {p : List α → Nat → ℝ≥0∞}

/-- A bind that only relabels the value makes no further choices. -/
private theorem expectedCost_bind_pure (x : SPMF.Cost α) (h : α → β) :
    expectedCost (x >>= fun a => Pure.pure (h a) : SPMF.Cost β) = expectedCost x := by
  unfold expectedCost
  rw [expect_bind]
  simp only [expect_pure, Nat.add_zero]

private theorem expectedCost_vectorOf_le {n : Nat} (hg : expectedCost g ≤ b) :
    expectedCost (vectorOf n g : SPMF.Cost (List α)) ≤ n * b := by
  induction n with
  | zero =>
    show SPMF.expect (Pure.pure [] : SPMF.Cost (List α)) _ ≤ _
    rw [expect_pure]
    simp
  | succ n ih =>
    rw [vectorOf_succ]
    show SPMF.expect (g >>= _ : SPMF.Cost (List α)) (fun q => (q.2 : ℝ≥0∞)) ≤ _
    rw [expect_bind]
    have hinner : ∀ q : α × Nat,
        SPMF.expect (vectorOf n g >>= fun xs => Pure.pure (q.1 :: xs) : SPMF.Cost (List α))
            (fun r => ((q.2 + r.2 : Nat) : ℝ≥0∞))
          ≤ (q.2 : ℝ≥0∞) + n * b := by
      intro q
      have hcast : (fun r : List α × Nat => ((q.2 + r.2 : Nat) : ℝ≥0∞))
          = fun r => (q.2 : ℝ≥0∞) + (r.2 : ℝ≥0∞) := by funext r; push_cast; rfl
      rw [hcast, SPMF.expect_add, SPMF.expect_const]
      refine add_le_add ?_ ((expectedCost_bind_pure _ _).trans_le ih)
      exact mul_le_of_le_one_left' (SPMF.mass_le_one _)
    refine (SPMF.expect_mono hinner).trans ?_
    rw [SPMF.expect_add, SPMF.expect_const]
    refine (add_le_add hg (mul_le_of_le_one_left' (SPMF.mass_le_one g))).trans ?_
    push_cast
    rw [add_mul, one_mul, add_comm]

/-- The only rule that reads the element generator's expected cost; the last resorts below apply
when it does not. -/
@[gen_rule]
theorem expect_vectorOf_le {n : Nat}
    (hg : SPMF.Cost.expectObs.spec g (fun _ m => (m : ℝ≥0∞)) ≤ b)
    (hp : ∀ a m, p a m = k + (m : ℝ≥0∞)) :
    SPMF.Cost.expectObs.spec (vectorOf n g) p ≤ k + n * b := by
  show SPMF.expect (vectorOf n g : SPMF.Cost (List α)) (fun q => p q.1 q.2) ≤ _
  rw [funext fun q : List α × Nat => hp q.1 q.2, SPMF.expect_add, SPMF.expect_const]
  exact add_le_add (mul_le_of_le_one_left' (SPMF.mass_le_one _))
    (expectedCost_vectorOf_le hg)

/-! The rules that use only the mass, as at `SPMF`. -/

/-- As `SPMF.expect_le_of_const`, with the choice count in the postexpectation. -/
theorem expect_le_of_const {x : SPMF.Cost α} {q : α → Nat → ℝ≥0∞} (hq : ∀ a m, q a m = d) :
    SPMF.Cost.expectObs.spec x q ≤ d :=
  SPMF.expect_le_of_support fun r _ => (hq r.1 r.2).le

@[inherit_doc expect_le_of_const]
theorem expect_le_iSup {x : SPMF.Cost α} {q : α → Nat → ℝ≥0∞} :
    SPMF.Cost.expectObs.spec x q ≤ ⨆ a, ⨆ m, q a m :=
  SPMF.expect_le_of_support fun r _ => le_iSup₂_of_le r.1 r.2 le_rfl

@[gen_rule] theorem expect_vectorOf_le_const {n : Nat} (hp : ∀ a m, p a m = d) :
    expectObs.spec (vectorOf n g) p ≤ d := expect_le_of_const hp

@[gen_rule] theorem expect_vectorOf_le_iSup {n : Nat} :
    expectObs.spec (vectorOf n g) p ≤ ⨆ a, ⨆ m, p a m := expect_le_iSup

@[gen_rule] theorem expect_listOfMaxLength_le_const {n : Nat} (hp : ∀ a m, p a m = d) :
    expectObs.spec (listOfMaxLength n g) p ≤ d := expect_le_of_const hp

@[gen_rule] theorem expect_listOfMaxLength_le_iSup {n : Nat} :
    expectObs.spec (listOfMaxLength n g) p ≤ ⨆ a, ⨆ m, p a m := expect_le_iSup

@[gen_rule] theorem expect_listOf_le_const (hp : ∀ a m, p a m = d) :
    expectObs.spec (listOf g) p ≤ d := expect_le_of_const hp

@[gen_rule] theorem expect_listOf_le_iSup :
    expectObs.spec (listOf g) p ≤ ⨆ a, ⨆ m, p a m := expect_le_iSup

@[gen_rule] theorem expect_nonEmptyListOf_le_const (hp : ∀ a m, p a m = d) :
    expectObs.spec (nonEmptyListOf g) p ≤ d := expect_le_of_const hp

@[gen_rule] theorem expect_nonEmptyListOf_le_iSup :
    expectObs.spec (nonEmptyListOf g) p ≤ ⨆ a, ⨆ m, p a m := expect_le_iSup

@[gen_rule] theorem expect_permutationOf_le_const {xs : List α}
    {q : { ys // xs.Perm ys } → Nat → ℝ≥0∞} (hq : ∀ a m, q a m = d) :
    expectObs.spec (permutationOf xs) q ≤ d := expect_le_of_const hq

@[gen_rule] theorem expect_permutationOf_le_iSup {xs : List α}
    {q : { ys // xs.Perm ys } → Nat → ℝ≥0∞} :
    expectObs.spec (permutationOf xs) q ≤ ⨆ a, ⨆ m, q a m := expect_le_iSup

end SPMF.Cost

namespace Basalt.ExpectBound

open Basalt.Walk

/-- `goal`, an expectation bound at either interpretation, with `SPMF.Cost.expectedCost` unfolded:
the generator, the postexpectation, the bound, and the goal restated in that form. `tac` is the
caller, for the error. -/
def parseExpect (tac : String) (goal : MVarId) :
    MetaM (Expr × Expr × Expr × MVarId) := goal.withContext do
  let ty ← whnfR (← instantiateMVars (← goal.getType))
  let bad := m!"{tac}: expected a goal `SPMF.expect (gen …) f ≤ B`, got{indentExpr ty}"
  unless ty.isAppOfArity ``LE.le 4 do throwError bad
  let mut lhs := ty.getArg! 2
  if lhs.isAppOf ``SPMF.Cost.expectedCost then
    lhs := ((← unfoldDefinition? lhs).getD lhs).headBeta
  unless lhs.isAppOfArity ``SPMF.expect 3 do throwError bad
  let goal ← if lhs == ty.getArg! 2 then pure goal
    else goal.change (mkApp2 ty.appFn!.appFn! lhs (ty.getArg! 3))
  return (lhs.getArg! 1, lhs.getArg! 2, ty.getArg! 3, goal)

/-- Walk `goal`, `SPMF.expect g f ≤ B` at either interpretation, returning the arithmetic goal
`b ≤ B` for the bound `b` the walk computes, then whatever else the walk left. `tac` is the caller,
for the errors. -/
partial def walkExpect (tac : String) (extras : Array Term) (goal : MVarId) :
    TermElabM (List MVarId) := do
  let (g, f, B, goal) ← parseExpect tac goal
  goal.withContext do
  if let some cases ← splitMatch? goal g then return ← cases.flatMapM (walkExpect tac extras)
  let gTy ← instantiateMVars (← inferType g)
  let (obs, post) ← if gTy.isAppOfArity ``SPMF.Cost 1 then do
      let (v, n) := match f with
        | .lam v _ _ _ => (v.eraseMacroScopes, Name.mkSimple s!"n_{v.eraseMacroScopes}")
        | _ => (`a, `n)
      let post ← withLocalDeclD v gTy.appArg! fun a => withLocalDeclD n (mkConst ``Nat) fun c => do
        mkLambdaFVars #[a, c] (← reduceCtorProjs (mkApp f (← mkAppM ``Prod.mk #[a, c])))
      pure (``SPMF.Cost.expectObs, post)
    else pure (``SPMF.expectObs, f)
  arithBound extras obs false g post B goal

/-- `expect_bound` replaces a goal `SPMF.expect (gen …) f ≤ B`, at `SPMF` or `SPMF.Cost` (where
`SPMF.Cost.expectedCost` is also accepted), by the `ℝ≥0∞` inequality `b ≤ B`, where `b` is the bound
it computes by pushing `f` through `gen`'s syntax. A recursive occurrence or a callee is bounded by a
hypothesis or by a fact passed as `expect_bound [h₁, h₂]`, stated under a postexpectation that
differs from the one the walk arrives with by a constant. -/
syntax (name := expectBoundTac) "expect_bound" (walkFacts)? : tactic

elab_rules : tactic
  | `(tactic| expect_bound $[$fs]?) => withMainContext do
    replaceMainGoal (← walkExpect "expect_bound" (walkFacts.terms fs) (← getMainGoal))

/-- `expect_fixpoint` proves `SPMF.expect (gen a₁ … aₙ) f ≤ B`, at `SPMF` or `SPMF.Cost`, up to
arithmetic. It inducts with `gen.fixpoint_induct` over the arguments some recursive call of `gen`
changes, admissible because `SPMF.expect` is continuous, unfolds one step, and runs `expect_bound`
(extra facts go in `expect_fixpoint [h₁, h₂]`). The first goal is the arithmetic one; in it the
recursive function is named after `gen`, the bound on its every call is `ih`, and the changing
arguments keep their names. Only an upper bound can be proved this way. -/
syntax (name := expectFixpointTac) "expect_fixpoint" (walkFacts)? : tactic

elab_rules : tactic
  | `(tactic| expect_fixpoint $[$fs]?) => withMainContext do
    let (x, f, B, goal) ← parseExpect "expect_fixpoint" (← getMainGoal)
    goal.withContext do
    let adm ← mkAppM ``SPMF.admissible_expect_le #[f, B]
    replaceMainGoal (← walkExpect "expect_fixpoint" (walkFacts.terms fs)
      (← fixpointStep "expect_fixpoint" "expect_bound" x adm goal))

end Basalt.ExpectBound
