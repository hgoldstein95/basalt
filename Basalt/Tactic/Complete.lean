/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt.Laws
import Basalt.Walk.Entry

/-!
# Walking Completeness

The structural half of a completeness proof. `a ∈ SPMF.support g` is a lower bound on `SPMF.mayObs`
at the postcondition `(· = a)`, in the angelic algebra, so `complete_bound` computes a precondition
for reaching `a`: an `∃` for each draw and an `∨` for each choice. A lower bound on a least fixed
point needs a ranking, which is the user's induction; a recursive occurrence is therefore left in
the precondition as itself.
-/

open RandomChoice Lean Meta Elab Tactic Basalt.Walk

namespace SPMF

/-! ## Leaves -/

@[obs_leaf]
theorem le_may_of_isCompleteFor {x : SPMF α} {R p : α → Prop} (hx : IsCompleteFor x R) :
    (∃ a, R a ∧ p a) ≤ mayObs.spec x p := fun ⟨a, hR, hp⟩ => ⟨a, hx a hR, hp⟩

@[obs_leaf]
theorem le_may_of_isSoundAndComplete {x : SPMF α} {R p : α → Prop}
    (hx : IsSoundAndComplete x R) : (∃ a, R a ∧ p a) ≤ mayObs.spec x p :=
  le_may_of_isCompleteFor hx.complete

/-- The reflexive leaf: a generator nothing is known about is reached through its own support. -/
@[obs_leaf self]
theorem le_may_self {x : SPMF α} {p : α → Prop} :
    (∃ a, a ∈ x.support ∧ p a) ≤ mayObs.spec x p := fun ⟨a, ha, hp⟩ => ⟨a, ha, hp⟩

/-- The induction hypothesis of `IsCompleteFor.of_measure`, as a leaf. -/
@[obs_leaf]
theorem le_may_of_measure {σ α : Type} {gen : σ → SPMF α} {P : σ → α → Prop} {μ : σ → α → Nat}
    {n : Nat} (ih : ∀ s a, μ s a < n → P s a → a ∈ (gen s).support) (s : σ) (p : α → Prop) :
    (∃ a, (μ s a < n ∧ P s a) ∧ p a) ≤ mayObs.spec (gen s) p :=
  fun ⟨a, ⟨h1, h2⟩, hp⟩ => ⟨a, ih s a h1 h2, hp⟩

/-! ## The combinators that take a generator

They ask for the completeness of the generator, for a predicate the list's postcondition says
nothing about: a fact or a law supplies it. Each bridges the combinator's support law. -/

section generatorArgument

variable {α : Type} {g : SPMF α} {R : α → Prop} {p : List α → Prop}

@[gen_rule]
theorem le_may_vectorOf {n : Nat} (hg : IsCompleteFor g R) :
    (∃ xs, (xs.length = n ∧ ∀ x ∈ xs, R x) ∧ p xs) ≤ mayObs.spec (vectorOf n g) p :=
  fun ⟨xs, ⟨hn, hR⟩, hp⟩ =>
    ⟨xs, mem_support_vectorOf_iff.mpr ⟨hn, fun x hx => hg x (hR x hx)⟩, hp⟩

@[gen_rule]
theorem le_may_listOfMaxLength {n : Nat} (hg : IsCompleteFor g R) :
    (∃ xs, (xs.length ≤ n ∧ ∀ x ∈ xs, R x) ∧ p xs) ≤ mayObs.spec (listOfMaxLength n g) p :=
  fun ⟨xs, ⟨hn, hR⟩, hp⟩ =>
    ⟨xs, mem_support_listOfMaxLength_iff.mpr ⟨hn, fun x hx => hg x (hR x hx)⟩, hp⟩

@[gen_rule]
theorem le_may_listOf (hg : IsCompleteFor g R) :
    (∃ xs, (∀ x ∈ xs, R x) ∧ p xs) ≤ mayObs.spec (listOf g) p :=
  fun ⟨xs, hR, hp⟩ => ⟨xs, mem_support_listOf.mpr fun x hx => hg x (hR x hx), hp⟩

@[gen_rule]
theorem le_may_nonEmptyListOf (hg : IsCompleteFor g R) :
    (∃ xs, (xs ≠ [] ∧ ∀ x ∈ xs, R x) ∧ p xs) ≤ mayObs.spec (nonEmptyListOf g) p :=
  fun ⟨xs, ⟨hne, hR⟩, hp⟩ =>
    ⟨xs, mem_support_nonEmptylistOf.mpr ⟨hne, fun x hx => hg x (hR x hx)⟩, hp⟩

end generatorArgument

end SPMF

namespace SPMF.Cost

/-! ## The cost interpretation

A run with its cost, `(a, n) ∈ SPMF.support g`, is the may observation at `fun b m => b = a ∧ m = n`.
There is no law to find here, so a callee stays in the precondition as a recursive occurrence
does. -/

@[obs_leaf self]
theorem le_may_self {x : SPMF.Cost α} {p : α → Nat → Prop} :
    (∃ a n, (a, n) ∈ SPMF.support x ∧ p a n) ≤ mayObs.spec x p :=
  fun ⟨a, n, ha, hp⟩ => ⟨(a, n), ha, hp⟩

end SPMF.Cost

/-- Completeness by strong induction on a measure of seed and value, which every recursive call has
to decrease: after `apply IsCompleteFor.of_measure μ fun n ih s a hn hP => ?_`, unfolding the
generator and `complete_bound` leave a goal with no generator in it. It is `apply` that finds `gen`
and `P`, from the goal; `refine` elaborates `μ` before it knows their types. -/
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

namespace Basalt.CompleteBound

/-- Walk `goal` (see `complete_bound`), returning the pruned precondition, then whatever else the
walk left. -/
partial def walkComplete (extras : Array Term) (goal : MVarId) : TermElabM (List MVarId) := do
  let mut goal := goal
  let law ← whnfR (← instantiateMVars (← goal.getType))
  if law.isAppOfArity ``IsCompleteFor 3 then
    -- The value is named after the predicate's binder, as the walk names a drawn value.
    let v := match law.getArg! 2 with | .lam v _ _ _ => v.eraseMacroScopes | _ => `a
    let (_, g) ← goal.introN 2 [← mkFreshUserName v, ← mkFreshUserName (.mkSimple s!"h_{v}")]
    goal := g
  goal.withContext do
  let ty ← whnfR (← instantiateMVars (← goal.getType))
  let hint := if ty.isAppOf ``IsSoundAndComplete then
    m!"\nSplit the law into its halves first: `refine .intro ?sound ?complete`." else m!""
  let bad := m!"complete_bound: expected a goal `a ∈ SPMF.support (gen …)` or \
    `IsCompleteFor (gen …) P`, got{indentExpr ty}{hint}"
  unless ty.isAppOfArity ``Membership.mem 5 do throwError bad
  let support ← whnfR (ty.getArg! 3)
  unless support.isAppOfArity ``SPMF.support 2 do throwError bad
  let g := support.getArg! 1
  let a := ty.getArg! 4
  if let some cases ← splitMatch? goal g then return ← cases.flatMapM (walkComplete extras)
  -- At the cost interpretation the value is a run: what was produced, and the choices it took.
  let atCost := (← instantiateMVars (← inferType g)).isAppOfArity ``SPMF.Cost 1
  let (obs, may) ← if atCost then do
      let (v, n) ← match a.app2? ``Prod.mk with
        | some (v, n) => pure (v, n)
        | none => pure (← mkAppM ``Prod.fst #[a], ← mkAppM ``Prod.snd #[a])
      pure (``SPMF.Cost.mayObs, ← mkAppOptM ``SPMF.Cost.mem_support_iff_may #[none, g, v, n])
    else pure (``SPMF.mayObs, ← mkAppOptM ``SPMF.mem_support_iff_may #[none, g, a])
  let some (_, rhs) := (← inferType may).iff? | throwError bad
  let lctx := (← goal.getDecl).lctx
  let (pre, structural, rest) ← computeBound extras obs true g rhs.appArg!
  let paths ← mkFreshExprMVar pre
  goal.assign (← mkAppM ``Iff.mpr #[may, mkApp structural paths])
  return (← prunePaths paths.mvarId!) ++ (← rest.mapM fun g => tidy lctx g)

/-- `complete_bound` replaces a goal `a ∈ SPMF.support (gen …)` by a precondition for `gen` to
produce `a` (at `SPMF.Cost`, to produce the value `a.1` in `a.2` choices), computed by walking
`gen`'s syntax: an `∃` over each value drawn, under the generator's own names, an `∨` over each
choice, with the branches that cannot produce `a` pruned, and at the end the equation between `a`
and the value built. On `IsCompleteFor (gen …) P` it introduces the value and `P` of it first,
inaccessible. A callee is reached through its `.sound_complete` or `.complete` law, or a fact passed
as `complete_bound [h₁, h₂]`; a recursive occurrence, or a callee nothing is known about, stays as
`∃ x ∈ SPMF.support (gen …), …`, to be discharged from the hypotheses of an induction.

There is no `complete_fixpoint`: choose an induction on the value or on `P`, unfold `gen` with
`rw [gen]`, and then run this. -/
syntax (name := completeBoundTac) "complete_bound" (walkFacts)? : tactic

elab_rules : tactic
  | `(tactic| complete_bound $[$fs]?) => withMainContext do
    replaceMainGoal (← walkComplete (walkFacts.terms fs) (← getMainGoal))

end Basalt.CompleteBound
