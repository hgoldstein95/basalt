/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt.SPMF.Termination
import Basalt.SPMF.MassBound.Attr

/-!
# Computing Mass Lower Bounds

The structural half of a termination proof: `mass_bound` walks a generator's syntax and *computes* a
lower bound on its mass from the `@[mass_bound]` rules, leaving a goal that is pure `ℝ≥0∞`
arithmetic. Every combinator in `Combinators.lean` needs a rule here, in the shape `Attr.lean`
describes, or the walk stops at it.
-/

open ENNReal RandomChoice Lean Meta Elab Tactic

namespace SPMF

/-! ## The rules

One per combinator. Each says: given a lower bound on every sub-generator's mass, here is the lower
bound on this combinator's. `mass_bound` chains them, so the bounds are metavariables when the rule
is applied and the conclusion is what *computes* the answer. -/

/-- Chaining rule: a known-terminating callee contributes `1`. Also the bridge the `mass_bound`
tactic uses for a `<callee>.terminates` law it finds by name. -/
theorem le_mass_of_isPMF {x : SPMF α} (h : IsPMF x) : (1 : ℝ≥0∞) ≤ x.mass := h.ge

/-- Bound a sub-generator by its own mass rather than by a constant: `mass_bound [le_mass_self]` is
what the ranking regime wants, where the bound being proved is itself a function of the seed. -/
theorem le_mass_self {x : SPMF α} : x.mass ≤ x.mass := le_rfl

@[mass_bound]
theorem le_mass_pure {a : α} : (1 : ℝ≥0∞) ≤ (Pure.pure a : SPMF α).mass := (mass_pure a).ge

@[mass_bound]
theorem le_mass_bind {x : SPMF α} {f : α → SPMF β} {c d : ℝ≥0∞}
    (hx : c ≤ x.mass) (hf : ∀ a, d ≤ (f a).mass) : c * d ≤ (x >>= f).mass :=
  mass_bind_ge_mul hx hf

@[mass_bound]
theorem le_mass_map {x : SPMF α} {f : α → β} {c : ℝ≥0∞} (hx : c ≤ x.mass) :
    c ≤ (f <$> x).mass := by rw [mass_map]; exact hx

@[mass_bound]
theorem le_mass_pick {x y : Unit → SPMF α} {c d : ℝ≥0∞}
    (hx : c ≤ (x ()).mass) (hy : d ≤ (y ()).mass) :
    (1/2 : ℝ≥0∞) * c + (1/2 : ℝ≥0∞) * d ≤ (pick x y).mass := by
  rw [show pick x y = pick (fun () => x ()) (fun () => y ()) from rfl, mass_pick]
  gcongr

/-- A conditional's branches need not have the same bound, so the rule takes their `min`: in a
generator that shortcuts on an exhausted seed, the shortcut and the recursive branch never do. -/
@[mass_bound]
theorem le_mass_ite {p : Prop} [Decidable p] {x y : SPMF α} {c d : ℝ≥0∞}
    (hx : p → c ≤ x.mass) (hy : ¬p → d ≤ y.mass) : min c d ≤ (if p then x else y).mass := by
  split
  · exact (min_le_left _ _).trans (by simp_all)
  · exact (min_le_right _ _).trans (by simp_all)

@[mass_bound]
theorem le_mass_dite {p : Prop} [Decidable p] {x : p → SPMF α} {y : ¬p → SPMF α} {c d : ℝ≥0∞}
    (hx : ∀ h, c ≤ (x h).mass) (hy : ∀ h, d ≤ (y h).mass) :
    min c d ≤ (if h : p then x h else y h).mass := by
  split
  · exact (min_le_left _ _).trans (by simp_all)
  · exact (min_le_right _ _).trans (by simp_all)

@[mass_bound]
theorem le_mass_choose {lo hi : Nat} {h : lo ≤ hi} :
    (1 : ℝ≥0∞) ≤ (choose lo hi h : SPMF (ULift {x : Nat // lo ≤ x ∧ x ≤ hi})).mass :=
  (mass_choose lo hi h).ge

@[mass_bound]
theorem le_mass_chooseNat {lo hi : Nat} {h : lo ≤ hi} :
    (1 : ℝ≥0∞) ≤ (chooseNat lo hi h : SPMF Nat).mass := (mass_chooseNat lo hi h).ge

@[mass_bound]
theorem le_mass_chooseInt {lo hi : Int} {h : lo ≤ hi} :
    (1 : ℝ≥0∞) ≤ (chooseInt lo hi h : SPMF Int).mass := (mass_chooseInt lo hi h).ge

@[mass_bound]
theorem le_mass_coin {r : Rat} : (1 : ℝ≥0∞) ≤ (coin r : SPMF Bool).mass := IsPMF_coin.ge

@[mass_bound]
theorem le_mass_elements [Inhabited α] {xs : List α} {hne : xs ≠ []} :
    (1 : ℝ≥0∞) ≤ (elements xs hne : SPMF α).mass := (IsPMF_elements xs hne).ge

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
@[mass_bound]
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

@[mass_bound]
theorem le_mass_frequency {gs : List (Nat × (Unit → SPMF α))}
    {hw : 0 < (gs.map Prod.fst).sum} {cs : List (Nat × ℝ≥0∞)}
    (h : WeightedBounds cs gs) :
    (cs.map fun p => (p.1 : ℝ≥0∞) * p.2).sum / ((cs.map Prod.fst).sum : ℝ≥0∞)
      ≤ (frequency gs hw : SPMF α).mass := by
  rw [mass_frequency hw, h.weights]
  exact ENNReal.div_le_div_right h.sum_le _

end SPMF

namespace Basalt.MassBound

/-- The bounds a rule computes are metavariables that its hypotheses determine, so `apply` must hand
back only the hypotheses. -/
private def applyCfg : ApplyConfig := { newGoals := .nonDependentOnly }

/-- Close `goal` outright with `e`, or with `e` read as an `IsPMF`/`IsAlmostSurelyTerminating` law. -/
private def tryFact (goal : MVarId) (e : Expr) : MetaM Bool := do
  for cand in [e, (← observing? (mkAppM ``SPMF.le_mass_of_isPMF #[e])).getD e] do
    if (← observing? do
          let gs ← goal.apply cand applyCfg
          unless gs.isEmpty do failure).isSome then
      return true
  return false

/-- The generator `g`'s own termination law, under the `<gen>.terminates` naming convention. -/
private def terminatesLaw? (g : Expr) : MetaM (Option Expr) := do
  let some head := g.getAppFn.constName? | return none
  unless (← getEnv).contains (head ++ `terminates) do return none
  return some (← mkConstWithFreshMVarLevels (head ++ `terminates))

mutual

/-- Bound the mass of the generator in `goal` below, recursing into its sub-generators. `extras`
are the facts the caller passed; they stay syntax because one may be used at several
sub-generators, and elaborating once would freeze its metavariables at the first. -/
partial def chain (extras : Array Term) (goal : MVarId) : TermElabM Unit := goal.withContext do
  let ty ← whnfR (← instantiateMVars (← goal.getType))
  -- A rule's hypothesis may be a `∀` (a bind's continuation, an `ite`'s branch condition).
  if ty.isForall then
    let (_, goal) ← goal.intro1P
    return ← chain extras goal
  if ty.isAppOfArity ``LE.le 4 then
    let rhs ← whnfR (ty.getArg! 3)
    if rhs.isAppOfArity ``SPMF.mass 2 then
      return ← bound extras goal ty rhs (rhs.getArg! 1)
  -- The branch bounds of a list combinator, built one branch at a time: any `nil`/`cons` relation
  -- whose last argument is the combinator's branch list.
  if let some head := ty.getAppFn.constName? then
    if (← getEnv).contains (head ++ `cons) && (← getEnv).contains (head ++ `nil) then
      let ctor := if (← whnfR ty.appArg!).isAppOfArity ``List.nil 1 then `nil else `cons
      for goal in ← goal.apply (← mkConstWithFreshMVarLevels (head ++ ctor)) applyCfg do
        chain extras goal
      return
  throwError "mass_bound: expected `_ ≤ SPMF.mass _`, got{indentExpr ty}"

/-- The `_ ≤ SPMF.mass g` case of `chain`: a rule for `g`'s combinator, or `g` is a leaf. -/
partial def bound (extras : Array Term) (goal : MVarId) (ty rhs g : Expr) :
    TermElabM Unit := goal.withContext do
  -- The reductions cover a branch that is still a redex or a projection (`(fun () => …) ()`,
  -- `p.2 ()`); no combinator is reducible, so no reduction can turn one combinator into another.
  -- The goal is rewritten to the reduced form before the rule is applied: matching a rule against
  -- an unreduced branch closes a side condition like `xs ≠ []` by proof irrelevance rather than by
  -- unification, and the side condition then survives as a goal.
  let rules := massBoundExt.getState (← getEnv)
  let rule? (e : Expr) := e.getAppFn.constName?.bind rules.find?
  for g' in [g, ← whnfCore g, ← whnfR g] do
    if let some lem := rule? g' then
      let goal ← if g' == g then pure goal else goal.change (ty.appFn!.app (rhs.appFn!.app g'))
      for goal in ← goal.apply (← mkConstWithFreshMVarLevels lem) applyCfg do
        chain extras goal
      return
  -- A leaf: a caller-supplied fact, a hypothesis (the recursive call's bound), or a proved law.
  for t in extras do
    let used ← observing? do
      let e ← Term.elabTerm t none
      unless ← tryFact goal e do failure
    if used.isSome then return
  for decl in ← getLCtx do
    unless decl.isImplementationDetail do
      if ← tryFact goal decl.toExpr then return
  if let some law ← terminatesLaw? g then
    if ← tryFact goal law then return
  throwError "mass_bound: no rule, hypothesis, or `.terminates` law bounds the mass \
    of{indentExpr g}\nTag a lower bound for it `@[mass_bound]`, or pass one to `mass_bound [_]`."

end

/-- `mass_bound` replaces a goal `c ≤ (gen …).mass` by the `ℝ≥0∞` inequality `c ≤ b`, where `b` is
the bound it computes by walking `gen`'s syntax with the `@[mass_bound]` rules. Recursive
occurrences are closed from the local context, callees from their `.terminates` law; any other fact
can be passed as `mass_bound [h₁, h₂]`. Unfold one step of the recursion *before* calling it. -/
syntax (name := massBoundTac) "mass_bound" (" [" term,* "]")? : tactic

elab_rules : tactic
  | `(tactic| mass_bound $[[$args,*]]?) => withMainContext do
    let goal ← getMainGoal
    let ty ← whnfR (← goal.getType)
    unless ty.isAppOfArity ``LE.le 4 do
      throwError "mass_bound: expected a goal `_ ≤ (gen …).mass`, got{indentExpr ty}"
    let bound ← mkFreshExprMVar (mkConst ``ENNReal)
    let structural ← mkFreshExprMVar (← mkAppM ``LE.le #[bound, ty.getArg! 3])
    chain ((args.map (·.getElems)).getD #[]) structural.mvarId!
    let arith ← mkFreshExprMVar (← mkAppM ``LE.le #[ty.getArg! 2, ← instantiateMVars bound])
    goal.assign (← mkAppM ``le_trans #[arith, structural])
    replaceMainGoal [arith.mvarId!]

end Basalt.MassBound
