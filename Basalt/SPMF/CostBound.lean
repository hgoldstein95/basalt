/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt.Laws
import Basalt.SPMF.Walk

/-!
# Walking Cost Bounds

The structural half of a cost proof: `cost_bound` pushes a postcondition on (value, cost) through a
generator with the `@[gen_rule]` rules for `SPMF.Cost.Always`, leaving one arithmetic goal per path.
-/

open RandomChoice Lean Meta Elab Tactic

namespace SPMF

/-- Every outcome of `g` satisfies `P`. -/
def All (g : SPMF α) (P : α → Prop) : Prop :=
  ∀ a ∈ SPMF.support g, P a

end SPMF

theorem IsCostBounded.isBounded {g : SPMF.Cost α} {c : α → Nat} (h : IsCostBounded g c) :
    IsBounded g c := h

namespace SPMF.Cost

/-- Every value `g` produces satisfies `Q` together with the number of choices it took. -/
def Always (g : SPMF.Cost α) (Q : α → Nat → Prop) : Prop :=
  SPMF.All g fun p => Q p.1 p.2

theorem isBounded_iff_always {g : SPMF.Cost α} {c : α → Nat} :
    IsBounded g c ↔ Always g (fun a n => n ≤ c a) := Iff.rfl

/-! ## Leaves -/

/-- A cost bound is a postcondition, up to consequence. -/
theorem Always.of_isBounded {x : SPMF.Cost α} {c : α → Nat} {Q : α → Nat → Prop}
    (hx : IsBounded x c) (hq : ∀ a n, n ≤ c a → Q a n) : Always x Q :=
  fun p hp => hq _ _ (hx p hp)

theorem Always.of_isCostBounded {x : SPMF.Cost α} {c : α → Nat} {Q : α → Nat → Prop}
    (hx : IsCostBounded x c) (hq : ∀ a n, n ≤ c a → Q a n) : Always x Q :=
  of_isBounded hx hq

/-- Consequence: a postcondition implies any weaker one. -/
theorem Always.of_always {x : SPMF.Cost α} {R Q : α → Nat → Prop}
    (hx : Always x R) (hq : ∀ a n, R a n → Q a n) : Always x Q :=
  fun p hp => hq _ _ (hx p hp)

open Lean.Order in
theorem admissible_Always (Q : α → Nat → Prop) :
    admissible fun x : SPMF.Cost α => Always x Q := by
  intro c hc ih p hp
  rw [SPMF.mem_support_csup hc] at hp
  obtain ⟨x, hxc, hxp⟩ := hp
  exact ih x hxc p hxp

/-! ## The rules

One per combinator, each concluding `Always (<combinator> …) Q` for an arbitrary `Q` and asking the
sub-generators for the postcondition that makes it true: costs add along a bind, and a random choice
costs `1`. -/

@[gen_rule]
theorem always_pure {a : α} {Q : α → Nat → Prop} (h : Q a 0) :
    Always (Pure.pure a : SPMF.Cost α) Q := by
  rintro ⟨b, n⟩ hb
  obtain ⟨rfl, rfl⟩ := mem_support_pure_iff.mp hb
  exact h

@[gen_rule]
theorem always_bind {x : SPMF.Cost α} {f : α → SPMF.Cost β} {Q : β → Nat → Prop}
    (h : Always x fun a n => Always (f a) fun b m => Q b (n + m)) : Always (x >>= f) Q := by
  rintro ⟨b, k⟩ hb
  obtain ⟨a, n, m, ha, hb', rfl⟩ := mem_support_bind_iff.mp hb
  exact h (a, n) ha (b, m) hb'

@[gen_rule]
theorem always_map {x : SPMF.Cost α} {f : α → β} {Q : β → Nat → Prop}
    (h : Always x fun a n => Q (f a) n) : Always (f <$> x) Q := by
  rintro ⟨b, n⟩ hb
  obtain ⟨a, ha, rfl⟩ := mem_support_map_iff.mp hb
  exact h (a, n) ha

@[gen_rule]
theorem always_pick {x y : Unit → SPMF.Cost α} {Q : α → Nat → Prop}
    (hx : Always (x ()) fun a n => Q a (1 + n)) (hy : Always (y ()) fun a n => Q a (1 + n)) :
    Always (pick x y) Q := by
  rintro ⟨a, k⟩ ha
  obtain ⟨n, rfl, h | h⟩ := mem_support_pick_iff.mp ha
  exacts [hx (a, n) h, hy (a, n) h]

@[gen_rule]
theorem always_ite {p : Prop} [Decidable p] {x y : SPMF.Cost α} {Q : α → Nat → Prop}
    (hx : p → Always x Q) (hy : ¬p → Always y Q) :
    Always (if p then x else y) Q := by
  split
  · exact hx ‹_›
  · exact hy ‹_›

@[gen_rule]
theorem always_dite {p : Prop} [Decidable p] {x : p → SPMF.Cost α} {y : ¬p → SPMF.Cost α}
    {Q : α → Nat → Prop} (hx : ∀ h, Always (x h) Q) (hy : ∀ h, Always (y h) Q) :
    Always (if h : p then x h else y h) Q := by
  split
  · exact hx ‹_›
  · exact hy ‹_›

@[gen_rule]
theorem always_choose {lo hi : Nat} {h : lo ≤ hi}
    {Q : ULift {x : Nat // lo ≤ x ∧ x ≤ hi} → Nat → Prop} (hq : ∀ a, Q a 1) :
    Always (choose lo hi h : SPMF.Cost (ULift {x : Nat // lo ≤ x ∧ x ≤ hi})) Q := by
  rintro ⟨a, n⟩ ha
  obtain rfl := mem_support_choose_iff.mp ha
  exact hq a

@[gen_rule]
theorem always_chooseNat {lo hi : Nat} {h : lo ≤ hi} {Q : Nat → Nat → Prop}
    (hq : ∀ a, lo ≤ a ∧ a ≤ hi → Q a 1) : Always (chooseNat lo hi h : SPMF.Cost Nat) Q := by
  rintro ⟨a, n⟩ ha
  obtain ⟨hlo, rfl⟩ := mem_support_chooseNat_iff.mp ha
  exact hq a hlo

@[gen_rule]
theorem always_chooseInt {lo hi : Int} {h : lo ≤ hi} {Q : Int → Nat → Prop}
    (hq : ∀ a, lo ≤ a ∧ a ≤ hi → Q a 1) : Always (chooseInt lo hi h : SPMF.Cost Int) Q := by
  rintro ⟨a, n⟩ ha
  obtain ⟨hlo, rfl⟩ := mem_support_chooseInt_iff.mp ha
  exact hq a hlo

@[gen_rule]
theorem always_elements {xs : List α} {hne : xs ≠ []} {Q : α → Nat → Prop}
    (hq : ∀ a, a ∈ xs → Q a 1) : Always (elements xs hne : SPMF.Cost α) Q := by
  unfold elements
  refine always_bind (always_map (always_choose fun ⟨i, hge, hle⟩ => ?_))
  exact always_pure (by simpa using hq _ (List.getElem_mem _))

@[gen_rule]
theorem always_coin {r : Rat} {Q : Bool → Nat → Prop} (hq : ∀ a, Q a 1) :
    Always (coin r : SPMF.Cost Bool) Q := by
  unfold coin
  refine always_bind (always_choose fun k => always_ite ?_ ?_) <;>
    exact fun _ => always_pure (hq _)

/-- The postconditions of a list combinator's branches, one `cons` at a time. -/
inductive AllBranches (Q : α → Nat → Prop) : List (Unit → SPMF.Cost α) → Prop
  | nil : AllBranches Q []
  | cons {g : Unit → SPMF.Cost α} {gs} (h : Always (g ()) Q) (hs : AllBranches Q gs) :
      AllBranches Q (g :: gs)

theorem AllBranches.always {Q : α → Nat → Prop} {gs : List (Unit → SPMF.Cost α)}
    (h : AllBranches Q gs) : ∀ g ∈ gs, Always (g ()) Q := by
  induction h with
  | nil => simp
  | cons hg _ ih =>
    intro g hg'
    rcases List.mem_cons.mp hg' with rfl | hg'
    exacts [hg, ih g hg']

/-- `AllBranches` for a weighted branch list. Every branch is asked for the postcondition, whatever
its weight. -/
inductive AllWeighted (Q : α → Nat → Prop) : List (Nat × (Unit → SPMF.Cost α)) → Prop
  | nil : AllWeighted Q []
  | cons {w : Nat} {g : Unit → SPMF.Cost α} {gs} (h : Always (g ()) Q) (hs : AllWeighted Q gs) :
      AllWeighted Q ((w, g) :: gs)

theorem AllWeighted.always {Q : α → Nat → Prop} {gs : List (Nat × (Unit → SPMF.Cost α))}
    (h : AllWeighted Q gs) : ∀ wg ∈ gs, Always (wg.2 ()) Q := by
  induction h with
  | nil => simp
  | cons hg _ ih =>
    intro wg hwg
    rcases List.mem_cons.mp hwg with rfl | hwg
    exacts [hg, ih wg hwg]

@[gen_rule]
theorem always_oneOf {gs : List (Unit → SPMF.Cost α)} {hne : gs ≠ []} {Q : α → Nat → Prop}
    (h : AllBranches (fun a n => Q a (1 + n)) gs) : Always (oneOf gs hne : SPMF.Cost α) Q := by
  unfold oneOf Helpers.oneOfAux
  refine always_bind (always_map (always_choose fun ⟨i, hge, hle⟩ => ?_))
  exact h.always _ (List.getElem_mem _)

@[gen_rule]
theorem always_frequency {gs : List (Nat × (Unit → SPMF.Cost α))} {hw : 0 < (gs.map Prod.fst).sum}
    {Q : α → Nat → Prop} (h : AllWeighted (fun a n => Q a (1 + n)) gs) :
    Always (frequency gs hw : SPMF.Cost α) Q := by
  unfold frequency Helpers.frequencyAux
  refine always_bind (always_map (always_choose fun ⟨i, _, _⟩ => ?_))
  dsimp only
  split
  · obtain ⟨w, g, hg, -, heq⟩ := frequencySelect_mem ‹_›
    rw [heq]
    exact h.always (w, g) hg
  · exact fun _ hp => absurd rfl hp

end SPMF.Cost

namespace Basalt.CostBound

open Basalt.Walk

/-- `goal`, a cost law or a cost bound, restated as `Always`, its postcondition's binders named
after the cost function's as in a residual goal. -/
def toAlways (goal : MVarId) : MetaM MVarId := goal.withContext do
  let ty ← instantiateMVars (← goal.getType)
  if ty.isAppOfArity ``SPMF.Cost.Always 3 then return goal
  let ty ← if ty.isAppOfArity ``IsCostBounded 3 then
      pure (mkAppN (mkConst ``IsBounded ty.getAppFn.constLevels!) ty.getAppArgs)
    else pure ty
  unless ty.isAppOfArity ``IsBounded 3 do
    throwError "cost_bound: expected a goal `IsCostBounded (gen …) c`, `IsBounded (gen …) c`, or \
      `SPMF.Cost.Always (gen …) Q`, got{indentExpr ty}"
  let #[α, g, c] := ty.getAppArgs | unreachable!
  let v := match c with | .lam v _ _ _ => v.eraseMacroScopes | _ => `v
  let post ← withLocalDeclD v α fun a => withLocalDeclD (.mkSimple s!"n_{v}") (mkConst ``Nat) fun n => do
    mkLambdaFVars #[a, n] (← mkAppM ``LE.le #[n, (mkApp c a).headBeta])
  goal.change (← mkAppM ``SPMF.Cost.Always #[g, post])

/-- `goal` with its metavariables instantiated, and beta-redexes and projections out of constructor
applications reduced, in the target and every hypothesis. -/
def tidy (goal : MVarId) : MetaM MVarId := goal.withContext do
  goal.setTag .anonymous
  let mut goal := goal
  for d in ← getLCtx do
    unless d.isImplementationDetail do
      let t ← reduceCtorProjs d.type
      if t != d.type then goal ← goal.replaceLocalDeclDefEq d.fvarId t
  goal.replaceTargetDefEq (← reduceCtorProjs (← goal.getType))

/-- Walk `goal` (see `cost_bound`), returning the tidied residual goals. -/
def run (extras : Array Term) (goal : MVarId) : TermElabM (List MVarId) := do
  (← walk extras (← toAlways goal)).mapM fun g => tidy g

/-- `cost_bound` proves `IsCostBounded (gen …) c` (or `IsBounded`, or `SPMF.Cost.Always … Q`) up to
arithmetic: it walks `gen`'s syntax with the `@[gen_rule]` rules, pushing the postcondition
`n ≤ c v` into each sub-generator, and leaves one goal per path through `gen`. Recursive
occurrences are closed from the local context, callees from their `.cost_bounded` law; any other
cost bound can be passed as `cost_bound [h₁, h₂]`.

In a residual goal, a value drawn by `let x ← …` is named `x`, the choices that draw took `n_x`,
and what is known about it `h_x` (a callee's or recursive call's bound, or a pivot's range). -/
syntax (name := costBoundTac) "cost_bound" (" [" term,* "]")? : tactic

elab_rules : tactic
  | `(tactic| cost_bound $[[$args,*]]?) => withMainContext do
    replaceMainGoal (← run ((args.map (·.getElems)).getD #[]) (← getMainGoal))

end Basalt.CostBound

namespace SPMF.Cost

open Basalt.CostBound

/-! ## Rules for the combinators that take a generator

They ask for the generator's cost bound, which only a fact can supply: the list's postcondition says
nothing about any one element's cost. -/

section generatorArgument

variable {α : Type} {g : SPMF.Cost α} {c : α → Nat}

private theorem isBounded_vectorOf (hg : IsBounded g c) {k : Nat} :
    IsBounded (vectorOf k g : SPMF.Cost (List α)) fun a => (a.map c).sum := by
  induction k with
  | zero =>
    show Always (Pure.pure []) fun a n => n ≤ (a.map c).sum
    exact always_pure (Nat.zero_le _)
  | succ k ih =>
    rw [vectorOf_succ]
    cost_bound
    simp only [List.map_cons, List.sum_cons]
    omega

@[gen_rule]
theorem always_vectorOf {k : Nat} {Q : List α → Nat → Prop}
    (hg : IsBounded g c) (hq : ∀ a n, n ≤ (a.map c).sum → Q a n) :
    Always (vectorOf k g : SPMF.Cost (List α)) Q :=
  Always.of_isBounded (isBounded_vectorOf hg) hq

@[gen_rule]
theorem always_listOfMaxLength {k : Nat} {Q : List α → Nat → Prop} (hg : IsBounded g c)
    (hq : ∀ a n, n ≤ 1 + (a.map c).sum → Q a n) :
    Always (listOfMaxLength k g : SPMF.Cost (List α)) Q := by
  unfold listOfMaxLength
  exact always_bind (always_map (always_choose fun ⟨_, _⟩ =>
    always_vectorOf hg fun a n hn => hq a (1 + n) (by omega)))

private theorem isBounded_listOf (hg : IsBounded g c) :
    IsBounded (listOf g : SPMF.Cost (List α)) fun a => a.length + (a.map c).sum + 1 := by
  refine listOf.fixpoint_induct g _
    (admissible_Always fun a n => n ≤ a.length + (a.map c).sum + 1)
    (fun listOf ih => ?_)
  cost_bound
  all_goals simp only [List.length_cons, List.map_cons, List.sum_cons, List.length_nil,
    List.map_nil, List.sum_nil]; omega

private theorem isBounded_nonEmptyListOf (hg : IsBounded g c) :
    IsBounded (nonEmptyListOf g : SPMF.Cost (List α)) fun a => a.length + (a.map c).sum := by
  refine nonEmptyListOf.fixpoint_induct g _
    (admissible_Always fun a n => n ≤ a.length + (a.map c).sum)
    (fun nonEmptyListOf ih => ?_)
  cost_bound
  all_goals simp only [List.length_cons, List.map_cons, List.sum_cons, List.length_nil,
    List.map_nil, List.sum_nil]; omega

@[gen_rule]
theorem always_listOf {Q : List α → Nat → Prop}
    (hg : IsBounded g c) (hq : ∀ a n, n ≤ a.length + (a.map c).sum + 1 → Q a n) :
    Always (listOf g : SPMF.Cost (List α)) Q :=
  Always.of_isBounded (isBounded_listOf hg) hq

@[gen_rule]
theorem always_nonEmptyListOf {Q : List α → Nat → Prop}
    (hg : IsBounded g c) (hq : ∀ a n, n ≤ a.length + (a.map c).sum → Q a n) :
    Always (nonEmptyListOf g : SPMF.Cost (List α)) Q :=
  Always.of_isBounded (isBounded_nonEmptyListOf hg) hq

@[gen_rule]
theorem always_biasedOptionGen {r : Rat} {Q : Option α → Nat → Prop} (hg : IsBounded g c)
    (hq : ∀ a n, n ≤ 1 + a.elim 0 c → Q a n) :
    Always (biasedOptionGen r g : SPMF.Cost (Option α)) Q := by
  unfold biasedOptionGen
  cost_bound
  all_goals apply hq; simp only [Option.elim]; omega

@[gen_rule]
theorem always_optionGen {Q : Option α → Nat → Prop} (hg : IsBounded g c)
    (hq : ∀ a n, n ≤ 1 + a.elim 0 c → Q a n) :
    Always (optionGen g : SPMF.Cost (Option α)) Q :=
  always_biasedOptionGen hg hq

end generatorArgument

end SPMF.Cost
