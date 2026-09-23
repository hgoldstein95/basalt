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

open RandomChoice Lean Meta Elab Tactic Basalt.Walk

namespace SPMF.Cost

/-- Every value `g` produces satisfies `Q` together with the number of choices it took. -/
def Always (g : SPMF.Cost α) (Q : α → Nat → Prop) : Prop :=
  ∀ p ∈ SPMF.support g, Q p.1 p.2

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
    {Q : ULift {x : Nat // lo ≤ x ∧ x ≤ hi} → Nat → Prop}
    (hq : ∀ x (hx : lo ≤ x ∧ x ≤ hi), Q ⟨⟨x, hx⟩⟩ 1) :
    Always (choose lo hi h : SPMF.Cost (ULift {x : Nat // lo ≤ x ∧ x ≤ hi})) Q := by
  rintro ⟨⟨⟨x, hx⟩⟩, n⟩ ha
  obtain rfl := mem_support_choose_iff.mp ha
  exact hq x hx

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
  refine always_bind (always_map (always_choose fun i ⟨hge, hle⟩ => ?_))
  exact always_pure (by simpa using hq _ (List.getElem_mem _))

@[gen_rule]
theorem always_coin {r : Rat} {Q : Bool → Nat → Prop} (hq : ∀ a, Q a 1) :
    Always (coin r : SPMF.Cost Bool) Q := by
  unfold coin
  refine always_bind (always_choose fun k _ => always_ite ?_ ?_) <;>
    exact fun _ => always_pure (hq _)

@[gen_rule]
theorem always_oneOf {gs : List (Unit → SPMF.Cost α)} {hne : gs ≠ []} {Q : α → Nat → Prop}
    (h : AllBranches (fun g => Always (g ()) fun a n => Q a (1 + n)) gs) :
    Always (oneOf gs hne : SPMF.Cost α) Q := by
  unfold oneOf Helpers.oneOfAux
  refine always_bind (always_map (always_choose fun i ⟨hge, hle⟩ => ?_))
  exact allBranches_iff.mp h _ (List.getElem_mem _)

@[gen_rule]
theorem always_frequency {gs : List (Nat × (Unit → SPMF.Cost α))} {hw : 0 < (gs.map Prod.fst).sum}
    {Q : α → Nat → Prop} (h : AllBranches (fun wg => Always (wg.2 ()) fun a n => Q a (1 + n)) gs) :
    Always (frequency gs hw : SPMF.Cost α) Q := by
  unfold frequency Helpers.frequencyAux
  refine always_bind (always_map (always_choose fun i _ => ?_))
  dsimp only
  split
  · obtain ⟨w, g, hg, -, heq⟩ := frequencySelect_mem ‹_›
    rw [heq]
    exact allBranches_iff.mp h (w, g) hg
  · exact fun _ hp => absurd rfl hp

end SPMF.Cost

namespace Basalt.CostBound

/-- `goal`, a cost law or a cost bound, restated as `Always`, its postcondition's binders named
after the cost function's as in a residual goal. -/
def toAlways (goal : MVarId) : MetaM MVarId := goal.withContext do
  let ty := (← instantiateMVars (← goal.getType)).consumeMData
  if ty.isAppOfArity ``SPMF.Cost.Always 3 then return ← goal.replaceTargetDefEq ty
  unless ty.isAppOfArity ``IsCostBounded 3 || ty.isAppOfArity ``IsBounded 3 do
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
def walkCost (extras : Array Term) (goal : MVarId) : TermElabM (List MVarId) := do
  (← walk extras (← toAlways goal)).mapM fun g => tidy g

/-- `cost_bound` proves `IsCostBounded (gen …) c` (or `IsBounded`, or `SPMF.Cost.Always … Q`) up to
arithmetic: it walks `gen`'s syntax with the `@[gen_rule]` rules, pushing the postcondition
`n ≤ c v` into each sub-generator, and leaves one goal per path through `gen`. Recursive
occurrences are closed from the local context, callees from their `.cost_bounded` law; any other
cost bound can be passed as `cost_bound [h₁, h₂]`.

In a residual goal, a value drawn by `let x ← …` is named `x`, the choices that draw took `n_x`,
and what is known about it `h_x`, as the walker names them (`Basalt/SPMF/Walk.lean`). -/
syntax (name := costBoundTac) "cost_bound" (" [" term,* "]")? : tactic

elab_rules : tactic
  | `(tactic| cost_bound $[[$args,*]]?) => withMainContext do
    replaceMainGoal (← walkCost ((args.map (·.getElems)).getD #[]) (← getMainGoal))

end Basalt.CostBound

namespace SPMF.Cost

open Basalt.CostBound

/-! ## Rules for the combinators that take a generator

They ask for the generator's cost bound, which the list's postcondition says nothing about: a fact
supplies it, or else the worst-case rules below. -/

section generatorArgument

variable {α : Type} {g : SPMF.Cost α} {c : α → Nat}

private theorem isBounded_vectorOf_sum (hg : IsBounded g c) {k : Nat} :
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
  Always.of_isBounded (isBounded_vectorOf_sum hg) hq

@[gen_rule]
theorem always_listOfMaxLength {k : Nat} {Q : List α → Nat → Prop} (hg : IsBounded g c)
    (hq : ∀ a n, n ≤ 1 + (a.map c).sum → Q a n) :
    Always (listOfMaxLength k g : SPMF.Cost (List α)) Q := by
  unfold listOfMaxLength
  exact always_bind (always_map (always_choose fun _ _ =>
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

end generatorArgument

/-! ## Worst-case costs

A combinator term passed as a generator argument has no law to supply its cost bound. These rules
compute one that ignores the value — the most choices any run can make — which exists only for a
combinator whose runs are bounded. -/

section worstCase

variable {α β : Type}

private theorem isBounded_le {x : SPMF.Cost α} {k k' : Nat} (h : IsBounded x fun _ => k)
    (hk : k ≤ k') {Q : α → Nat → Prop} (hq : ∀ a n, n ≤ k' → Q a n) : Always x Q :=
  Always.of_isBounded h fun a n hn => hq a n (Nat.le_trans hn hk)

/-- The largest of the branches' worst cases bounds each of them. -/
private theorem isBounded_foldr_max {γ : Type} {f : γ → SPMF.Cost α} {ks : List Nat} {bs : List γ}
    (h : List.Forall₂ (fun k b => IsBounded (f b) fun _ => k) ks bs) :
    ∀ b ∈ bs, IsBounded (f b) fun _ => ks.foldr max 0 := by
  induction h with
  | nil => simp
  | cons hk _ ih =>
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    exacts [IsBounded_mono hk fun _ => Nat.le_max_left _ _,
      IsBounded_mono (ih b hb) fun _ => Nat.le_max_right _ _]

@[gen_rule]
theorem isBounded_pure {a : α} : IsBounded (Pure.pure a : SPMF.Cost α) fun _ => 0 := by
  cost_bound; omega

@[gen_rule]
theorem isBounded_bind {x : SPMF.Cost α} {f : α → SPMF.Cost β} {k₁ k₂ : Nat}
    (hx : IsBounded x fun _ => k₁) (hf : ∀ a, IsBounded (f a) fun _ => k₂) :
    IsBounded (x >>= f) fun _ => k₁ + k₂ := by
  cost_bound; omega

@[gen_rule]
theorem isBounded_map {x : SPMF.Cost α} {f : α → β} {k : Nat} (hx : IsBounded x fun _ => k) :
    IsBounded (f <$> x) fun _ => k := by
  cost_bound; omega

@[gen_rule]
theorem isBounded_pick {x y : Unit → SPMF.Cost α} {k₁ k₂ : Nat}
    (hx : IsBounded (x ()) fun _ => k₁) (hy : IsBounded (y ()) fun _ => k₂) :
    IsBounded (pick x y) fun _ => 1 + max k₁ k₂ := by
  cost_bound <;> omega

@[gen_rule]
theorem isBounded_ite {p : Prop} [Decidable p] {x y : SPMF.Cost α} {k₁ k₂ : Nat}
    (hx : p → IsBounded x fun _ => k₁) (hy : ¬p → IsBounded y fun _ => k₂) :
    IsBounded (if p then x else y) fun _ => max k₁ k₂ := by
  cost_bound <;> omega

@[gen_rule]
theorem isBounded_dite {p : Prop} [Decidable p] {x : p → SPMF.Cost α} {y : ¬p → SPMF.Cost α}
    {k₁ k₂ : Nat} (hx : ∀ h, IsBounded (x h) fun _ => k₁) (hy : ∀ h, IsBounded (y h) fun _ => k₂) :
    IsBounded (if h : p then x h else y h) fun _ => max k₁ k₂ := by
  cost_bound <;> omega

@[gen_rule]
theorem isBounded_choose {lo hi : Nat} {h : lo ≤ hi} :
    IsBounded (choose lo hi h : SPMF.Cost (ULift {x : Nat // lo ≤ x ∧ x ≤ hi})) fun _ => 1 := by
  cost_bound; omega

@[gen_rule]
theorem isBounded_chooseInt {lo hi : Int} {h : lo ≤ hi} :
    IsBounded (chooseInt lo hi h : SPMF.Cost Int) fun _ => 1 := by
  cost_bound; omega

@[gen_rule]
theorem isBounded_elements {xs : List α} {hne : xs ≠ []} :
    IsBounded (elements xs hne : SPMF.Cost α) fun _ => 1 := by
  cost_bound; omega

@[gen_rule]
theorem isBounded_coin {r : Rat} : IsBounded (coin r : SPMF.Cost Bool) fun _ => 1 := by
  cost_bound; omega

@[gen_rule]
theorem isBounded_oneOf {gs : List (Unit → SPMF.Cost α)} {hne : gs ≠ []} {ks : List Nat}
    (h : List.Forall₂ (fun k g => IsBounded (g ()) fun _ => k) ks gs) :
    IsBounded (oneOf gs hne : SPMF.Cost α) fun _ => 1 + ks.foldr max 0 :=
  isBounded_iff_always.mpr (always_oneOf (allBranches_iff.mpr fun g hg =>
    isBounded_le (isBounded_foldr_max (f := fun g => g ()) h g hg) le_rfl fun _ _ _ => by omega))

@[gen_rule]
theorem isBounded_frequency {gs : List (Nat × (Unit → SPMF.Cost α))}
    {hw : 0 < (gs.map Prod.fst).sum} {ks : List Nat}
    (h : List.Forall₂ (fun k wg => IsBounded (wg.2 ()) fun _ => k) ks gs) :
    IsBounded (frequency gs hw : SPMF.Cost α) fun _ => 1 + ks.foldr max 0 :=
  isBounded_iff_always.mpr (always_frequency (allBranches_iff.mpr fun wg hwg =>
    isBounded_le (isBounded_foldr_max (f := fun wg => wg.2 ()) h wg hwg) le_rfl
      fun _ _ _ => by omega))

@[gen_rule]
theorem isBounded_vectorOf {n : Nat} {g : SPMF.Cost α} {k : Nat} (hg : IsBounded g fun _ => k) :
    IsBounded (vectorOf n g : SPMF.Cost (List α)) fun _ => n * k := by
  induction n with
  | zero =>
    show IsBounded (Pure.pure []) _
    exact IsBounded_mono isBounded_pure fun _ => Nat.zero_le _
  | succ n ih =>
    rw [vectorOf_succ]
    refine IsBounded_mono (isBounded_bind hg fun _ => isBounded_bind ih fun _ => isBounded_pure)
      fun _ => ?_
    rw [Nat.succ_mul]
    omega

@[gen_rule]
theorem isBounded_listOfMaxLength {n : Nat} {g : SPMF.Cost α} {k : Nat}
    (hg : IsBounded g fun _ => k) :
    IsBounded (listOfMaxLength n g : SPMF.Cost (List α)) fun _ => 1 + n * k := by
  unfold listOfMaxLength
  refine isBounded_iff_always.mpr (always_bind (always_map (always_choose ?_)))
  rintro j ⟨-, hj⟩
  exact isBounded_le (isBounded_vectorOf hg) (Nat.mul_le_mul_right k hj) fun _ _ _ => by omega

end worstCase

end SPMF.Cost
