/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Mathlib.Data.ENat.Lattice
import Basalt.Laws
import Basalt.Walk.Entry

/-!
# Walking Cost Bounds

The structural half of a cost proof. `SPMF.Cost.Always g Q` is a lower bound, by `True`, on
`SPMF.Cost.alwaysObs` in the demonic algebra, so `cost_bound` is the walk of
`Basalt/Obs/Ordered.lean`: it computes the weakest precondition of `Q` and splits it into one
arithmetic goal per path. The worst-case cost of a combinator term, which a list combinator needs of
its argument, is an upper bound on `SPMF.Cost.worstObs` in the `sup` algebra.
-/

open RandomChoice Lean Meta Elab Tactic Basalt.Walk

namespace SPMF.Cost

/-- Every value `g` produces satisfies `Q` together with the number of choices it took. -/
def Always (g : SPMF.Cost α) (Q : α → Nat → Prop) : Prop :=
  ∀ p ∈ SPMF.support g, Q p.1 p.2

theorem isBounded_iff_always {g : SPMF.Cost α} {c : α → Nat} :
    IsBounded g c ↔ Always g (fun a n => n ≤ c a) := Iff.rfl

/-- `Always`, read through a specification the always observation equals. -/
theorem always_of_obs {g : SPMF.Cost α} {w : WPC Mix.demonic α} (h : alwaysObs.spec g = w)
    {Q : α → Nat → Prop} : Always g Q ↔ w Q :=
  iff_of_eq (congrFun h Q)

/-- A cost bound is a postcondition, up to consequence. -/
theorem Always.of_isBounded {x : SPMF.Cost α} {c : α → Nat} {Q : α → Nat → Prop}
    (hx : IsBounded x c) (hq : ∀ a n, n ≤ c a → Q a n) : Always x Q :=
  fun p hp => hq _ _ (hx p hp)

open Lean.Order in
theorem admissible_Always (Q : α → Nat → Prop) :
    admissible fun x : SPMF.Cost α => Always x Q := by
  intro c hc ih p hp
  rw [SPMF.mem_support_csup hc] at hp
  obtain ⟨x, hxc, hxp⟩ := hp
  exact ih x hxc p hxp

instance : alwaysObs.MonotoneC := ⟨fun _ _ _ h hp _ ha => h _ _ (hp _ ha)⟩

/-! ## Leaves

A fact about a sub-generator is used under the postcondition the walk arrives with: what it has to
imply is the bound. -/

theorem le_spec_of_always {x : SPMF.Cost α} {R p : α → Nat → Prop} (hx : Always x R) :
    (∀ a n, R a n → p a n) ≤ alwaysObs.spec x p := fun h q hq => h _ _ (hx q hq)

theorem le_spec_of_isBounded {x : SPMF.Cost α} {c : α → Nat} {p : α → Nat → Prop}
    (hx : IsBounded x c) : (∀ a n, n ≤ c a → p a n) ≤ alwaysObs.spec x p :=
  fun h q hq => h _ _ (hx q hq)

theorem le_spec_of_isCostBounded {x : SPMF.Cost α} {c : α → Nat} {p : α → Nat → Prop}
    (hx : IsCostBounded x c) : (∀ a n, n ≤ c a → p a n) ≤ alwaysObs.spec x p :=
  le_spec_of_isBounded hx

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

/-- Walk `goal` (see `cost_bound`), returning the tidied residual goals. -/
partial def walkCost (extras : Array Term) (goal : MVarId) : TermElabM (List MVarId) := do
  let goal ← toAlways goal
  goal.withContext do
  let #[_, g, post] := (← instantiateMVars (← goal.getType)).getAppArgs
    | throwError "cost_bound: internal error"
  if let some cases ← splitMatch? goal g then return ← cases.flatMapM (walkCost extras)
  let (wp, structural, rest) ← computeBound extras ``SPMF.Cost.alwaysObs true g post
  let paths ← mkFreshExprMVar wp
  goal.assign (mkApp structural paths)
  ((← splitPaths paths.mvarId!) ++ rest).mapM fun g => tidy g

/-- `cost_bound` proves `IsCostBounded (gen …) c` (or `IsBounded`, or `SPMF.Cost.Always … Q`) up to
arithmetic: it walks `gen`'s syntax, pushing the postcondition `n ≤ c v` into each sub-generator,
and leaves one goal per path through `gen`. Recursive occurrences are closed from the local context,
callees from their `.cost_bounded` law; any other cost bound can be passed as `cost_bound [h₁, h₂]`.

In a residual goal, a value drawn by `let x ← …` is named `x`, the choices that draw took `n_x`,
and what is known about it `h_x`, as the walker names them (`Basalt/Walk/Basic.lean`). -/
syntax (name := costBoundTac) "cost_bound" (" [" term,* "]")? : tactic

elab_rules : tactic
  | `(tactic| cost_bound $[[$args,*]]?) => withMainContext do
    replaceMainGoal (← walkCost ((args.map (·.getElems)).getD #[]) (← getMainGoal))

end Basalt.CostBound

namespace SPMF.Cost

open Basalt.CostBound

/-! ## The combinators that take a generator

They ask for the generator's cost bound, which the list's postcondition says nothing about: a fact
supplies it, or else its worst case below. The recursive ones are laws, bridged to the walk. -/

section generatorArgument

variable {α : Type} {g : SPMF.Cost α} {c : α → Nat} {p : List α → Nat → Prop}

private theorem isBounded_vectorOf_sum (hg : IsBounded g c) {k : Nat} :
    IsBounded (vectorOf k g : SPMF.Cost (List α)) fun a => (a.map c).sum := by
  induction k with
  | zero =>
    show IsBounded (Pure.pure []) _
    cost_bound
    simp
  | succ k ih =>
    rw [vectorOf_succ]
    cost_bound
    simp only [List.map_cons, List.sum_cons]
    omega

@[gen_rule]
theorem le_spec_vectorOf {k : Nat} (hg : IsBounded g c) :
    (∀ a n, n ≤ (a.map c).sum → p a n) ≤ alwaysObs.spec (vectorOf k g) p :=
  le_spec_of_isBounded (isBounded_vectorOf_sum hg)

@[gen_rule]
theorem le_spec_listOfMaxLength {k : Nat} (hg : IsBounded g c) :
    (∀ a n, n ≤ 1 + (a.map c).sum → p a n) ≤ alwaysObs.spec (listOfMaxLength k g) p := by
  intro h
  unfold listOfMaxLength
  refine (always_of_obs ((alwaysObs.map_bind _ _).trans
    (congrArg (· >>= _) ((alwaysObs.map_map _ _).trans
      (congrArg _ (alwaysObs.map_choose 0 k (Nat.zero_le k))))))).mpr ?_
  exact (Mix.range_demonic _).mpr fun j _ =>
    Always.of_isBounded (isBounded_vectorOf_sum hg) fun a n hn => h a (1 + 0 + n) (by omega)

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
theorem le_spec_listOf (hg : IsBounded g c) :
    (∀ a n, n ≤ a.length + (a.map c).sum + 1 → p a n) ≤ alwaysObs.spec (listOf g) p :=
  le_spec_of_isBounded (isBounded_listOf hg)

@[gen_rule]
theorem le_spec_nonEmptyListOf (hg : IsBounded g c) :
    (∀ a n, n ≤ a.length + (a.map c).sum → p a n) ≤ alwaysObs.spec (nonEmptyListOf g) p :=
  le_spec_of_isBounded (isBounded_nonEmptyListOf hg)

end generatorArgument

end SPMF.Cost

/-! ## Worst-case costs

A combinator term passed as a generator argument has no law to supply its cost bound; its worst
case, the most choices any run can make, is `SPMF.Cost.worstObs`, and these are its bounds in the
`sup` algebra. -/

namespace SPMF.Cost

instance : worstObs.MonotoneC :=
  ⟨fun _ _ _ h => iSup₂_mono fun p _ => h p.1 p.2⟩

/-- The judgment `IsBounded g fun _ => k`, with `k` to be found, as an upper bound on `worstObs`. -/
theorem isBounded_of_worst {g : SPMF.Cost α} {b : ℕ∞} {k : Nat}
    (h : worstObs.spec g (fun _ n => (n : ℕ∞)) ≤ b) (hb : b = (k : ℕ∞)) :
    IsBounded g fun _ => k := fun p hp =>
  Nat.cast_le.mp ((le_iSup₂_of_le p hp le_rfl).trans (h.trans hb.le))

theorem worst_le_add_of_le {x : SPMF.Cost α} {p : α → Nat → ℕ∞} {k B : ℕ∞}
    (hx : worstObs.spec x (fun _ n => (n : ℕ∞)) ≤ B) (hp : ∀ a n, p a n = k + (n : ℕ∞)) :
    worstObs.spec x p ≤ k + B :=
  iSup₂_le fun q hq => (hp q.1 q.2).le.trans
    (add_le_add le_rfl ((le_iSup₂_of_le q hq le_rfl).trans hx))

theorem worst_le_add_of_isBounded {x : SPMF.Cost α} {p : α → Nat → ℕ∞} {k : ℕ∞} {K : Nat}
    (hx : IsBounded x fun _ => K) (hp : ∀ a n, p a n = k + (n : ℕ∞)) :
    worstObs.spec x p ≤ k + (K : ℕ∞) :=
  worst_le_add_of_le (iSup₂_le fun q hq => Nat.cast_le.mpr (hx q hq)) hp

end SPMF.Cost

@[norm_cast]
theorem ENat.coe_max' (a b : ℕ) : ((max a b : ℕ) : ℕ∞) = max (a : ℕ∞) (b : ℕ∞) :=
  Nat.mono_cast.map_max

@[norm_cast]
theorem ENat.coe_ite' (p : Prop) [Decidable p] (a b : ℕ) :
    ((if p then a else b : ℕ) : ℕ∞) = if p then (a : ℕ∞) else (b : ℕ∞) := by split <;> rfl

namespace Mix

@[gen_rule] theorem sup_range_le {lo hi : Nat} {h : lo ≤ hi}
    {F : ULift.{u} {x : Nat // lo ≤ x ∧ x ≤ hi} → ℕ∞} {d : ℕ∞}
    (hF : ∀ x (hx : lo ≤ x ∧ x ≤ hi), F ⟨⟨x, hx⟩⟩ ≤ d) : Mix.sup.range lo hi h F ≤ d :=
  iSup_le fun a => hF _ a.down.property

set_option linter.deprecated false in
@[gen_rule, deprecated "use `sup_index_le`" (since := "2026-09-22")]
theorem sup_binary_le {t e c d : ℕ∞} (ht : t ≤ c) (he : e ≤ d) :
    (Mix.sup.{u}).binary t e ≤ max c d := by
  refine iSup_le fun a => ?_
  dsimp only
  split
  · exact ht.trans (le_max_left _ _)
  · exact he.trans (le_max_right _ _)

@[gen_rule] theorem sup_threshold_le {n : Nat} {k : ℤ} {t e c d : ℕ∞} (ht : t ≤ c) (he : e ≤ d) :
    (Mix.sup.{u}).threshold n k t e ≤ max c d := by
  refine iSup_le fun a => ?_
  dsimp only
  split
  · exact ht.trans (le_max_left _ _)
  · exact he.trans (le_max_right _ _)

private theorem le_foldr_max {γ : Type v} {F : γ → ℕ∞} {cs : List ℕ∞} {l : List γ}
    (h : List.Forall₂ (fun c g => F g ≤ c) cs l) : ∀ g ∈ l, F g ≤ cs.foldr max 0 := by
  induction h with
  | nil => simp
  | cons hc _ ih =>
    intro g hg
    rcases List.mem_cons.mp hg with rfl | hg
    · exact hc.trans (le_max_left _ _)
    · exact (ih g hg).trans (le_max_right _ _)

@[gen_rule] theorem sup_index_le {γ : Type v} {l : List γ} {hne : l ≠ []} {F : γ → ℕ∞}
    {cs : List ℕ∞} (h : List.Forall₂ (fun c g => F g ≤ c) cs l) :
    (Mix.sup.{u}).index l hne F ≤ cs.foldr max 0 :=
  iSup_le fun _ => le_foldr_max h _ (List.getElem_mem _)

@[gen_rule] theorem sup_element_le {γ : Type v} {l : List γ} {hne : l ≠ []} {F : γ → ℕ∞} {d : ℕ∞}
    (h : ∀ a ∈ l, F a ≤ d) : (Mix.sup.{u}).element l hne F ≤ d :=
  iSup_le fun _ => h _ (List.getElem_mem _)

private theorem selectD_le {l : List (Nat × ℕ∞)} {b : ℕ∞} (h : ∀ p ∈ l, p.2 ≤ b) (d : ℕ∞) :
    ∀ n, n < (l.map Prod.fst).sum → Obs.selectD l n d ≤ b := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    obtain ⟨k, x⟩ := hd
    intro n hn
    simp only [Obs.selectD]
    split
    · exact h (k, x) List.mem_cons_self
    · exact ih (fun p hp => h p (List.mem_cons_of_mem _ hp)) _
        (by simp only [List.map_cons, List.sum_cons] at hn; omega)

@[gen_rule] theorem sup_select_le {γ : Type v} {l : List (Nat × γ)}
    {hpos : 0 < (l.map Prod.fst).sum} {F : γ → ℕ∞} {d : ℕ∞} {cs : List (Nat × ℕ∞)}
    (h : Weighted (· ≤ ·) F cs l) :
    (Mix.sup.{u}).select l hpos F d ≤ (cs.map Prod.snd).foldr max 0 := by
  have key : ∀ q ∈ l, F q.2 ≤ (cs.map Prod.snd).foldr max 0 := by
    clear hpos
    induction h with
    | nil => simp
    | cons hc _ ih =>
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact hc.trans (le_max_left _ _)
      · exact (ih q hq).trans (le_max_right _ _)
  refine iSup_le fun a => selectD_le (fun p hp => ?_) d _ ?_
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    exact key q hq
  · have h1 := a.down.property.2
    have h2 : ((l.map fun p => (p.1, F p.2)).map Prod.fst).sum = (l.map Prod.fst).sum := by
      simp [Function.comp_def]
    omega

@[gen_rule] theorem sup_rangeInt_le {lo hi : ℤ} {h : lo ≤ hi} {F : ℤ → ℕ∞} {d : ℕ∞}
    (hF : ∀ x, lo ≤ x ∧ x ≤ hi → F x ≤ d) : (Mix.sup.{0}).rangeInt lo hi h F ≤ d := by
  refine iSup_le fun a => hF _ ⟨by omega, ?_⟩
  have := a.down.property
  omega

end Mix

namespace SPMF.Cost

open Basalt.CostBound

/-! The list combinators of fixed or bounded length, bridged to the worst-case walk. -/

variable {α : Type} {g : SPMF.Cost α} {b k : ℕ∞} {p : List α → Nat → ℕ∞}

private theorem isBounded_vectorOf {n k : Nat} (hg : IsBounded g fun _ => k) :
    IsBounded (vectorOf n g : SPMF.Cost (List α)) fun _ => n * k := by
  induction n with
  | zero =>
    show IsBounded (Pure.pure []) _
    cost_bound
    omega
  | succ n ih =>
    rw [vectorOf_succ]
    -- The recursive occurrence is a combinator term, which the walk would bound by its rule.
    generalize (vectorOf n g : SPMF.Cost (List α)) = v at ih ⊢
    cost_bound
    rw [Nat.succ_mul]
    omega

private theorem always_listOfMaxLength {n : Nat} {Q : List α → Nat → Prop}
    (h : ∀ j, j ≤ n → Always (vectorOf j g) fun a m => Q a (1 + 0 + m)) :
    Always (listOfMaxLength n g) Q := by
  unfold listOfMaxLength
  refine (always_of_obs ((alwaysObs.map_bind _ _).trans
    (congrArg (· >>= _) ((alwaysObs.map_map _ _).trans
      (congrArg _ (alwaysObs.map_choose 0 n (Nat.zero_le n))))))).mpr ?_
  exact (Mix.range_demonic _).mpr fun j hj => h j hj.2

private theorem isBounded_listOfMaxLength {n k : Nat} (hg : IsBounded g fun _ => k) :
    IsBounded (listOfMaxLength n g : SPMF.Cost (List α)) fun _ => 1 + n * k := by
  refine isBounded_iff_always.mpr (always_listOfMaxLength (Q := fun _ m => m ≤ 1 + n * k)
    fun j hj => Always.of_isBounded (isBounded_vectorOf hg) fun a m hm => ?_)
  have := Nat.mul_le_mul_right k hj
  show 1 + 0 + m ≤ 1 + n * k
  omega

@[gen_rule]
theorem worst_vectorOf_le {n : Nat} (hg : worstObs.spec g (fun _ m => (m : ℕ∞)) ≤ b)
    (hp : ∀ a m, p a m = k + (m : ℕ∞)) : worstObs.spec (vectorOf n g) p ≤ k + n * b := by
  induction b using ENat.recTopCoe with
  | top =>
    cases n with
    | zero =>
      refine (congrFun (worstObs.map_pure _) p).le.trans ?_
      show p [] 0 ≤ _
      rw [hp]
      simp
    | succ n => simp
  | coe K =>
    refine (worst_le_add_of_isBounded (isBounded_vectorOf (isBounded_of_worst hg rfl)) hp).trans ?_
    push_cast
    exact le_rfl

@[gen_rule]
theorem worst_listOfMaxLength_le {n : Nat} (hg : worstObs.spec g (fun _ m => (m : ℕ∞)) ≤ b)
    (hp : ∀ a m, p a m = k + (m : ℕ∞)) :
    worstObs.spec (listOfMaxLength n g) p ≤ k + (1 + n * b) := by
  induction b using ENat.recTopCoe with
  | top =>
    cases n with
    | zero =>
      have h0 : IsBounded (listOfMaxLength 0 g : SPMF.Cost (List α)) fun _ => 1 := by
        refine isBounded_iff_always.mpr (always_listOfMaxLength (Q := fun _ m => m ≤ 1)
          fun j hj => ?_)
        obtain rfl : j = 0 := by omega
        exact (always_of_obs (alwaysObs.map_pure _)).mpr (show 1 + 0 + 0 ≤ 1 by omega)
      exact (worst_le_add_of_isBounded h0 hp).trans (by simp)
    | succ n => simp
  | coe K =>
    refine (worst_le_add_of_isBounded
      (isBounded_listOfMaxLength (isBounded_of_worst hg rfl)) hp).trans ?_
    push_cast
    exact le_rfl

end SPMF.Cost
