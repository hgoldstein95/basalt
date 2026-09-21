/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt

/-!
# Cost-Always as a Lower Bound in the Demonic Algebra, Prototyped

What `cost_bound` and `cost_fixpoint` would become under `PLAN.md`'s Stage 2 step 5:
`SPMF.Cost.Always g Q` is `True ≤ SPMF.Cost.alwaysObs.spec g Q`, so the walk computes the weakest
precondition as one proposition with the lower-bound rules, and `cost_bound'` then introduces and
splits it into one goal per path.
-/

open RandomChoice Lean Meta Elab Tactic

instance : SPMF.Cost.alwaysObs.MonotoneC := ⟨fun _ _ _ h hp _ ha => h _ _ (hp _ ha)⟩

namespace Obs

variable {G : Type u → Type v} {Ω : Type w} [Preorder Ω] {m : Mix.{u} Ω} [Monad G] [RandomChoice G]
  {O : Obs G (WPC m)}

@[gen_rule] theorem le_specC_pure {a : α} {post : α → Nat → Ω} {b : Ω} (hb : b ≤ post a 0) :
    b ≤ O.spec (Pure.pure a) post := hb.trans (congrFun (O.map_pure a) post).ge

@[gen_rule] theorem le_specC_bind [O.MonotoneC] {x : G α} {k : α → G β} {post : β → Nat → Ω}
    {h : α → Nat → Ω} {b : Ω}
    (hk : ∀ a n, h a n ≤ O.spec (k a) (fun b n' => post b (n + n'))) (hx : b ≤ O.spec x h) :
    b ≤ O.spec (x >>= k) post :=
  (hx.trans (MonotoneC.spec_mono x hk)).trans (congrFun (O.map_bind x k) post).ge

@[gen_rule] theorem le_specC_map [LawfulMonad G] {x : G α} {f : α → β} {post : β → Nat → Ω}
    {b : Ω} (hx : b ≤ O.spec x (fun a n => post (f a) n)) : b ≤ O.spec (f <$> x) post :=
  hx.trans (congrFun (O.map_map f x) post).ge

@[gen_rule] theorem le_specC_ite {p : Prop} [Decidable p] {x y : G α} {post : α → Nat → Ω}
    {c d : Ω} (hx : p → c ≤ O.spec x post) (hy : ¬p → d ≤ O.spec y post) :
    (if p then c else d) ≤ O.spec (if p then x else y) post := by split <;> simp_all

/-- The bound may mention the branch's proof. -/
@[gen_rule] theorem le_specC_dite {p : Prop} [Decidable p] {x : p → G α} {y : ¬p → G α}
    {post : α → Nat → Ω} {c : p → Ω} {d : ¬p → Ω} (hx : ∀ h, c h ≤ O.spec (x h) post)
    (hy : ∀ h, d h ≤ O.spec (y h) post) :
    (if h : p then c h else d h) ≤ O.spec (if h : p then x h else y h) post := by
  split <;> simp_all

theorem le_specC_of_map {g : G α} {w : WPC m α} {post : α → Nat → Ω} {b : Ω}
    (h : O.spec g = w) (hw : b ≤ w post) : b ≤ O.spec g post := hw.trans (congrFun h post).ge

end Obs

namespace Mix

@[gen_rule] theorem le_demonic_mix {lo hi : Nat} {F : ULift.{u} {x : Nat // lo ≤ x ∧ x ≤ hi} → Prop}
    {d : (x : Nat) → lo ≤ x ∧ x ≤ hi → Prop} (h : ∀ x hx, d x hx ≤ F ⟨⟨x, hx⟩⟩) :
    (∀ x hx, d x hx) ≤ Mix.demonic.mix lo hi F := fun hd a => h _ _ (hd _ _)

@[gen_rule] theorem le_demonic_binary {t e c d : Prop} (ht : c ≤ t) (he : d ≤ e) :
    (c ∧ d) ≤ (Mix.demonic.{u}).binary t e := by
  rintro ⟨hc, hd⟩ a
  show if _ then t else e
  split
  · exact ht hc
  · exact he hd

@[gen_rule] theorem le_demonic_threshold {n : Nat} {k : ℤ} {t e c d : Prop} (ht : c ≤ t)
    (he : d ≤ e) : (c ∧ d) ≤ (Mix.demonic.{u}).threshold n k t e := by
  rintro ⟨hc, hd⟩ a
  show if _ then t else e
  split
  · exact ht hc
  · exact he hd

@[gen_rule] theorem le_demonic_index {γ : Type v} {l : List γ} {hne : l ≠ []} {F : γ → Prop}
    {cs : List Prop} (h : List.Forall₂ (fun c g => c ≤ F g) cs l) :
    cs.foldr And True ≤ (Mix.demonic.{u}).index l hne F := by
  intro hcs
  have key : ∀ g ∈ l, F g := by
    clear hne
    induction h with
    | nil => simp
    | cons hc _ ih => exact List.forall_mem_cons.mpr ⟨hc hcs.1, ih hcs.2⟩
  exact (index_demonic l hne F).mpr key

/-- The fallback for a list that is not a literal. -/
@[gen_rule] theorem le_demonic_index_mem {γ : Type v} {l : List γ} {hne : l ≠ []} {F : γ → Prop} :
    (∀ g ∈ l, F g) ≤ (Mix.demonic.{u}).index l hne F := (index_demonic l hne F).mpr

@[gen_branches]
inductive BranchesGE {γ : Type v} (F : γ → Prop) : List Prop → List (Nat × γ) → Prop
  | nil : BranchesGE F [] []
  | cons {w : Nat} {c : Prop} {g : γ} {cs gs} (h : c ≤ F g) (hs : BranchesGE F cs gs) :
      BranchesGE F (c :: cs) ((w, g) :: gs)

@[gen_rule] theorem le_demonic_select {γ : Type v} {l : List (Nat × γ)}
    {hpos : 0 < (l.map Prod.fst).sum} {F : γ → Prop} {d : Prop} {cs : List Prop}
    (h : BranchesGE F cs l) : cs.foldr And True ≤ (Mix.demonic.{u}).select l hpos F d := by
  intro hcs
  have key : ∀ q ∈ l, F q.2 := by
    clear hpos
    induction h with
    | nil => simp
    | cons hc _ ih => exact List.forall_mem_cons.mpr ⟨hc hcs.1, ih hcs.2⟩
  refine (select_demonic (l.map fun p => (p.1, F p.2)) (by simp [Function.comp_def]) hpos d).mpr ?_
  intro p hp _
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  exact key q hq

@[gen_rule] theorem le_demonic_rangeInt {lo hi : ℤ} {h : lo ≤ hi} {F : ℤ → Prop}
    {d : (x : ℤ) → lo ≤ x ∧ x ≤ hi → Prop} (hF : ∀ x hx, d x hx ≤ F x) :
    (∀ x hx, d x hx) ≤ (Mix.demonic.{0}).rangeInt lo hi h F := by
  intro hd a
  have := a.down.property
  exact hF _ ⟨by omega, by omega⟩ (hd _ _)

end Mix

namespace SPMF.Cost

theorem le_spec_of_always {x : SPMF.Cost α} {R p : α → Nat → Prop} (hx : Always x R) :
    (∀ a n, R a n → p a n) ≤ alwaysObs.spec x p := fun h q hq => h _ _ (hx q hq)

theorem le_spec_of_isBounded {x : SPMF.Cost α} {c : α → Nat} {p : α → Nat → Prop}
    (hx : IsBounded x c) : (∀ a n, n ≤ c a → p a n) ≤ alwaysObs.spec x p :=
  fun h q hq => h _ _ (hx q hq)

theorem le_spec_of_isCostBounded {x : SPMF.Cost α} {c : α → Nat} {p : α → Nat → Prop}
    (hx : IsCostBounded x c) : (∀ a n, n ≤ c a → p a n) ≤ alwaysObs.spec x p :=
  le_spec_of_isBounded hx

/-! The recursive list combinators stay laws, bridged per judgment; their generator argument's
cost bound is today's `IsBounded` judgment. -/

variable {α : Type} {g : SPMF.Cost α} {c : α → Nat} {p : List α → Nat → Prop}

@[gen_rule] theorem le_spec_vectorOf {k : Nat} (hg : IsBounded g c) :
    (∀ a n, n ≤ (a.map c).sum → p a n) ≤ alwaysObs.spec (vectorOf k g) p :=
  fun h => always_vectorOf hg h

@[gen_rule] theorem le_spec_listOfMaxLength {k : Nat} (hg : IsBounded g c) :
    (∀ a n, n ≤ 1 + (a.map c).sum → p a n) ≤ alwaysObs.spec (listOfMaxLength k g) p :=
  fun h => always_listOfMaxLength hg h

@[gen_rule] theorem le_spec_listOf (hg : IsBounded g c) :
    (∀ a n, n ≤ a.length + (a.map c).sum + 1 → p a n) ≤ alwaysObs.spec (listOf g) p :=
  fun h => always_listOf hg h

@[gen_rule] theorem le_spec_nonEmptyListOf (hg : IsBounded g c) :
    (∀ a n, n ≤ a.length + (a.map c).sum → p a n) ≤ alwaysObs.spec (nonEmptyListOf g) p :=
  fun h => always_nonEmptyListOf hg h

end SPMF.Cost

namespace Basalt.CostGate

open Basalt.Walk Basalt.CostBound Lean.Order

theorem ite_intro {p : Prop} [Decidable p] {c d : Prop} (hc : p → c) (hd : ¬p → d) :
    if p then c else d := by split <;> simp_all

theorem dite_intro {p : Prop} [Decidable p] {c : p → Prop} {d : ¬p → Prop} (hc : ∀ h, c h)
    (hd : ∀ h, d h) : if h : p then c h else d h := by split <;> simp_all

/-- One goal per path through a computed weakest precondition. -/
partial def splitWP (g : MVarId) : MetaM (List MVarId) := g.withContext do
  let ty ← reduceCtorProjs (← g.getType)
  let ty := ty.consumeMData
  if ty.isConstOf ``True then
    g.assign (mkConst ``True.intro)
    return []
  if ty.isForall then
    let (_, g) ← g.intro1P
    return ← splitWP g
  if ty.isAppOf ``List.foldr then
    return ← splitWP (← g.replaceTargetDefEq (← whnf ty))
  for lem in [``And.intro, ``ite_intro, ``dite_intro] do
    if let some gs ← observing? (applyExact g (← mkConstWithFreshMVarLevels lem)) then
      return ← gs.flatMapM splitWP
  return [g]

def walkCost' (extras : Array Term) (goal : MVarId) : TermElabM (List MVarId) := do
  let goal ← toAlways goal
  goal.withContext do
  let ty ← instantiateMVars (← goal.getType)
  let #[_, g, post] := ty.getAppArgs | throwError "cost_bound': internal error"
  let gTy ← instantiateMVars (← inferType g)
  let spec := mkApp (← mkAppOptM ``Obs.spec #[none, none, none, none, none, none,
    some (mkConst ``SPMF.Cost.alwaysObs [← getDecLevel gTy]), none, some g]) post
  let wp ← mkFreshExprMVar (mkSort 0)
  let structural ← mkFreshExprMVar (← mkAppM ``LE.le #[wp, spec])
  let rest ← walk extras structural.mvarId!
  let wpGoal ← mkFreshExprMVar (← instantiateMVars wp)
  goal.assign (mkApp structural wpGoal)
  ((← splitWP wpGoal.mvarId!) ++ rest).mapM fun g => tidy g

syntax "cost_bound'" (" [" term,* "]")? : tactic
elab_rules : tactic
  | `(tactic| cost_bound' $[[$args,*]]?) => withMainContext do
    replaceMainGoal (← walkCost' ((args.map (·.getElems)).getD #[]) (← getMainGoal))

private partial def mkAdmissible (gTy : Expr) (post : Array Expr → MetaM Expr)
    (ys : Array Expr := #[]) : MetaM Expr := do
  match ← whnf gTy with
  | .forallE n d b _ =>
    withLocalDeclD n d fun y => do
      let inner ← mkAdmissible (b.instantiate1 y) post (ys.push y)
      let P ← mkLambdaFVars #[y] (← whnfR (← inferType inner)).appArg!
      mkAppOptM ``admissible_pi_apply
        #[d, ← mkLambdaFVars #[y] (b.instantiate1 y), none, P, ← mkLambdaFVars #[y] inner]
  | _ => mkAppM ``SPMF.Cost.admissible_Always #[← post ys]

/-- `cost_fixpoint`, with `walkCost'` for its walk. -/
syntax "cost_fixpoint'" (" [" term,* "]")? : tactic
elab_rules : tactic
  | `(tactic| cost_fixpoint' $[[$extras,*]]?) => withMainContext do
    let extras := (extras.map (·.getElems)).getD #[]
    let goal ← toAlways (← getMainGoal)
    goal.withContext do
    let ty ← instantiateMVars (← goal.getType)
    let #[_, x, post] := ty.getAppArgs | throwError "internal error"
    let some gen := x.getAppFn.constName? | throwError "expected a generator"
    let some (indName, seed) ← fixpointSeed? gen
      | let [goal] ← Lean.Elab.Tactic.run goal (evalTactic (← `(tactic| unfold $(mkIdent gen))))
          | throwError "could not unfold"
        replaceMainGoal (← walkCost' extras goal)
        return
    let ind ← mkConstWithFreshMVarLevels indName
    let (xs, _, concl) ← forallMetaTelescope (← inferType ind)
    let some step := xs.back? | throwError "internal error"
    let adm := xs[xs.size - 2]!
    let F := concl.appArg!
    let fTy ← whnf (← inferType F)
    let args := x.getAppArgs
    forallTelescope fTy fun ys _ => do
      let target := (seed.zip ys).foldl (fun as (k, y) => as.set! k y) args
      unless ← isDefEq (mkAppN F ys).headBeta (mkAppN x.getAppFn target) do
        throwError "could not match the fixpoint"
    let seedArgs := seed.map (args[·]!)
    let seedFVars := seedArgs.filter (·.isFVar)
    let postAt (ys : Array Expr) : MetaM Expr := do
      let ys := (seedArgs.zip ys).filterMap fun (a, y) => if a.isFVar then some y else none
      instantiateMVars (post.replaceFVars seedFVars ys)
    let gTy ← inferType F
    let motive ← withLocalDeclD `g gTy fun g => do
      mkLambdaFVars #[g] (← forallTelescope fTy fun ys _ => do
        mkForallFVars ys (← mkAppM ``SPMF.Cost.Always #[mkAppN g ys, ← postAt ys]))
    unless ← isDefEq concl.appFn! motive do throwError "motive"
    unless ← isDefEq adm (← mkAdmissible gTy postAt) do throwError "admissible"
    let pf := mkAppN (mkAppN ind xs) seedArgs
    unless ← isDefEq (← inferType pf) ty do throwError "induction"
    goal.assign pf
    let recName ← forallBoundedTelescope (← inferType step) (some 1) fun rs _ =>
      rs[0]!.fvarId!.getUserName
    let (_, s) ← step.mvarId!.introN 2 [recName.eraseMacroScopes, `ih]
    let (_, s) ← s.introN seed.size (← seed.mapM (binderName gen ·)).toList
    let s ← s.tryClearMany (seedFVars.map (·.fvarId!))
    let s ← s.withContext do s.replaceTargetDefEq (← Core.betaReduce (← instantiateMVars (← s.getType)))
    replaceMainGoal (← walkCost' extras s)

end Basalt.CostGate
