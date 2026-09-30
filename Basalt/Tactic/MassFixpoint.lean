/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt.Laws
import Basalt.Walk.Mass

/-!
# The `mass_fixpoint` Tactic

`mass_fixpoint` reduces a `.terminates` law to its criterion,
`IsAlmostSurelyTerminating.of_lfpIsOne`: it builds the family over the generator's seed, unfolds one
step, and walks it. The termination facts of the list combinators and of the retry loops
(`suchThat`, QuickCheck's `suchThatFrom`) live here because they are proved with it.
-/

open ENNReal RandomChoice

namespace Basalt.MassFixpoint

open Lean Meta Elab Tactic Basalt.Walk

/-- Right-nested tuple of `es` (`Unit` when empty), with its type. -/
private def mkTuple (es : Array Expr) : MetaM Expr := do
  let some last := es.back? | return mkConst ``Unit.unit
  es.pop.foldrM (fun e acc => mkAppM ``Prod.mk #[e, acc]) last

/-- The components of a right-nested tuple `s` of `n` values. -/
private def untuple (s : Expr) : Nat → MetaM (Array Expr)
  | 0 => return #[]
  | 1 => return #[s]
  | n + 1 => do
    return #[← mkAppM ``Prod.fst #[s]] ++ (← untuple (← mkAppM ``Prod.snd #[s]) n)

/-- Proves `IsAlmostSurelyTerminating (gen …)` for a recursive `gen`.

`mass_fixpoint [h₁.obs, …] using hF` takes a certificate `hF : LfpIsOne F` and the callees'
termination facts, unfolds `gen` once, and leaves one arithmetic goal, `F c ≤ <bound>`, where
`<bound>` is a lower bound on the mass of the unfolded step. In context:
* `c`, a lower bound on the mass of every recursive call (`hrec`), with `hc1 : c ≤ 1`;
* the arguments the recursion changes, under their own names.

Without `using`, the goal left is `LfpIsOne F` for the computed `F` instead. With `per_seed` (or a
certificate over the arguments), `c` is a function of the arguments: one bound per call. -/
syntax (name := massFixpointTac)
  "mass_fixpoint" (&" per_seed")? (walkFacts)? (" using " term)? : tactic

elab_rules : tactic
  | `(tactic| mass_fixpoint $[per_seed%$perSeedTk]? $[$fs]? $[using $cert]?) =>
  withMainContext do
    let goal ← getMainGoal
    let ty ← whnfR (← instantiateMVars (← goal.getType))
    let some x := (if ty.isAppOfArity ``IsAlmostSurelyTerminating 2 then some ty.appArg! else none)
      | throwError "mass_fixpoint: expected a goal `IsAlmostSurelyTerminating (gen …)`, \
          got{indentExpr ty}"
    let some gen := x.getAppFn.constName?
      | throwError "mass_fixpoint: expected a generator applied to its arguments, got{indentExpr x}"
    if isCombinator (← getEnv) gen then
      throwError "mass_fixpoint: `{gen}` is a combinator, not a generator definition; prove the \
        termination of a combinator term with `rw [IsAlmostSurelyTerminating.iff_obs]` and `walk`"
    let args := x.getAppArgs
    let seed ← match ← fixpointSeed? gen with
      | some (_, seed) => pure seed
      | none => do
        if ← isRecursiveDefinition gen then
          throwError "mass_fixpoint: `{gen}` is recursive but not a `partial_fixpoint`; induct on \
            its decreasing argument, `rw [IsAlmostSurelyTerminating.iff_obs]`, unfold it, and \
            `walk`"
        pure #[]
    unless seed.all (· < args.size) do
      throwError "mass_fixpoint: `{gen}` is not fully applied in{indentExpr x}"
    -- The family over the seed.
    let seedTy ← match seed.size with
      | 0 => pure (mkConst ``Unit)
      | _ => do
        let tys ← seed.mapM fun k => inferType args[k]!
        tys.pop.foldrM (fun t acc => mkAppM ``Prod #[t, acc]) tys.back!
    let family ← withLocalDeclD `s seedTy fun s => do
      let comps ← untuple s seed.size
      let mut args' := args
      for h : k in [:seed.size] do
        args' := args'.set! seed[k] comps[k]!
      let body := mkAppN x.getAppFn args'
      unless ← isTypeCorrect body do
        throwError "mass_fixpoint: the seed of `{gen}` has an argument whose type depends on \
          another; apply `IsAlmostSurelyTerminating.of_lfpIsOne_uniform` to an explicit family \
          instead"
      mkLambdaFVars #[s] body
    let point ← mkTuple (seed.map (args[·]!))
    -- The certificate, and the mode it selects.
    let ennreal := mkConst ``ENNReal
    let hCert? ← cert.mapM fun cert => do
      let hF ← Tactic.elabTerm cert none
      let hFTy ← whnfR (← instantiateMVars (← inferType hF))
      unless hFTy.isAppOfArity ``SPMF.LfpIsOne 4 do
        throwError "mass_fixpoint: expected a certificate `LfpIsOne F`, got{indentExpr hF}\n\
          of type{indentExpr hFTy}"
      unless hFTy.appArg!.isLambda do
        throwError "mass_fixpoint: the certificate{indentExpr hF}\ndoes not determine its bound; \
          name it, or omit `using` and prove the `LfpIsOne` goal about the computed bound"
      return (hF, hFTy.appArg!, ← isDefEq (hFTy.getArg! 0) ennreal)
    let perSeed := perSeedTk.isSome || hCert?.any (!·.2.2)
    -- `F` (or `T`) is opaque, so that nothing but the final step (not `conv`'s closing `rfl`) can
    -- choose it.
    let fnTy ← if perSeed then do
        let vec ← mkArrow seedTy ennreal
        mkArrow vec vec
      else mkArrow ennreal ennreal
    let F ← mkFreshExprSyntheticOpaqueMVar fnTy
    let hF ← match hCert? with
      | some (hF, T, _) =>
        unless ← isDefEq (← inferType F) (← inferType T) do
          throwError "mass_fixpoint: the certificate is over{indentExpr (← inferType T)}\n\
            but the seed of `{gen}` needs one over{indentExpr fnTy}"
        F.mvarId!.assign T
        pure hF
      | none => mkFreshExprSyntheticOpaqueMVar (← mkAppM ``SPMF.LfpIsOne #[F]) `certificate
    let crit ← mkAppM (if perSeed then ``IsAlmostSurelyTerminating.of_lfpIsOne
      else ``IsAlmostSurelyTerminating.of_lfpIsOne_uniform) #[family, hF]
    let .forallE _ stepTy _ _ ← whnfR (← inferType crit) | throwError "mass_fixpoint: internal error"
    let step ← mkFreshExprSyntheticOpaqueMVar stepTy
    let pf := mkApp2 crit step point
    unless ← isDefEq (← inferType pf) ty do
      throwError "mass_fixpoint: could not match the goal to the family{indentExpr family}"
    goal.assign pf
    -- One step: `c`, `hc1`, `hrec`, the seed.
    let seedNames ← seed.mapM (binderName gen ·)
    let (_, step) ← step.mvarId!.introN 3 [`c, `hc1, `hrec]
    let (sv, step) ← step.intro (if seedNames.size == 1 then seedNames[0]! else `seed)
    let step ← step.withContext do
      let some hrec := (← getLCtx).findFromUserName? `hrec | throwError "mass_fixpoint: internal error"
      let step ← step.changeLocalDecl hrec.fvarId (← reduceCtorProjs hrec.type)
      step.change (← reduceCtorProjs (← step.getType))
    -- The goal's own seed values are replaced by the introduced seed.
    let step ← step.tryClearMany (seed.filterMap fun k => args[k]!.fvarId?)
    let step ← match seedNames.size with
      | 0 => step.clear sv
      | 1 => pure step
      | _ => do
        let ids := seedNames.map mkIdent
        let [step] ← Lean.Elab.Tactic.run step
            (evalTactic (← `(tactic| obtain ⟨$[$ids],*⟩ := $(mkIdent `seed))))
          | throwError "mass_fixpoint: internal error"
        step.withContext do step.change (← reduceCtorProjs (← step.getType))
    replaceMainGoal [step]
    -- Unfold on the right only, then bound.
    let genId := mkIdent gen
    evalTactic (← `(tactic| first
      | conv_rhs => rw [$genId:ident]
      | conv_rhs => unfold $genId:ident))
    let facts := walkFacts.terms fs
    for t in facts do checkFact t
    replaceMainGoal (← walkGoal facts (← getMainGoal))
    if cert.isNone then
      let arith ← getMainGoal
      arith.withContext do
        let some (_, _, _, rhs) := (← instantiateMVars (← arith.getType)).app4? ``LE.le
          | throwError "mass_fixpoint: internal error"
        let lctx ← getLCtx
        let some c := lctx.findFromUserName? `c | throwError "mass_fixpoint: internal error"
        let lam ← if perSeed then
            -- The seed's components, as introduced, become projections of a seed variable.
            let comps ← match seedNames.size with
              | 0 => pure #[]
              | _ => seedNames.mapM fun n => do
                let some d := lctx.findFromUserName? n | throwError "mass_fixpoint: internal error"
                pure d.toExpr
            withLocalDeclD (if seedNames.size == 1 then seedNames[0]! else `seed) seedTy fun s => do
              let rhs := rhs.replaceFVars comps (← untuple s comps.size)
              mkLambdaFVars #[c.toExpr, s] rhs
          else mkLambdaFVars #[c.toExpr] rhs
        let outer := (← F.mvarId!.getDecl).lctx
        if lam.hasAnyFVar (!outer.contains ·) then
          throwError "mass_fixpoint: the computed bound depends on the seed, so it is no single \
            `F c`:{indentExpr rhs}\nName a certificate with `mass_fixpoint using _`, or take the \
            bound as a function of the seed with `mass_fixpoint per_seed`."
        F.mvarId!.assign lam
        arith.assign (← mkAppM ``le_refl #[rhs])
      replaceMainGoal [hF.mvarId!]

end Basalt.MassFixpoint

namespace SPMF

section combinators

variable {α : Type*}

theorem isAlmostSurelyTerminating_listOf {g : SPMF α} (hg : IsAlmostSurelyTerminating g) :
    IsAlmostSurelyTerminating (listOf g) := by
  mass_fixpoint [hg.obs] using LfpIsOne.affine (m := 1 / 2) (by norm_num)
  simp [ENNReal.one_sub_inv_two, div_eq_mul_inv, add_mul, mul_comm]

theorem isAlmostSurelyTerminating_nonEmptyListOf {g : SPMF α} (hg : IsAlmostSurelyTerminating g) :
    IsAlmostSurelyTerminating (nonEmptyListOf g) := by
  mass_fixpoint [hg.obs] using LfpIsOne.affine (m := 1 / 2) (by norm_num)
  simp [ENNReal.one_sub_inv_two, div_eq_mul_inv, add_mul, mul_comm]

private theorem ite_le_listOf {g : SPMF α} {c : ℝ≥0∞} (hg : c ≤ expectObs.spec g fun _ => 1) :
    (if 1 ≤ c then 1 else 0) ≤ expectObs.spec (listOf g) fun _ => 1 := by
  split
  · exact (isAlmostSurelyTerminating_listOf
      (IsAlmostSurelyTerminating.iff_obs.mpr (‹1 ≤ c›.trans hg))).obs
  · exact zero_le

private theorem ite_le_nonEmptyListOf {g : SPMF α} {c : ℝ≥0∞}
    (hg : c ≤ expectObs.spec g fun _ => 1) :
    (if 1 ≤ c then 1 else 0) ≤ expectObs.spec (nonEmptyListOf g) fun _ => 1 := by
  split
  · exact (isAlmostSurelyTerminating_nonEmptyListOf
      (IsAlmostSurelyTerminating.iff_obs.mpr (‹1 ≤ c›.trans hg))).obs
  · exact zero_le

/-- An unbounded-length list only passes termination through: its bound is `1` exactly when its
element generator's is, which is the shape that still chains when that generator is a bind. -/
@[gen_rule]
theorem le_expect_listOf {g : SPMF α} {c d : ℝ≥0∞} {p : List α → ℝ≥0∞}
    (hg : c ≤ expectObs.spec g fun _ => 1) (hp : ∀ a, p a = d) :
    (if 1 ≤ c then 1 else 0) * d ≤ expectObs.spec (listOf g) p :=
  le_expect_of_le (ite_le_listOf hg) hp

@[gen_rule, inherit_doc le_expect_vectorOf_iInf]
theorem le_expect_listOf_iInf {g : SPMF α} {c : ℝ≥0∞} {p : List α → ℝ≥0∞}
    (hg : c ≤ expectObs.spec g fun _ => 1) :
    (if 1 ≤ c then 1 else 0) * ⨅ a, p a ≤ expectObs.spec (listOf g) p :=
  le_expect_iInf_of_le (ite_le_listOf hg)

@[gen_rule, inherit_doc le_expect_listOf]
theorem le_expect_nonEmptyListOf {g : SPMF α} {c d : ℝ≥0∞} {p : List α → ℝ≥0∞}
    (hg : c ≤ expectObs.spec g fun _ => 1) (hp : ∀ a, p a = d) :
    (if 1 ≤ c then 1 else 0) * d ≤ expectObs.spec (nonEmptyListOf g) p :=
  le_expect_of_le (ite_le_nonEmptyListOf hg) hp

@[gen_rule, inherit_doc le_expect_vectorOf_iInf]
theorem le_expect_nonEmptyListOf_iInf {g : SPMF α} {c : ℝ≥0∞} {p : List α → ℝ≥0∞}
    (hg : c ≤ expectObs.spec g fun _ => 1) :
    (if 1 ≤ c then 1 else 0) * ⨅ a, p a ≤ expectObs.spec (nonEmptyListOf g) p :=
  le_expect_iInf_of_le (ite_le_nonEmptyListOf hg)

/-- One step of rejection sampling: a draw accepted with chance at least `1 - r`, or else a retry of
mass at least `c`. -/
private theorem le_expect_accept {g : SPMF α} {p : α → Bool} {r c : ℝ≥0∞}
    (hg : IsAlmostSurelyTerminating g) (hr : expectObs.spec g (fun a => if p a then 0 else 1) ≤ r)
    (hr1 : r ≤ 1) (hc : c ≤ 1) :
    (1 - r) + r * c ≤ expectObs.spec g fun a => if p a then 1 else c := by
  have hsum : (expectObs.spec g fun a => if p a then 1 else c)
      + (1 - c) * expectObs.spec g (fun a => if p a then 0 else 1) = 1 := by
    show expect g _ + (1 - c) * expect g _ = 1
    rw [← expect_mul_left, ← expect_add,
      show (fun a => (if p a then 1 else c) + (1 - c) * if p a then 0 else 1) = fun _ => (1 : ℝ≥0∞)
        from funext fun a => by split <;> simp [add_tsub_cancel_of_le hc],
      expect_one]
    exact hg
  have hone : (1 - r) + r * c + (1 - c) * r = 1 := by
    rw [add_assoc, mul_comm (1 - c), ← mul_add, add_tsub_cancel_of_le hc, mul_one,
      tsub_add_cancel_of_le hr1]
  refine ENNReal.le_of_add_le_add_right (a := (1 - c) * r)
    (ENNReal.mul_ne_top (ENNReal.sub_ne_top ENNReal.one_ne_top)
      (ne_top_of_le_ne_top ENNReal.one_ne_top hr1)) ?_
  calc (1 - r) + r * c + (1 - c) * r = 1 := hone
    _ = _ := hsum.symm
    _ ≤ _ := by gcongr

theorem isAlmostSurelyTerminating_suchThat {g : SPMF α} {p : α → Bool} {r : ℝ≥0∞}
    (hg : IsAlmostSurelyTerminating g) (hr : expectObs.spec g (fun a => if p a then 0 else 1) ≤ r)
    (hr1 : r < 1) : IsAlmostSurelyTerminating (suchThat g p) := by
  mass_fixpoint [le_expect_accept hg hr hr1.le hc1] using LfpIsOne.affine (m := r) hr1
  exact le_rfl

private theorem ite_le_suchThat {g : SPMF α} {p : α → Bool} {c r : ℝ≥0∞}
    (hg : c ≤ expectObs.spec g fun _ => 1)
    (hr : expectObs.spec g (fun a => if p a then 0 else 1) ≤ r) :
    (if 1 ≤ c ∧ r < 1 then 1 else 0) ≤ expectObs.spec (suchThat g p) fun _ => 1 := by
  split
  · rename_i h
    exact (isAlmostSurelyTerminating_suchThat
      (IsAlmostSurelyTerminating.iff_obs.mpr (h.1.trans hg)) hr h.2).obs
  · exact zero_le

/-- Rejection sampling terminates when `g` does and rejects with a chance `r < 1`, which the bound
asks of the arithmetic: a fact about how often `g` rejects closes `hr`. -/
@[gen_rule]
theorem le_expect_suchThat {g : SPMF α} {p : α → Bool} {c r d : ℝ≥0∞} {post : α → ℝ≥0∞}
    (hg : c ≤ expectObs.spec g fun _ => 1)
    (hr : expectObs.spec g (fun a => if p a then 0 else 1) ≤ r) (hp : ∀ a, post a = d) :
    (if 1 ≤ c ∧ r < 1 then 1 else 0) * d ≤ expectObs.spec (suchThat g p) post :=
  le_expect_of_le (ite_le_suchThat hg hr) hp

@[gen_rule, inherit_doc le_expect_vectorOf_iInf]
theorem le_expect_suchThat_iInf {g : SPMF α} {p : α → Bool} {c r : ℝ≥0∞} {post : α → ℝ≥0∞}
    (hg : c ≤ expectObs.spec g fun _ => 1)
    (hr : expectObs.spec g (fun a => if p a then 0 else 1) ≤ r) :
    (if 1 ≤ c ∧ r < 1 then 1 else 0) * ⨅ a, post a ≤ expectObs.spec (suchThat g p) post :=
  le_expect_iInf_of_le (ite_le_suchThat hg hr)

/-! ### QuickCheck's retry loop

`suchThatFrom gs f n` draws from `gs` at the sizes `n`, `n + 1`, …, each round starting one size
later, so every draw is at a size from `n` on: it terminates when each of those does and rejects
with a chance at most `r < 1`. -/

section suchThatFrom

open QuickCheck

variable {α β : Type} {gs : Nat → SPMF α} {f : α → Option β} {n : Nat} {r c : ℝ≥0∞}

private theorem le_one_sub_add_mul (hr1 : r ≤ 1) (hc : c ≤ 1) : c ≤ (1 - r) + r * c :=
  calc c = (1 - r) * c + r * c := by rw [← add_mul, tsub_add_cancel_of_le hr1, one_mul]
    _ ≤ (1 - r) + r * c := by gcongr; exact mul_le_of_le_one_right' hc

/-- One round of `trySizes`, each attempt from size `n` on accepted with chance at least `1 - r`:
at least `c` in all when a round that returns nothing is worth `c`, and at least
`(1 - r) + r * c` when it makes a draw. -/
private theorem le_expect_trySizes_rounds
    (hg : ∀ j, n ≤ j → IsAlmostSurelyTerminating (gs j))
    (hr : ∀ j, n ≤ j → expectObs.spec (gs j) (fun a => if (f a).isSome then 0 else 1) ≤ r)
    (hr1 : r ≤ 1) (hc : c ≤ 1) :
    ∀ k m, n ≤ m →
      c ≤ expect (trySizes gs f m k) (fun o => if o.isSome then 1 else c) ∧
      (0 < k → (1 - r) + r * c ≤ expect (trySizes gs f m k) fun o => if o.isSome then 1 else c) := by
  intro k
  induction k with
  | zero =>
    intro m _
    refine ⟨?_, fun h => absurd h (Nat.lt_irrefl 0)⟩
    rw [trySizes, expect_pure]
    exact le_rfl
  | succ k ih =>
    intro m hm
    have hstep : (1 - r) + r * c ≤ expect (trySizes gs f m (k + 1))
        (fun o => if o.isSome then 1 else c) := by
      rw [trySizes, expect_bind]
      refine (le_expect_accept (p := fun a => (f a).isSome) (hg m hm) (hr m hm) hr1 hc).trans
        (expect_mono fun a => ?_)
      split
      · simp [expect_pure, *]
      · exact (ih (m + 1) (by omega)).1
    exact ⟨(le_one_sub_add_mul hr1 hc).trans hstep, fun _ => hstep⟩

theorem isAlmostSurelyTerminating_suchThatFrom
    (hg : ∀ j, n ≤ j → IsAlmostSurelyTerminating (gs j))
    (hr : ∀ j, n ≤ j → expectObs.spec (gs j) (fun a => if (f a).isSome then 0 else 1) ≤ r)
    (hr1 : r < 1) : IsAlmostSurelyTerminating (suchThatFrom gs f n) := by
  have key := IsAlmostSurelyTerminating.of_lfpIsOne_uniform (fun s => suchThatFrom gs f (n + s))
    (LfpIsOne.affine hr1) (fun c hc hrec s => ?_) 0
  · simpa using key
  show _ ≤ expect _ _
  conv => right; rw [suchThatFrom]
  rw [expect_bind]
  refine ((le_expect_trySizes_rounds hg hr hr1.le hc (n + s + 1) (n + s) (by omega)).2
    (by omega)).trans (expect_mono fun o => ?_)
  rcases o with _ | b
  · exact hrec (s + 1)
  · simp

private theorem ite_le_suchThatFrom
    (hg : ∀ j, n ≤ j → c ≤ expectObs.spec (gs j) fun _ => 1)
    (hr : ∀ j, n ≤ j → expectObs.spec (gs j) (fun a => if (f a).isSome then 0 else 1) ≤ r) :
    (if 1 ≤ c ∧ r < 1 then 1 else 0) ≤ expectObs.spec (suchThatFrom gs f n) fun _ => 1 := by
  split
  · rename_i h
    exact (isAlmostSurelyTerminating_suchThatFrom
      (fun j hj => IsAlmostSurelyTerminating.iff_obs.mpr (h.1.trans (hg j hj))) hr h.2).obs
  · exact zero_le

/-- As for `suchThat`: a fact about how often `gs` rejects at each size from `n` on closes `hr`. -/
@[gen_rule]
theorem le_expect_suchThatFrom {d : ℝ≥0∞} {post : β → ℝ≥0∞}
    (hg : ∀ j, n ≤ j → c ≤ expectObs.spec (gs j) fun _ => 1)
    (hr : ∀ j, n ≤ j → expectObs.spec (gs j) (fun a => if (f a).isSome then 0 else 1) ≤ r)
    (hp : ∀ a, post a = d) :
    (if 1 ≤ c ∧ r < 1 then 1 else 0) * d ≤ expectObs.spec (suchThatFrom gs f n) post :=
  le_expect_of_le (ite_le_suchThatFrom hg hr) hp

@[gen_rule, inherit_doc le_expect_vectorOf_iInf]
theorem le_expect_suchThatFrom_iInf {post : β → ℝ≥0∞}
    (hg : ∀ j, n ≤ j → c ≤ expectObs.spec (gs j) fun _ => 1)
    (hr : ∀ j, n ≤ j → expectObs.spec (gs j) (fun a => if (f a).isSome then 0 else 1) ≤ r) :
    (if 1 ≤ c ∧ r < 1 then 1 else 0) * ⨅ a, post a ≤ expectObs.spec (suchThatFrom gs f n) post :=
  le_expect_iInf_of_le (ite_le_suchThatFrom hg hr)

/-- `QuickCheck.suchThat p`, at a size, is `suchThatFrom` of `Option.guard p`: its rejections are
stated through `p`. -/
@[gen_rule]
theorem le_expect_suchThatFrom_guard {p : α → Bool} {d : ℝ≥0∞} {post : α → ℝ≥0∞}
    (hg : ∀ j, n ≤ j → c ≤ expectObs.spec (gs j) fun _ => 1)
    (hr : ∀ j, n ≤ j → expectObs.spec (gs j) (fun a => if p a then 0 else 1) ≤ r)
    (hp : ∀ a, post a = d) :
    (if 1 ≤ c ∧ r < 1 then 1 else 0) * d ≤ expectObs.spec (suchThatFrom gs (Option.guard p) n) post :=
  le_expect_suchThatFrom hg (fun j hj => by simpa [Option.isSome_guard] using hr j hj) hp

@[gen_rule, inherit_doc le_expect_suchThatFrom_guard]
theorem le_expect_suchThatFrom_guard_iInf {p : α → Bool} {post : α → ℝ≥0∞}
    (hg : ∀ j, n ≤ j → c ≤ expectObs.spec (gs j) fun _ => 1)
    (hr : ∀ j, n ≤ j → expectObs.spec (gs j) (fun a => if p a then 0 else 1) ≤ r) :
    (if 1 ≤ c ∧ r < 1 then 1 else 0) * ⨅ a, post a
      ≤ expectObs.spec (suchThatFrom gs (Option.guard p) n) post :=
  le_expect_suchThatFrom_iInf hg fun j hj => by simpa [Option.isSome_guard] using hr j hj

end suchThatFrom

end combinators

end SPMF
