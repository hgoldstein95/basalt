/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt.SPMF.MassBound
import Basalt.SPMF.Termination

/-!
# The `mass_fixpoint` Tactic

`mass_fixpoint` reduces a `.terminates` law to the termination criterion of `Termination.lean`: it
builds the family over the generator's seed, unfolds one step, and runs `mass_bound`. The list
combinators' termination facts live here because they are proved with it.
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

/-- `mass_fixpoint using hF` proves `IsAlmostSurelyTerminating (gen a₁ … aₙ)` (or `SPMF.IsPMF _`)
from a certificate `hF : LfpIsOne F`. The seed is the arguments some recursive call of `gen`
changes. It unfolds one step of `gen` and runs `mass_bound` (extra facts go in
`mass_fixpoint [h₁, h₂] using hF`), leaving the `ℝ≥0∞` goal `F c ≤ <bound>` with `c`,
`hc1 : c ≤ 1`, `hrec : ∀ j, c ≤ (gen … j …).mass`, and the seed, under its binder names, in context.
Without `using`, `F` is the computed bound itself and the goal left is `LfpIsOne F`
(`SPMF.LfpIsOne.mono` reduces it to a named certificate).

`mass_fixpoint per_seed` goes through `SPMF.IsPMF_of_lfp_eq_one` instead, for a certificate over the
seed (`LfpIsOne.ranking`): `c : Seed → ℝ≥0∞`, `hrec : ∀ j, c j ≤ (gen … j …).mass`, and the goal
`T c seed ≤ <bound>`; without `using`, `T` is the computed bound as a function of `c` and the seed.
A certificate over the seed selects this mode without the keyword. -/
syntax (name := massFixpointTac)
  "mass_fixpoint" (&" per_seed")? (" [" term,* "]")? (" using " term)? : tactic

elab_rules : tactic
  | `(tactic| mass_fixpoint $[per_seed%$perSeedTk]? $[[$extras,*]]? $[using $cert]?) =>
  withMainContext do
    let goal ← getMainGoal
    let ty := (← instantiateMVars (← goal.getType)).consumeMData
    let some x := (if ty.isAppOfArity `IsAlmostSurelyTerminating 2 then some ty.appArg!
        else if ty.isAppOfArity ``SPMF.IsPMF 2 then some ty.appArg! else none)
      | throwError "mass_fixpoint: expected a goal `IsAlmostSurelyTerminating (gen …)`, \
          got{indentExpr ty}"
    let some gen := x.getAppFn.constName?
      | throwError "mass_fixpoint: expected a generator applied to its arguments, got{indentExpr x}"
    if isCombinator (← getEnv) gen then
      throwError "mass_fixpoint: `{gen}` is a combinator, not a generator definition; prove \
        `SPMF.IsPMF` of a combinator term with `SPMF.IsPMF.of_one_le` and `mass_bound`"
    let args := x.getAppArgs
    let seed ← match ← fixpointSeed? gen with
      | some (_, seed) => pure seed
      | none => do
        if ← isRecursiveDefinition gen then
          throwError "mass_fixpoint: `{gen}` is recursive but not a `partial_fixpoint`; induct on \
            its decreasing argument, unfold it, and apply `SPMF.IsPMF.of_one_le` and `mass_bound`"
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
          another; apply `SPMF.IsPMF_of_lfp_eq_one_uniform` to an explicit family instead"
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
    let crit ← mkAppM (if perSeed then ``SPMF.IsPMF_of_lfp_eq_one
      else ``SPMF.IsPMF_of_lfp_eq_one_uniform) #[family, hF]
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
    match extras with
    | some extras => evalTactic (← `(tactic| mass_bound [$extras,*]))
    | none => evalTactic (← `(tactic| mass_bound))
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

/-- If a generator `g` is an SPMF, then `listOf g` is also an SPMF. -/
theorem IsPMF_listOf {g : SPMF α} (hg : IsPMF g) : IsPMF (listOf g) := by
  mass_fixpoint using LfpIsOne.affine (m := 1 / 2) (by norm_num)
  simp [ENNReal.one_sub_inv_two]

/-- If a generator `g` is an SPMF, then `nonEmptyListOf g` is also an SPMF. -/
theorem IsPMF_nonEmptyListOf {g : SPMF α} (hg : IsPMF g) : IsPMF (nonEmptyListOf g) := by
  mass_fixpoint using LfpIsOne.affine (m := 1 / 2) (by norm_num)
  simp [ENNReal.one_sub_inv_two]

/-- An unbounded-length list only passes termination through: its bound is `1` exactly when its
element generator's is, which is the shape that still chains when that generator is a bind. -/
@[gen_rule]
theorem le_mass_listOf {g : SPMF α} {c : ℝ≥0∞} (hg : c ≤ g.mass) :
    (if 1 ≤ c then 1 else 0 : ℝ≥0∞) ≤ (listOf g).mass := by
  split
  · exact (IsPMF_listOf (le_antisymm (mass_le_one g) (‹1 ≤ c›.trans hg))).ge
  · exact zero_le

@[gen_rule]
theorem le_mass_nonEmptyListOf {g : SPMF α} {c : ℝ≥0∞} (hg : c ≤ g.mass) :
    (if 1 ≤ c then 1 else 0 : ℝ≥0∞) ≤ (nonEmptyListOf g).mass := by
  split
  · exact (IsPMF_nonEmptyListOf (le_antisymm (mass_le_one g) (‹1 ≤ c›.trans hg))).ge
  · exact zero_le

end combinators

end SPMF
