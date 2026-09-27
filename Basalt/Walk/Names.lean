/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Lean.Meta.Tactic.Replace
import Basalt.Obs.Basic

/-!
# The Walker's Names

This machinery ensures that the walk does not mangle intermediate value names.
-/

open Lean Meta

namespace Basalt.Walk

/-- The binder names of a postcondition, its value and, at the cost family, its cost: those of the
first argument of `ty`, or of an `O.spec …` among its arguments, that is a lambda. -/
partial def postNames (ty : Expr) : Option (Name × Option Name) :=
  ty.getAppArgs.findSome? fun
    | .lam v _ (.lam n _ _ _) _ => some (v.eraseMacroScopes, some n.eraseMacroScopes)
    | .lam v _ _ _ => some (v.eraseMacroScopes, none)
    | e => if e.isAppOf ``Obs.spec then postNames e else none

/-- `ty`, a rule's or a bridge's statement, with the binders of the bound it computes named after
the generator: `∀ a n, R a n → p a n` and `∀ x hx, d x hx` become `∀ v n_v h_v, …` and `∀ v h_v, …`,
and `∃ x hx, d x hx` and `∃ a n, …` become `∃ v h_v, …` and `∃ v n_v, …`. The paths of a
`Prop`-valued bound are introduced under these names, and a user has to be able to refer to a drawn
value. -/
def nameBound (ty : Expr) : Option (Name × Option Name) → Expr
  | none => ty
  | some (v, c) =>
    let h := Name.mkSimple s!"h_{v}"
    let c := c.getD (.mkSimple s!"n_{v}")
    let rename : Expr → Expr
      | .forallE _ d₁ (.forallE _ d₂ (.forallE _ d₃ b bi₃) bi₂) bi₁ =>
        if d₂.isConstOf ``Nat then
          .forallE v d₁ (.forallE c d₂ (.forallE h d₃ b bi₃) bi₂) bi₁
        else .forallE v d₁ (.forallE h d₂ (.forallE `_ d₃ b bi₃) bi₂) bi₁
      | .forallE _ d₁ (.forallE _ d₂ b bi₂) bi₁ => .forallE v d₁ (.forallE h d₂ b bi₂) bi₁
      | .app (.app (.const ``Exists us₁) t₁) (.lam _ d₁ b₁ bi₁) =>
        let b₁ := match b₁ with
          | .app (.app (.const ``Exists us₂) t₂) (.lam _ d₂ b₂ bi₂) =>
            mkApp2 (.const ``Exists us₂) t₂ (.lam (if d₂.isConstOf ``Nat then c else h) d₂ b₂ bi₂)
          | b₁ => b₁
        mkApp2 (.const ``Exists us₁) t₁ (.lam v d₁ b₁ bi₁)
      | e => e
    let rec go : Expr → Expr
      | .forallE n d b bi => .forallE n d (go b) bi
      | e =>
        if e.isAppOfArity ``LE.le 4 then
          mkAppN e.getAppFn ((e.getAppArgs.set! 2 (rename (e.getArg! 2))).set! 3
            (rename (e.getArg! 3)))
        else e
    go ty

/-- The binder name a hygienic lambda of an unfolded body carries (`(·.down.val)`, a `do` block's
`← e`). `namePremises` takes it as no hint, so what it binds is named after the goal's
postcondition, as any hint-less draw is. -/
def unfoldedBinder : Name := `_unfolded

/-- `e` with every hygienic lambda binder renamed `unfoldedBinder`. -/
partial def renameLambdas : Expr → Expr
  | .lam n d b bi =>
    .lam (if n.hasMacroScopes then unfoldedBinder else n) (renameLambdas d) (renameLambdas b) bi
  | .forallE n d b bi => .forallE n (renameLambdas d) (renameLambdas b) bi
  | .app f a => .app (renameLambdas f) (renameLambdas a)
  | .letE n t v b nd => .letE n (renameLambdas t) (renameLambdas v) (renameLambdas b) nd
  | .mdata m e => .mdata m (renameLambdas e)
  | .proj s i e => .proj s i (renameLambdas e)
  | e => e

/-- The names of the lambda arguments of `g`'s head that bind something other than `Unit`: a
continuation's `delta`, a `dite` branch's `h`. -/
private def lambdaHints (g : Expr) : Array Name :=
  g.getAppArgs.filterMap fun
    | .lam n d _ _ => if d.isConstOf ``Unit || d.isConstOf ``PUnit || d.isAppOf ``PUnit then none
        else some n.eraseMacroScopes
    | _ => none

private def prefixed (p : String) (v : Name) : Name := .mkSimple (p ++ v.toString)

/-- `t`, a rule premise, with its binders named after `hint`, the combinator's lambda argument, or
else after `post`, the goal's postcondition's binders. -/
private def nameBinders (t : Expr) (hint : Option Name) (post : Option (Name × Option Name)) :
    MetaM Expr := do
  let value? := hint <|> post.map (·.1)
  -- A postcondition of one binder has no cost to name.
  let cost? := if post.any (·.2.isNone) then none
    else if hint.isSome then value?.map (prefixed "n_") else post.bind (·.2)
  let rec go (t : Expr) (fvars : Array Expr) (v : Option Name) (k : Nat) (hintUsed : Bool) :
      MetaM Expr := do
    match t with
    | .forallE n d b bi =>
      let d := d.instantiateRev fvars
      let (n', v', k', used) ← do
        if ← isProp d then
          match v, hint, hintUsed with
          | some v, _, _ => pure (prefixed "h_" v, some v, k, hintUsed)
          | none, some h, false => pure (h, none, k, true)
          | _, _, _ => pure (if n.hasMacroScopes then `h else n, v, k, hintUsed)
        else if k == 0 then
          let v := value?.getD n
          pure (v, some v, 1, true)
        else if k == 1 then pure ((cost?.getD n), v, 2, hintUsed)
        else pure (n, v, k + 1, hintUsed)
      withLocalDecl n' bi d fun x => do
        mkForallFVars #[x] (← go b (fvars.push x) v' k' used)
    | _ =>
      let t := t.instantiateRev fvars
      unless fvars.isEmpty do return t
      -- A premise that binds nothing may still hand a postcondition on: name its binders.
      let some v := value? | return t
      -- The postcondition is an argument of the judgment, or of the `O.spec …` it is stated on.
      let renameIn (t : Expr) : Option Expr :=
        let args := t.getAppArgs
        match args.findIdx? (·.isLambda) with
        | some i =>
          match args[i]!, cost? with
          | .lam _ d₁ (.lam _ d₂ b bi₂) bi₁, some c =>
            some (mkAppN t.getAppFn (args.set! i (.lam v d₁ (.lam c d₂ b bi₂) bi₁)))
          | .lam _ d₁ b bi₁, none => some (mkAppN t.getAppFn (args.set! i (.lam v d₁ b bi₁)))
          | _, _ => none
        | none => none
      if let some t' := renameIn t then return t'
      let args := t.getAppArgs
      let some i := args.findIdx? (·.isAppOf ``Obs.spec) | return t
      let some spec := renameIn args[i]! | return t
      return mkAppN t.getAppFn (args.set! i spec)
  go t #[] none 0 false

/-- Whether premise `t` binds a drawn value: a `∀` over data, or a postcondition to hand on. -/
private def bindsValue (t : Expr) : MetaM Bool := do
  match t with
  | .forallE _ d _ _ => return !(← isProp d)
  | _ => return (postNames t).isSome

/-- `premises` renamed by `nameBinders`. The hints go one per premise when there are as many, and
otherwise, in order, to the premises that bind a value, when there are as many of those. -/
def namePremises (g? : Option Expr) (goalTy : Expr) (premises : List MVarId) :
    MetaM (List MVarId) := do
  let hints := (g?.map lambdaHints).getD #[]
  let post := postNames goalTy
  let types ← premises.mapM fun p => do instantiateMVars (← p.getType)
  let hints ← if hints.size == premises.length then pure (hints.toList.map some) else do
    let binds ← types.mapM bindsValue
    if (binds.filter id).length != hints.size then pure (types.map fun _ => none) else
      let (out, _) := binds.foldl (fun (out, rest) b =>
        if b then (out ++ [rest.head?], rest.drop 1) else (out ++ [none], rest))
        (([] : List (Option Name)), hints.toList)
      pure out
  (premises.zip (types.zip hints)).mapM fun (p, t, hint) => do
    p.replaceTargetDefEq (← nameBinders t (hint.filter (· != unfoldedBinder)) post)

/-- The tag of a shape goal that came from a draw, carrying the name of the value drawn. -/
def drawTag : Name := `_draw

/-- The user-facing name of `gen`'s `k`th binder. -/
def binderName (gen : Name) (k : Nat) : MetaM Name :=
  do forallTelescope (← getConstInfo gen).type fun xs _ => do
    let n ← xs[k]!.fvarId!.getUserName
    return n.eraseMacroScopes

end Basalt.Walk
