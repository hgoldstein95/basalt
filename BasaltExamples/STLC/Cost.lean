/-
Copyright (c) 2026 Harrison Goldstein & Ernest Ng. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein & Ernest Ng
-/
import Basalt
import Basalt.PlausibleGen
import BasaltExamples.STLC.Syntax
import BasaltExamples.STLC.GenType
import BasaltExamples.STLC.GenTerm
import BasaltExamples.STLC.TypeCheck

open RandomChoice SPMF List

/-!
# Cost Bound for `genTerm` (work in progress)

This file records the *context-aware* cost function for `genTerm` and the shape of its cost proof.
The proof itself is still `sorry`; the point of the file is to not lose the design.

## Why the bound must mention the context

`IsCostBounded g c` needs `c : Term → Nat` — a function of the *output term*. But the `App` branch
of `genTerm` (`BasaltExamples/STLC/GenTerm.lean`) spends `argTy.size` choices generating an argument
type via `genType`, and `argTy` is **not stored** in the produced `.App e1 e2`:

```
let argTy ← genType            -- costs `argTy.size` (see `genType_cost`)
let e1 ← genTerm Γ (.Fun argTy τ)
let e2 ← genTerm Γ argTy
return .App e1 e2
```

So there is no purely term-structural function that bounds the cost. The escape hatch is that this
is Church-style STLC, so **typing is unique**: `argTy` is recoverable as the type of `e2`, and
`e2 : argTy`. Concretely `argTy = typeCheck Γ e2` (the typechecker in `TypeCheck.lean` *is* the
`typeOf` we need, and `typeCheck_complete` *is* the `typeOf_of_Typing` uniqueness fact). Recovering
`argTy` requires knowing `Γ`, so the cost function threads the context.

`Term.costInCtx` must be total, so on ill-typed inputs the `App` case falls back to a default type
via `Option.getD`. That default is never observed by the cost proof: `genTerm`'s support is exactly
the well-typed terms (`genTerm_sound`), and `typeCheck_getD_of_typing` below is the *theorem* — not
a comment — witnessing that the `getD` collapses to the real type on every well-typed term,
regardless of the default. The final `IsCostBounded` guarantee is verified for every term `genTerm`
can produce; the default is invisible to it.

## The cost function

Charge one choice per `oneOf` selection plus the cost of the chosen branch, reading `genTerm`:

* `.Bool _`   : `oneOf` (1) + `genBool`/`genZero`-at-`Bool` (1)               = 2
* `.Var _`    : `oneOf` (1) + `elements` (1)                                  = 2
* `.Abs τ1 e` : `oneOf` (1) + recurse under the extended context `τ1 :: Γ`
* `.App e1 e2`: `oneOf` (1) + `genType` for `argTy` (`argTy.size`) + recurse on `e1` and `e2`

Note on `.Abs`: an `Abs` can be produced by *either* the recursive `Abs` branch *or* `genZero`.
The bound below charges the recursive-branch cost, which dominates the `genZero` path (`genZero`
makes exactly one choice), so it is a valid upper bound for both.
-/

/-- Context-aware cost bound for `genTerm Γ`. Counts the random choices `genTerm` makes to
    reproduce a term, recovering each discarded application-argument type from `typeCheck`. -/
def Term.costInCtx (Γ : Ctx) (e : Term) : Nat :=
  match e with
  | .Bool _    => 2
  | .Var _     => 2
  | .Abs τ1 e  => 1 + Term.costInCtx (τ1 :: Γ) e
  | .App e1 e2 =>
      let e1_cost := Term.costInCtx Γ e1
      let e2_cost := Term.costInCtx Γ e2
      let genType_cost := ((typeCheck Γ e2).getD .Bool).size
      1 + genType_cost + e1_cost + e2_cost

/-- On a well-typed term the `Option.getD` in `Term.costInCtx`'s `App` case collapses to the term's
    actual type, whatever the default `d` is. This is the formal replacement for the "the default is
    never hit" side remark: `genTerm`'s outputs are well-typed (`genTerm_sound`), so the cost proof
    only ever evaluates `costInCtx` where this lemma applies. -/
theorem typeCheck_getD_of_typing {d : Ty} (h : Typing Γ e τ) :
    (typeCheck Γ e).getD d = τ := by
  rw [typeCheck_complete h]; rfl

/-- `genTerm Γ τ` makes at most `Term.costInCtx Γ` random choices.

    Recipe (WORKFLOW.md, Recipe 3, indexed form):

    ```
    open Lean.Order in
    delta genTerm
    apply fix_induct
      (motive := fun g => ∀ Γ τ, IsBounded (g Γ τ) (Term.costInCtx Γ)) _ ?admissible ?step
    case admissible => apply admissible_pi_apply _ fun _ => admissible_IsBounded _
    case step =>
      intro genTerm_rec ih
      intro Γ τ; rw [IsBounded_iff]; rintro ⟨v, n⟩ hmem
      cost_support_simp at hmem      -- inverts oneOf / genType / recursive calls
      -- one branch per `oneOf` entry; callee bounds needed as `have`s:
      --   genType_cost           : nType ≤ argTy.size
      --   IsBounded_elements     : the `elements` draw costs 1
      --   a `genZero` cost lemma  : IsBounded (genZero Γ τ) (fun _ => 1)  [still to prove]
      -- App branch, the one creative step: collapse the `getD` in `costInCtx` to `argTy` via
      --   typeCheck_getD_of_typing (genTerm_sound hτ2)   -- e2 : argTy ⇒ (typeCheck Γ e2).getD _ = argTy
      -- then `omega`.
    ```

    If `omega` fails, the bound is too tight — read off the missing term (usually a callee `have`).
-/
theorem genTerm.cost_bounded :
    IsBounded (genTerm (G := SPMF.Cost) Γ τ) (Term.costInCtx Γ) := by
  sorry
