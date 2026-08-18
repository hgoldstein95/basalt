/-
Copyright (c) 2026 Harrison Goldstein & Ernest Ng. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein & Ernest Ng
-/
import Basalt

open List

/-!
# STLC Syntax and Typing

Syntax, contexts, and the typing judgement for the simply-typed lambda calculus extended with
Bools, along with lemmas relating the `lookup` judgement to `List` indexing.
-/

/-- Types are just Bool or function types -/
inductive Ty where
  | Bool : Ty
  | Fun : Ty → Ty → Ty
  deriving DecidableEq

-- Derive `BEq` from `DecidableEq` so the two agree, giving a `LawfulBEq`
-- instance (needed to turn `τ' == τ` guards into propositional equalities).
instance : BEq Ty := instBEqOfDecidableEq
instance : LawfulBEq Ty := by infer_instance

/-- Pretty-prints a `Ty`. Arrows are right-associative, so a function type on the
    left of an arrow gets parenthesized but one on the right does not
    (`(Bool → Bool) → Bool` vs. `Bool → Bool → Bool`). -/
private def Ty.reprPrec (τ : Ty) (prec : Nat) : Std.Format :=
  match τ with
  | .Bool => "Bool"
  | .Fun τ1 τ2 =>
    let body := Ty.reprPrec τ1 1 ++ " → " ++ Ty.reprPrec τ2 0
    if prec ≥ 1 then "(" ++ body ++ ")" else body

instance : Repr Ty where
  reprPrec := Ty.reprPrec

/-- Terms in the STLC extended with Bools.
    (This type is called `Term` instead of `Expr` to avoid conflicting
    with the `Expr` type that is used for Lean metaprogramming.) -/
inductive Term where
  | Bool: Bool → Term
  | Var: Nat → Term
  | App: Term → Term → Term
  | Abs: Ty → Term → Term
  deriving DecidableEq, BEq, Inhabited

/-- Pretty-prints a `Term`. Variables use De Bruijn indices (`#n`).

    Three precedence levels drive the parenthesization:
    * lambdas (`0`) extend as far to the right as possible, so they get
      parenthesized whenever they appear as a function or argument;
    * application (`1`) is left-associative, so the argument (right child) is
      printed at the atomic level while the function (left child) stays at the
      application level;
    * variables and Boolean literals (`2`) are atomic and never parenthesized. -/
private def Term.reprPrec (t : Term) (prec : Nat) : Std.Format :=
  match t with
  | .Bool b => if b then "true" else "false"
  | .Var n => "#" ++ repr n
  | .App e1 e2 =>
    let body := Term.reprPrec e1 1 ++ " " ++ Term.reprPrec e2 2
    if prec ≥ 2 then "(" ++ body ++ ")" else body
  | .Abs τ e =>
    let body := "λ:" ++ repr τ ++ ". " ++ Term.reprPrec e 0
    if prec ≥ 1 then "(" ++ body ++ ")" else body

instance : Repr Term where
  reprPrec := Term.reprPrec

/-- A context is just a list of types (variables represented using De Bruijn variables) -/
abbrev Ctx := List Ty

/-- `lookup Γ n τ` checks whether the `n`th element of the context `Γ` has type `τ` -/
inductive lookup : Ctx -> Nat -> Ty -> Prop where
  | Now : forall τ Γ, lookup (τ :: Γ) .zero τ
  | Later : forall τ τ' n Γ,
      lookup Γ n τ -> lookup (τ' :: Γ) (.succ n) τ

/-- `typing Γ e τ` is the typing judgement `Γ ⊢ e : τ` -/
inductive Typing : Ctx → Term → Ty → Prop where
| TBool : ∀ Γ b,
    Typing Γ (.Bool b) .Bool
| TAbs: ∀ Γ e τ1 τ2,
    Typing (τ1::Γ) e τ2 →
    Typing Γ (.Abs τ1 e) (.Fun τ1 τ2)
| TVar: ∀ Γ x τ,
    lookup Γ x τ →
    Typing Γ (.Var x) τ
| TApp: ∀ Γ e1 e2 τ1 τ2,
    Typing Γ e2 τ1 →
    Typing Γ e1 (.Fun τ1 τ2) →
    Typing Γ (.App e1 e2) τ2

/-- The number of constructors in a type; used as `genType`'s cost bound. -/
def Ty.size : Ty → Nat
  | .Bool => 1
  | .Fun τ1 τ2 => 1 + τ1.size + τ2.size

/-- If `Γ[i]` returns `τ`, then the judgment `lookup Γ i τ` holds -/
theorem getElem?_lookup :
    Γ[i]? = some τ → lookup Γ i τ := by
  intro h
  induction Γ generalizing i τ with
  | nil => contradiction
  | cons τ' Γ' IH =>
    cases i with
    | zero =>
      simp at h
      subst h
      constructor
    | succ i' =>
      apply lookup.Later
      apply IH
      simp at h
      assumption

/-- Converse of `getElem?_lookup`: `lookup Γ i τ` implies `Γ[i]? = some τ`. -/
theorem lookup_getElem? :
    lookup Γ i τ → Γ[i]? = some τ := by
  intro h
  induction h with
  | Now τ Γ => simp
  | Later τ τ' n Γ hl IH => simpa using IH
