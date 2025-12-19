import Basalt
import Basalt.Examples.NatList

open RandomChoice

namespace STLCExample

----------------------
-- Type Definitions
----------------------

/-- Base types in the STLC (either Nat or functions) -/
inductive Ty where
  | Nat : Ty
  | Fun: Ty → Ty → Ty
  deriving BEq, DecidableEq

/-- Pretty-printer for `Ty`s -/
def typeToString (ty : Ty) : String :=
  match ty with
  | .Nat => "ℕ"
  | .Fun τ1 τ2 => s!"{typeToString τ1} → {typeToString τ2}"

/-- Repr instance for `type`s -/
instance : Repr Ty where
  reprPrec ty _ := typeToString ty

/-- A typing context `Ctx` is just a list of types -/
abbrev Ctx := List Ty

/-- STLC expressions using De Bruijn indices,
    extended with Nats & addition -/
inductive Expr where
  | Const: Nat → Expr
  | Add: Expr → Expr → Expr
  | Var: Nat → Expr
  | App: Expr → Expr → Expr
  | Abs: Ty → Expr → Expr
  deriving BEq

/-- Pretty-printer for `Expr`s -/
def exprToString (e : Expr) : String :=
  match e with
  | .Const n => s!"Const {n}"
  | .Add e1 e2 => s!"({exprToString e1} + {exprToString e2})"
  | .Var id => s!"Id {id}"
  | .App e1 e2 => s!"({exprToString e1} {exprToString e2})"
  | .Abs τ e2 => s!"(λ _ : {typeToString τ}. {exprToString e2})"

/-- Repr instance for `Expr`s -/
instance : Repr Expr where
  reprPrec (e : Expr) _ := exprToString e

----------------------
-- Generators
----------------------

/-- A naive generator for STLC types -/
def Ty.genTy : Gen Ty :=
  pick
    (fun () => pure .Nat)
    (fun () => do
       let t1 ← genTy
       let t2 ← genTy
       return .Fun t1 t2)
partial_fixpoint

-- We open the `NatList` namesapce just so we can use `Nat.arbitrary` below
open NatListExample

-- TODO:
-- * add sub-generators for Abs, Add, Var
-- * parameterize the generator by Ctx
def Expr.genExpr : Gen Expr :=
  pick
    (fun () => .Const <$> Nat.arbitrary)
    (fun () => do
       let e1 ← Expr.genExpr
       let e2 ← Expr.genExpr
       return .App e1 e2)
partial_fixpoint


end STLCExample
