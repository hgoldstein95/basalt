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
  deriving BEq, Inhabited

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
  deriving BEq, Inhabited

/-- Pretty-printer for `Expr`s -/
def exprToString (e : Expr) : String :=
  match e with
  | .Const n => s!"Const {n}"
  | .Add e1 e2 => s!"({exprToString e1} + {exprToString e2})"
  | .Var id => s!"Var {id}"
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


mutual

  /-- Helper: generates structurally simple expressions based on type.
      NB: we have to define this generator explicitly using `do`-notation,
      since `monotone_bind` is defined in terms of `>>=`
      (i.e. we can't use `<$>` to make this generator more succinct). -/
  def Expr.genOne (Γ : Ctx) (ty : Ty) : Gen Expr :=
    match ty with
    | Ty.Nat =>
      pick
        (fun () => do
          let n ← Nat.arbitrary
          pure (.Const n))
        (fun () => do
          let e1 ← Expr.genExpr Γ .Nat
          let e2 ← Expr.genExpr Γ .Nat
          return .Add e1 e2)
    | .Fun t1 t2 => do
        let body ← Expr.genOne (t1 :: Γ) t2
        pure (.Abs t1 body)
    partial_fixpoint

  /-- `genExpr Γ τ` generates random `Expr`s `e` such that `Γ ⊢ e : τ` -/
  def Expr.genExpr (Γ : Ctx) (τ : Ty) : Gen Expr :=
    pick
      (fun () => genOne Γ τ)
      (fun () => pick
          (fun () => do
            let vars := List.filter (fun i => Γ[i]! == τ) (List.range Γ.length)
            RandomChoice.elements (.Var <$> vars))
          (fun () => do
            let t1 ← Ty.genTy
            let e1 ← Expr.genExpr Γ (.Fun t1 τ)
            let e2 ← Expr.genExpr Γ t1
            return .App e1 e2))
  partial_fixpoint
end

end STLCExample
