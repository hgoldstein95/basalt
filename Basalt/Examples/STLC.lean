import Basalt

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

/-- STLC terms using De Bruijn indices,
    extended with naturals and addition -/
inductive Term where
  | Const: Nat → Term
  | Add: Term → Term → Term
  | Var: Nat → Term
  | App: Term → Term → Term
  | Abs: Ty → Term → Term
  deriving BEq

/-- Pretty-printer for `Term`s -/
def termToString (e : Term) : String :=
  match e with
  | .Const n => s!"Const {n}"
  | .Add e1 e2 => s!"({termToString e1} + {termToString e2})"
  | .Var id => s!"Id {id}"
  | .App e1 e2 => s!"({termToString e1} {termToString e2})"
  | .Abs τ e2 => s!"(λ _ : {typeToString τ}. {termToString e2})"

/-- Repr instance for `term`s -/
instance : Repr Term where
  reprPrec (e : Term) _ := termToString e

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




end STLCExample
