import Basalt

open RandomChoice

namespace STLCExample

/-- Base types in the STLC (either Nat or functions) -/
inductive type where
  | Nat : type
  | Fun: type → type → type
  deriving BEq, DecidableEq

/-- Pretty-printer for `type`s -/
def typeToString (ty : type) : String :=
  match ty with
  | .Nat => "ℕ"
  | .Fun τ1 τ2 => s!"{typeToString τ1} → {typeToString τ2}"

/-- Repr instance for `type`s -/
instance : Repr type where
  reprPrec ty _ := typeToString ty

/-- STLC terms using De Bruijn indices,
    extended with naturals and addition -/
inductive term where
  | Const: Nat → term
  | Add: term → term → term
  | Var: Nat → term
  | App: term → term → term
  | Abs: type → term → term
  deriving BEq

/-- Pretty-printer for `term`s -/
def termToString (e : term) : String :=
  match e with
  | .Const n => s!"Const {n}"
  | .Add e1 e2 => s!"({termToString e1} + {termToString e2})"
  | .Var id => s!"Id {id}"
  | .App e1 e2 => s!"({termToString e1} {termToString e2})"
  | .Abs τ e2 => s!"(λ _ : {typeToString τ}. {termToString e2})"

/-- Repr instance for `term`s -/
instance : Repr term where
  reprPrec (e : term) _ := termToString e

end STLCExample
