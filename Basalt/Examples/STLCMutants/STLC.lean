import Basalt

/-- Types in the simply-typed lambda calculus -/
inductive Ty where
  | TBool : Ty
  | TFun : Ty → Ty → Ty
  deriving BEq, Inhabited, Repr

namespace Ty

def toString : Ty → String
  | .TBool => "Bool"
  | .TFun t1 t2 => s!"({toString t1} → {toString t2})"

instance : ToString Ty where
  toString := toString

end Ty

/-- Expressions in the simply-typed lambda calculus -/
inductive Expr where
  | Var : Nat → Expr
  | Bool : Bool → Expr
  | Abs : Ty → Expr → Expr
  | App : Expr → Expr → Expr
  deriving BEq, Inhabited, Repr

namespace Expr

def toString : Expr → String
  | Var n => s!"(Var {n})"
  | Bool b => s!"(Bool {b})"
  | Abs t e => s!"(Abs {t} {toString e})"
  | App e1 e2 => s!"(App {toString e1} {toString e2})"

instance : ToString Expr where
  toString := toString

end Expr

/-- Typing context (list of types) -/
abbrev Ctx := List Ty

namespace STLC

/-- Check if an expression is in normal form -/
def isNF : Expr → Bool
  | Expr.Var _ => true
  | Expr.Bool _ => true
  | Expr.Abs _ e => isNF e
  | Expr.App (Expr.Abs _ _) _ => false
  | Expr.App e1 e2 => isNF e1 && isNF e2

/-- Get the type of an expression in a given context -/
def getTy (ctx : Ctx) (e : Expr) : Option Ty :=
  match e with
  | .Var n =>
    if n < ctx.length then
      some ctx[n]!
    else none
  | .Bool _ => some Ty.TBool
  | .Abs t e => do
    let t' ← getTy (t :: ctx) e
    return (Ty.TFun t t')
  | .App e1 e2 => do
    match (← getTy ctx e1) with
    | .TFun t11 t12 => do
      let t2 ← getTy ctx e2
      if t11 == t2 then return t12 else none
    | _ => none


/-- Type check an expression against a given type -/
def typeCheck (ctx : Ctx) (e : Expr) (t : Ty) : Bool :=
  match getTy ctx e with
  | some t' => t == t'
  | none => false

end STLC
