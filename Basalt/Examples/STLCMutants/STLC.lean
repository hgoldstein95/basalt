import Basalt

/-- Types in the simply-typed lambda calculus -/
inductive Typ where
  | TBool : Typ
  | TFun : Typ → Typ → Typ
  deriving BEq, Inhabited, Repr

namespace Typ

def toString : Typ → String
  | TBool => "Bool"
  | TFun t1 t2 => s!"({toString t1} → {toString t2})"

instance : ToString Typ where
  toString := toString

end Typ

/-- Expressions in the simply-typed lambda calculus -/
inductive Expr where
  | Var : Nat → Expr
  | Bool : Bool → Expr
  | Abs : Typ → Expr → Expr
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
abbrev Ctx := List Typ

namespace STLC

/-- Check if an expression is in normal form -/
def isNF : Expr → Bool
  | Expr.Var _ => true
  | Expr.Bool _ => true
  | Expr.Abs _ e => isNF e
  | Expr.App (Expr.Abs _ _) _ => false
  | Expr.App e1 e2 => isNF e1 && isNF e2

/-- Get the type of an expression in a given context -/
def getTyp : Ctx → Expr → Option Typ
  | ctx, Expr.Var n =>
    if n < ctx.length then
      some ctx[n]!
    else
      none
  | _, Expr.Bool _ => some Typ.TBool
  | ctx, Expr.Abs t e =>
    match getTyp (t :: ctx) e with
    | some t' => some (Typ.TFun t t')
    | none => none
  | ctx, Expr.App e1 e2 =>
    match getTyp ctx e1, getTyp ctx e2 with
    | some (Typ.TFun t11 t12), some t2 =>
      if t11 == t2 then some t12 else none
    | _, _ => none

/-- Type check an expression against a given type -/
def typeCheck (ctx : Ctx) (e : Expr) (t : Typ) : Bool :=
  match getTyp ctx e with
  | some t' => t == t'
  | none => false

end STLC
