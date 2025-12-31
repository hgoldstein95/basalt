import Basalt.Examples.STLCMutants.STLC

namespace STLCMutants

open Expr Typ

/-- Shift free variables in an expression by `d`, starting from cutoff `c` -/
def shift (d : Int) : Expr → Expr :=
  let rec go (c : Nat) : Expr → Expr
    | Var n =>
      if n < c then
        Var n
      else
        Var (n + d.toNat)
    | Expr.Bool b => Expr.Bool b
    | Abs t e => Abs t (go (c + 1) e)
    | App e1 e2 => App (go c e1) (go c e2)
  go 0

/-- Substitute expression `s` for variable `n` in expression `e`: `[n -> s]e` -/
def subst (n : Nat) (s : Expr) : Expr → Expr
  | Var m =>
    if m == n then s else Var m
  | Expr.Bool b => Expr.Bool b
  | Abs t e => Abs t (subst (n + 1) (shift 1 s) e)
  | App e1 e2 => App (subst n s e1) (subst n s e2)

/-- Top-level substitution: [0 -> s]e with proper shifting -/
def substTop (s : Expr) (e : Expr) : Expr :=
  shift (-1) (subst 0 (shift 1 s) e)

/-- Parallel reduction step (reduces all redexes in parallel) -/
def pstep : Expr → Option Expr
  | Abs t e => Abs t <$> pstep e
  | App (Abs _ e1) e2 =>
    let e1' := (pstep e1).getD e1
    let e2' := (pstep e2).getD e2
    some (substTop e2' e1')
  | App e1 e2 =>
    match pstep e1, pstep e2 with
    | none, none => none
    | me1, me2 =>
      let e1' := me1.getD e1
      let e2' := me2.getD e2
      some (App e1' e2')
  | _ => none

/-- Multi-step reduction with fuel -/
def multistep (fuel : Nat) (step : Expr → Option Expr) (e : Expr) : Option Expr :=
  match fuel with
  | 0 => none
  | fuel' + 1 =>
    match step e with
    | none => some e
    | some e' => multistep fuel' step e'

end STLCMutants
