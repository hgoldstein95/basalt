import Basalt
import Basalt.Examples.STLCMutants.STLC

namespace STLCExperiments

open STLC

/-- Helper for typechecking an `Option Expr` against a `Ty` -/
def mTypeCheck (e : Option Expr) (ty : Ty) : Bool :=
  match e with
  | some e' => typeCheck [] e' ty
  | none => true

/-- Stepping a well-typed expr should preserve its type -/
def prop_single_preserve (e : Expr) (pstep : Expr → Option Expr) : Gen Bool :=
  match getTy [] e with
  | some ty => return mTypeCheck (pstep e) ty
  | none => return true

/-- Multi-stepping an expr should preserve its type -/
def prop_multi_preserve
  (e : Expr)
  (multistep : Nat → (Expr → Option Expr) → Expr → Option Expr)
  (pstep : Expr → Option Expr) : Gen Bool :=
  match getTy [] e with
  | some ty => return mTypeCheck (multistep 40 pstep e) ty
  | none => return true

end STLCExperiments
