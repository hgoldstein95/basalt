import Basalt
import Basalt.Examples.STLCMutants.STLC

open STLC

/-- Generator for STLC types -/
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
  def Expr.genOne (Γ : Ctx) (τ : Ty) : Gen Expr :=
    match τ with
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
            -- Generate a random variable in the context
            let vars := List.filter (fun i => Γ[i]! == τ) (List.range Γ.length)
            let default ← .Const <$> Nat.arbitrary
            RandomChoice.elements (.Var <$> vars) default)
          (fun () => do
            let t1 ← Ty.genTy
            let e1 ← Expr.genExpr Γ (.Fun t1 τ)
            let e2 ← Expr.genExpr Γ t1
            return .App e1 e2))
  partial_fixpoint


end
