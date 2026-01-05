import Basalt
import Basalt.Examples.STLCMutants.STLC
import Basalt.Examples.NatList
import Basalt.Experiments.BDT.Hyperparameters

open STLC RandomChoice
open NatListExample

namespace NaiveSTLCGenerator

/-- Naive generator for STLC types (50-50 between TBool and TFun) -/
def Ty.genTy : Gen Ty :=
  pick
    (fun () => pure .TBool)
    (fun () => do
       let t1 ← genTy
       let t2 ← genTy
       return .TFun t1 t2)
partial_fixpoint

mutual

  /-- Helper: generates structurally simple expressions based on type.
      NB: we have to define this generator explicitly using `do`-notation,
      since `monotone_bind` is defined in terms of `>>=`
      (i.e. we can't use `<$>` to make this generator more succinct). -/
  def Expr.genOne (Γ : Ctx) (τ : Ty) : Gen Expr :=
    match τ with
    | .TBool => do
      let b ← coin (1/2)
      pure (.Bool b)
    | .TFun t1 t2 => do
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
            if vars.isEmpty then
              genOne Γ τ
            else do
              let idx ← choose 0 (vars.length - 1) (by omega)
              return .Var vars[idx]!)
          (fun () => do
            let t1 ← Ty.genTy
            let e1 ← Expr.genExpr Γ (.TFun t1 τ)
            let e2 ← Expr.genExpr Γ t1
            return .App e1 e2))
  partial_fixpoint

end

end NaiveSTLCGenerator

/-- BDT-parameterized generator for STLC types

  Parameters:
  - α: current energy level
  - t0: weight for arity-0 constructors (TBool)
  - t2: weight for arity-2 constructors (TFun)
  - d: decay factor
-/
def Ty.genTyWithBDT (α t0 t2 d : Rat) : Gen Ty := do
  let boolWeight := t0
  let funWeight := t2 * α * α
  let bias := boolWeight / (boolWeight + funWeight)
  if (← coin bias) then
    return .TBool
  else
    let α' := α * d
    let t1 ← genTyWithBDT α' t0 t2 d
    let t2 ← genTyWithBDT α' t0 t2 d
    return .TFun t1 t2
  partial_fixpoint

/-- Thunked generator which produces a Boolean expression -/
def genBool : Unit → Gen Expr := fun _ => do
  let b ← coin (1/2)
  return .Bool b


mutual

  /-- BDT-parameterized helper: generates structurally simple expressions

  Parameters:
  - α: current energy level
  - t0: weight for arity-0 constructors (Bool, Var)
  - t1: weight for arity-1 constructors (Abs)
  - t2: weight for arity-2 constructors (App)
  - d: decay factor
  - Γ: typing context
  - τ: target type
  -/
  def Expr.genOneWithBDT (α t0 t1 t2 d : Rat) (Γ : Ctx) (τ : Ty) : Gen Expr := do
    match τ with
    | .TBool => genBool ()
    | .TFun ty1 ty2 =>
      let α' := α * d
      let body ← genOneWithBDT α' t0 t1 t2 d (ty1 :: Γ) ty2
      return .Abs ty1 body

  /-- BDT-parameterized expression generator

  Generates well-typed expressions `e` such that `Γ ⊢ e : τ`

  Constructor arities:
  - Arity 0: Bool, Var (weight t0)
  - Arity 1: Abs (weight t1 * α)
  - Arity 2: App (weight t2 * α * α)
  -/
  def Expr.genExprWithBDT (α t0 t1 t2 d : Rat) (Γ : Ctx) (τ : Ty): Gen Expr := do
    let leafWeight := t0            -- a Leaf is either a Bool or a Var
    let absWeight := t1 * α         -- Abs
    let appWeight := t2 * α * α     -- App

    let totalWeight := leafWeight + absWeight + appWeight

    let preferLeaf ← coin (leafWeight / totalWeight)
    if preferLeaf then
      -- Generate a leaf
      match τ with
      | .TBool =>
        -- Try to generate a variable if context has one of this type
        let vars := List.filter (fun i => Γ[i]! == τ) (List.range Γ.length)
        if !vars.isEmpty then
          pick
            (fun () => do
              let idx ← choose 0 (vars.length - 1) (by omega)
              return .Var vars[idx]!)
            (fun () => genBool ())
        else genBool ()
      | .TFun τ1 τ2 =>
        -- For function types, see if there is already a variable of type
        -- `τ1 → τ2` in the context. If yes, pick between generating that
        -- variable and generating a new Abs.
        let vars := List.filter (fun i => Γ[i]! == τ) (List.range Γ.length)
        if !vars.isEmpty then
          pick
            (fun () => do
              let idx ← choose 0 (vars.length - 1) (by omega)
              return .Var vars[idx]!)
            (fun () => do
              let α' := α * d
              let body ← genExprWithBDT α' t0 t1 t2 d (τ1 :: Γ) τ2
              return .Abs τ1 body)
        else
          -- Generate Abs
          let α' := α * d
          let body ← genExprWithBDT α' t0 t1 t2 d (τ1 :: Γ) τ2
          return .Abs τ1 body
    else
      -- Choose between Abs and App
      let preferAbsOverApp ← coin (absWeight / (absWeight + appWeight))

      if preferAbsOverApp then
        -- Generate Abs (only valid for function types)
        match τ with
        | .TBool =>
          -- Can't generate an abstraction when the expected type is Bool,
          -- so we just generate a Bool in this case
          genBool ()
        | .TFun ty1 ty2 =>
          let α' := α * d
          let body ← genExprWithBDT α' t0 t1 t2 d (ty1 :: Γ) ty2
          return .Abs ty1 body
      else
        -- Generate App
        let α' := α * d
        let argTy ← Ty.genTyWithBDT α' t0 t2 d
        let e1 ← genExprWithBDT α' t0 t1 t2 d Γ (.TFun argTy τ)
        let e2 ← genExprWithBDT α' t0 t1 t2 d Γ argTy
        return .App e1 e2
    partial_fixpoint

end

/-- Generate a well-typed STLC expression using BDT parameters

  Generates expressions in an empty context with TBool type by default.
-/
def genSTLCExpr (params : BDTParams) (τ : Ty := .TBool) : Gen Expr :=
  let { alpha0 := α, t0, t1, t2, decay := d } := params
  Expr.genExprWithBDT α t0 t1 t2 d [] τ

/-- Generate a well-typed STLC expression with a specific context -/
def genSTLCExprWithCtx (params : BDTParams) (Γ : Ctx) (τ : Ty) : Gen Expr :=
  let { alpha0 := α, t0, t1, t2, decay := d } := params
  Expr.genExprWithBDT α t0 t1 t2 d Γ τ
