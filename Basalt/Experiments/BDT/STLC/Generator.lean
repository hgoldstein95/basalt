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

/-- BDT generator for STLC terms, where:
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

/-- Generates a Boolean expression -/
def genBoolExpr : Gen Expr := do
  let b ← coin (1/2)
  return .Bool b

/-- Generates a variable from the input list of `vars`.
    Precondition: `vars` must be non-empty.
    (the caller of this generator must ensure this precondition is met) -/
def genVar (vars : List Nat) : Gen Expr := do
  let idx ← choose 0 (vars.length - 1) (by omega)
  return .Var vars[idx]!

/-- BDT STLC generator of well-typed expressions `e` where `Γ ⊢ e : τ`.
  Constructor arities:
  - Arity 0: Bool, Var (weight t0)
  - Arity 1: Abs (weight t1 * α)
  - Arity 2: App (weight t2 * α * α)
-/
def Expr.genExprWithBDT (α t0 t1 t2 d : Rat) (Γ : Ctx) (τ : Ty): Gen Expr := do
  let leafWeight := t0          -- "Leaves" are Bool & Var (0 recursive calls to `Expr`)
  let absWeight := t1 * α       -- Abs has 1 recursive call
  let appWeight := t2 * α * α   -- App has 2 recursive calls

  let totalWeight := leafWeight + absWeight + appWeight

  let leafChoice ← coin (leafWeight / totalWeight)
  if leafChoice then
    -- Generate a leaf
    match τ with
    | .TBool =>
      -- Try to generate a variable if context has one of this type
      let vars := List.filter (fun i => Γ[i]! == τ) (List.range Γ.length)

      -- TODO: is this right? I wonder if we should just have different
      -- weights for `Var` & `Bool` instead of conflating `t0` for
      -- both of them (i.e. perform a weighted choice here instead of `pick`)
      if !vars.isEmpty then
        pick
          (fun () => genVar vars)
          (fun () => genBoolExpr)
      else
        genBoolExpr
    | .TFun τ1 τ2 =>
      -- For function types, see if there is already a variable of type
      -- `τ1 → τ2` in the context. If yes, pick between generating that
      -- variable and generating a new Abs.
      let vars := List.filter (fun i => Γ[i]! == τ) (List.range Γ.length)
      if !vars.isEmpty then
        pick
          (fun () => genVar vars)
          (fun () => genAbs τ1 τ2)
      else
        genAbs τ1 τ2
  else
    -- Choose between Abs and App
    let absChoice ← coin (absWeight / (absWeight + appWeight))

    if absChoice then
      -- We can't generate an abstraction of type `TBool`,
      -- so we just generate a Bool when `τ = Tbool`
      match τ with
      | .TBool => genBoolExpr
      | .TFun τ1 τ2 => genAbs τ1 τ2
    else
      genApp
  partial_fixpoint
where
  -- Generates an `Abs` of type `τ1 → τ2`
  genAbs (τ1 τ2 : Ty) : Gen Expr := do
    let α' := α * d
    let body ← genExprWithBDT α' t0 t1 t2 d (τ1 :: Γ) τ2
    return .Abs τ1 body
  partial_fixpoint

  -- Generates an application
  genApp : Gen Expr := do
    let α' := α * d
    let argTy ← Ty.genTyWithBDT α' t0 t2 d
    let e1 ← genExprWithBDT α' t0 t1 t2 d Γ (.TFun argTy τ)
    let e2 ← genExprWithBDT α' t0 t1 t2 d Γ argTy
    return .App e1 e2
  partial_fixpoint


/-- Generates a well-typed expression `e` such that `Γ ⊢ e : τ`
    using the BDT STLC generator -/
def genSTLCExpr (params : BDTParams) (Γ : Ctx) (τ : Ty) : Gen Expr :=
  let { alpha0 := α, t0, t1, t2, decay := d } := params
  Expr.genExprWithBDT α t0 t1 t2 d Γ τ
