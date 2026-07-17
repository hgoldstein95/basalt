import Basalt
import Basalt.PlausibleGen

open RandomChoice SPMF List

def Bool.arbitrary [Gen G] : G Bool :=
  pick (fun _ => pure true) (fun _ => pure false)

inductive Ty where
  | Bool : Ty
  | Fun : Ty → Ty → Ty
  deriving DecidableEq, Repr, BEq

/-- Terms in the STLC extended with Bools.
    (This type is called `Term` instead of `Expr` to avoid conflicting
    with the `Expr` type that is used for Lean metaprogramming.) -/
inductive Term where
  | Bool: Bool → Term
  | Var: Nat → Term
  | App: Term → Term → Term
  | Abs: Ty → Term → Term
  deriving DecidableEq, BEq, Repr

/-- A context is just a list of types (variables represented using De Bruijn variables) -/
abbrev Ctx := List Ty

/-- `lookup Γ n τ` checks whether the `n`th element of the context `Γ` has type `τ` -/
inductive lookup : Ctx -> Nat -> Ty -> Prop where
  | Now : forall τ Γ, lookup (τ :: Γ) .zero τ
  | Later : forall τ τ' n Γ,
      lookup Γ n τ -> lookup (τ' :: Γ) (.succ n) τ

/-- `typing Γ e τ` is the typing judgement `Γ ⊢ e : τ` -/
inductive Typing: Ctx → Term → Ty → Prop where
| TBool : ∀ Γ n,
    Typing Γ (.Bool n) .Bool
| TAbs: ∀ Γ e τ1 τ2,
    Typing (τ1::Γ) e τ2 →
    Typing Γ (.Abs τ1 e) (.Fun τ1 τ2)
| TVar: ∀ Γ x τ,
    lookup Γ x τ →
    Typing Γ (.Var x) τ
| TApp: ∀ Γ e1 e2 τ1 τ2,
    Typing Γ e2 τ1 →
    Typing Γ e1 (.Fun τ1 τ2) →
    Typing Γ (.App e1 e2) τ2

/-- Generates a random term of some `depth` -/
def genType [Gen G] (depth : Nat) : G Ty :=
  match depth with
  | 0 => pure .Bool
  | depth + 1 =>
    pick
      (fun _ => pure .Bool)
      (fun _ => do
        let τ1 ← genType depth
        let τ2 ← genType depth
        return .Fun τ1 τ2)

/-- Generates a term that's a Boolean literal -/
def genBool [Gen G] : G Term :=
  Term.Bool <$> Bool.arbitrary

/-- Finds all variables in `Γ` that have type `τ` -/
def varsWithType (Γ : Ctx) (τ : Ty) : List Term :=
  Γ.filterMap (fun τ' => if τ' == τ then Term.Var <$> Γ.idxOf? τ' else none)

/-- Generates a term with size 0 -/
def genZero [Gen G] (Γ : Ctx) (τ : Ty) : G Term :=
  match τ with
  | .Bool => genBool
  | .Fun τ1 τ2 => do
    let e ← genZero (τ1 :: Γ) τ2
    return .Abs τ1 e

/-- Generates a well-typed term of a particular `depth`,
    at type `τ` in context `Γ` -/
def genTerm [Gen G] (Γ : Ctx) (depth : Nat) (τ : Ty) : G Term :=
  match depth with
  | 0 =>
    let vars := varsWithType Γ τ
    if hne : vars ≠ [] then
      oneOf [
        fun _ => elements vars hne,
        fun _ => genZero Γ τ
      ] (by apply cons_ne_nil)
    else
      genZero Γ τ
  | depth' + 1 =>
    let vars := varsWithType Γ τ
    if hne : vars ≠ [] then
      oneOf [
        fun _ => elements vars hne,
        fun _ => do
          let argTy ← genType depth'
          let e1 ← genTerm Γ depth' (.Fun argTy τ)
          let e2 ← genTerm Γ depth' argTy
          return .App e1 e2,
        fun _ =>
          match τ with
          | .Bool => genBool
          | .Fun τ1 τ2 => do
            let e ← genTerm (τ1 :: Γ) depth' τ2
            return .Abs τ1 e
      ] (by apply cons_ne_nil)
    else
      oneOf [
        fun _ => do
          let argTy ← genType depth'
          let e1 ← genTerm Γ depth' (.Fun argTy τ)
          let e2 ← genTerm Γ depth' argTy
          return .App e1 e2,
        fun _ =>
          match τ with
          | .Bool => genBool
          | .Fun τ1 τ2 => do
            let e ← genTerm (τ1 :: Γ) depth' τ2
            return .Abs τ1 e
      ] (by apply cons_ne_nil)

#guard_msgs(drop info) in
#eval (for _ in [0:10] do
  IO.println <| repr (← genTerm [] 3 .Bool) : IO Unit)

#guard_msgs(drop info) in
#eval (for _ in [0:10] do
  IO.println <| repr (← genTerm [] 3 (.Fun .Bool .Bool)) : IO Unit)
