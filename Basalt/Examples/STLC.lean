import Basalt
import Basalt.PlausibleGen
import Basalt.Examples.ArbNat

open RandomChoice ArbNat SPMF List

inductive Ty where
  | Nat : Ty
  | Fun : Ty → Ty → Ty
  deriving DecidableEq, Repr, BEq

/-- Terms in the STLC extended with naturals and addition -/
inductive Term where
  | Const: Nat → Term
  | Add: Term → Term → Term
  | Var: Nat → Term
  | App: Term → Term → Term
  | Abs: Ty → Term → Term
  deriving DecidableEq, BEq, Repr

abbrev Ctx := List Ty

/-- `lookup Γ n τ` checks whether the `n`th element of the context `Γ` has type `τ` -/
inductive lookup : Ctx-> Nat -> Ty -> Prop where
  | Now : forall τ Γ, lookup (τ :: Γ) .zero τ
  | Later : forall τ τ' n Γ,
      lookup Γ n τ -> lookup (τ' :: Γ) (.succ n) τ

/-- `typing Γ e τ` is the typing judgement `Γ ⊢ e : τ` -/
inductive Typing: Ctx → Term → Ty → Prop where
| TConst : ∀ Γ n,
    Typing Γ (.Const n) .Nat
| TAdd: ∀ Γ e1 e2,
    Typing Γ e1 .Nat →
    Typing Γ e2 .Nat →
    Typing Γ (.Add e1 e2) .Nat
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


-- TODO: maybe change this to `G (Option Term)` instead
def genVar [Gen G] (Γ : Ctx) (τ : Ty) (hmem : τ ∈ Γ) : G Term :=
  let vars := Γ.filterMap (fun τ' => if τ' == τ then Term.Var <$> Γ.idxOf? τ' else none)
  elements vars (by
    -- Since `τ ∈ Γ`, `idxOf? τ Γ` is `some i`, so `Var i ∈ vars`, hence `vars ≠ []`.
    have hsome : (Γ.idxOf? τ).isSome := by rw [List.isSome_idxOf?]; exact hmem
    apply ne_nil_of_mem (a := Term.Var ((Γ.idxOf? τ).get hsome))
    rw [List.mem_filterMap]
    refine ⟨τ, hmem, ?_⟩
    simp only [beq_self_eq_true, if_true, Functor.map]
    rw [Option.map_eq_some_iff]
    exact ⟨_, (Option.some_get hsome).symm, rfl⟩)

/-- Generates a random term of some `depth` -/
def genType [Gen G] (depth : Nat) : G Ty :=
  match depth with
  | 0 => pure .Nat
  | depth + 1 =>
    pick
      (fun _ => pure .Nat)
      (fun _ => do
        let τ1 ← genType depth
        let τ2 ← genType depth
        return .Fun τ1 τ2)
