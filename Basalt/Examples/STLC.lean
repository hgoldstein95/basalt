import Basalt
import Basalt.PlausibleGen

open RandomChoice SPMF List

def Bool.arbitrary [Gen G] : G Bool :=
  pick (fun _ => pure true) (fun _ => pure false)

/-- Types are just Bool or function types -/
inductive Ty where
  | Bool : Ty
  | Fun : Ty → Ty → Ty
  deriving DecidableEq

-- Derive `BEq` from `DecidableEq` so the two agree, giving a `LawfulBEq`
-- instance (needed to turn `τ' == τ` guards into propositional equalities).
instance : BEq Ty := instBEqOfDecidableEq
instance : LawfulBEq Ty := by infer_instance

/-- Pretty-prints a `Ty`. Arrows are right-associative, so a function type on the
    left of an arrow gets parenthesized but one on the right does not
    (`(Bool → Bool) → Bool` vs. `Bool → Bool → Bool`). -/
private def Ty.reprPrec (τ : Ty) (prec : Nat) : Std.Format :=
  match τ with
  | .Bool => "Bool"
  | .Fun τ1 τ2 =>
    let body := Ty.reprPrec τ1 1 ++ " → " ++ Ty.reprPrec τ2 0
    if prec ≥ 1 then "(" ++ body ++ ")" else body

instance : Repr Ty where
  reprPrec := Ty.reprPrec

/-- Terms in the STLC extended with Bools.
    (This type is called `Term` instead of `Expr` to avoid conflicting
    with the `Expr` type that is used for Lean metaprogramming.) -/
inductive Term where
  | Bool: Bool → Term
  | Var: Nat → Term
  | App: Term → Term → Term
  | Abs: Ty → Term → Term
  deriving DecidableEq, BEq

/-- Pretty-prints a `Term`. Variables use De Bruijn indices (`#n`).

    Three precedence levels drive the parenthesization:
    * lambdas (`0`) extend as far to the right as possible, so they get
      parenthesized whenever they appear as a function or argument;
    * application (`1`) is left-associative, so the argument (right child) is
      printed at the atomic level while the function (left child) stays at the
      application level;
    * variables and Boolean literals (`2`) are atomic and never parenthesized. -/
private def Term.reprPrec (t : Term) (prec : Nat) : Std.Format :=
  match t with
  | .Bool b => if b then "true" else "false"
  | .Var n => "#" ++ repr n
  | .App e1 e2 =>
    let body := Term.reprPrec e1 1 ++ " " ++ Term.reprPrec e2 2
    if prec ≥ 2 then "(" ++ body ++ ")" else body
  | .Abs τ e =>
    let body := "λ:" ++ repr τ ++ ". " ++ Term.reprPrec e 0
    if prec ≥ 1 then "(" ++ body ++ ")" else body

instance : Repr Term where
  reprPrec := Term.reprPrec

/-- A context is just a list of types (variables represented using De Bruijn variables) -/
abbrev Ctx := List Ty

/-- `lookup Γ n τ` checks whether the `n`th element of the context `Γ` has type `τ` -/
inductive lookup : Ctx -> Nat -> Ty -> Prop where
  | Now : forall τ Γ, lookup (τ :: Γ) .zero τ
  | Later : forall τ τ' n Γ,
      lookup Γ n τ -> lookup (τ' :: Γ) (.succ n) τ

/-- `typing Γ e τ` is the typing judgement `Γ ⊢ e : τ` -/
inductive Typing : Ctx → Term → Ty → Prop where
| TBool : ∀ Γ b,
    Typing Γ (.Bool b) .Bool
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

/-- The number of constructors in a type; used as `genType`'s cost bound. -/
def Ty.size : Ty → Nat
  | .Bool => 1
  | .Fun τ1 τ2 => 1 + τ1.size + τ2.size

/-- Generates an arbitrary type. -/
def genType [Gen G] : G Ty :=
  pick
    (fun _ => pure .Bool)
    (fun _ => do
      let τ1 ← genType
      let τ2 ← genType
      return .Fun τ1 τ2)
partial_fixpoint

/-- `genType` can produce every type. -/
theorem genType_support : τ ∈ SPMF.support (genType (G := SPMF)) := by
  induction τ with
  | Bool => rw [genType]; simp
  | Fun τ1 τ2 ih1 ih2 =>
    rw [genType]
    support_simp [Ty.Fun.injEq]
    exact Or.inr ⟨τ1, ih1, τ2, ih2, rfl, rfl⟩

/-- `genType` terminates with probability 1 -/
theorem genType_terminates : SPMF.IsPMF (genType (G := SPMF)) := by
  refine SPMF.IsPMF_of_critical (F := fun c => 1 / 2 + 1 / 2 * c ^ 2)
    (fun c hle hge => ?_) ?_
  · rw [← ENNReal.toReal_eq_one_iff]
    ennreal_to_real at hge
    ennreal_to_real at hle
    norm_num at hge hle
    nlinarith [sq_nonneg (c.toReal - 1)]
  · conv_rhs => rw [genType]
    simp only [SPMF.mass_pick, SPMF.mass_pure, mul_one]
    gcongr
    rw [sq]
    refine SPMF.mass_bind_ge_mul (le_refl _) (fun τ1 => ?_)
    rw [SPMF.mass_bind_pure]

/-- `genType` makes at most `τ.size` random choices to produce `τ`. -/
theorem genType_cost : IsBounded (genType (G := SPMF.Cost)) (fun τ => τ.size) := by
  open Lean.Order in
  delta genType
  apply fix_induct
    (motive := fun (g : SPMF.Cost Ty) => IsBounded g (fun τ => τ.size)) _ ?admissible ?step
  case admissible => apply admissible_IsBounded
  case step =>
    intro genType_rec ih
    rw [IsBounded_iff]
    rintro ⟨τ, n⟩ hmem
    cost_support_simp at hmem
    obtain ⟨m, rfl, h | h⟩ := hmem
    · obtain ⟨rfl, rfl⟩ := h
      simp [Ty.size]
    · obtain ⟨τ1, n1, n2, hτ1, ⟨τ2, n3, n4, hτ2, ⟨rfl, hn4⟩, hn2⟩, hm⟩ := h
      have h1 : n1 ≤ τ1.size := ih (τ1, n1) hτ1
      have h2 : n3 ≤ τ2.size := ih (τ2, n3) hτ2
      show 1 + m ≤ (Ty.Fun τ1 τ2).size
      simp only [Ty.size]
      omega

-- Note that there is no predicate constraining the random types produced by `genType` here,
-- so we just instantitate the predicate with `⊤`
instance : LawfulGenerator genType ⊤ (fun τ => τ.size) where
  support_iff := by simp [genType_support]
  is_pmf := genType_terminates
  is_bounded := genType_cost

/-- Generates a term that's a Boolean literal -/
def genBool [Gen G] : G Term :=
  Term.Bool <$> Bool.arbitrary

/-- Bools produced by `genBool` are always well-typed -/
theorem genBool_sound :
    b ∈ SPMF.support genBool → Typing Γ b .Bool := by
  intro h
  simp [genBool] at h
  cases h with
  | inl h =>
    obtain ⟨hmem, heq⟩ := h
    subst heq
    constructor
  | inr h =>
    obtain ⟨hmem, heq⟩ := h
    subst heq
    constructor

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

/-- Any term produced by `genZero` is well-typed -/
theorem genZero_sound :
    e ∈ SPMF.support (genZero Γ τ) → Typing Γ e τ := by
  induction τ generalizing Γ e with
  | Bool =>
    intro h
    simp [genZero] at h
    apply genBool_sound at h
    assumption
  | Fun τ1 τ2 IH1 IH2 =>
    intro h
    simp [genZero] at h
    obtain ⟨body, hbody, heq⟩ := h
    subst heq
    constructor
    apply IH2
    assumption

/-- If `τ` is at index `n` in `Γ`, then `lookup Γ n τ` holds.
    This bridges `List.idxOf?` (used by `varsWithType`) to the `lookup` inductive relation. -/
theorem lookup_of_idxOf? {Γ : Ctx} {τ : Ty} {n : Nat} :
    Γ.idxOf? τ = some n → lookup Γ n τ := by
  induction Γ generalizing n with
  | nil => simp [List.idxOf?]
  | cons τ' Γ' IH =>
    simp only [List.idxOf?_cons]
    split
    · rename_i hbeq
      have hτ : τ' = τ := eq_of_beq hbeq
      subst hτ
      rintro ⟨rfl⟩
      constructor
    · rename_i hbeq
      cases hmap : Γ'.idxOf? τ with
      | none => simp
      | some m =>
        simp only [Option.map_some, Option.some.injEq]
        rintro rfl
        apply lookup.Later _ _ _ _
        apply IH hmap

/-- All terms in the list produced by `varsWithType` are sound -/
theorem varsWithType_sound :
    e ∈ varsWithType Γ τ → Typing Γ e τ := by
  intro h
  simp [varsWithType] at h
  obtain ⟨hmem, a, hidx, rfl⟩ := h
  apply Typing.TVar
  apply lookup_of_idxOf?
  assumption


/-- Generates a well-typed term of a particular `depth`,
    at type `τ` in context `Γ`.

    TODO: this recurses on `depth`, but ideally we'd like to
    rewrite this using `partial_fixpoint` instead in order to have a
    `LawfulGenerator` instance for `genTerm`. -/
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
          let argTy ← genType
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
          let argTy ← genType
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

theorem genTerm_sound :
  e ∈ SPMF.support (genTerm Γ depth τ) → Typing Γ e τ := by
  induction depth generalizing Γ e τ with
  | zero =>
    intro h
    simp [genTerm] at h
    rcases h <;> sorry
  | succ depth' IH =>
    sorry

#guard_msgs(drop info) in
#eval (for _ in [0:10] do
  IO.println <| repr (← genTerm [] 3 .Bool) : IO Unit)

#guard_msgs(drop info) in
#eval (for _ in [0:10] do
  IO.println <| repr (← genTerm [] 3 (.Fun .Bool .Bool)) : IO Unit)
