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

/-- Generates a term that's a Boolean literal -/
def genBool [Gen G] : G Term :=
  Term.Bool <$> Bool.arbitrary

/-- Any term generated by `genBool` is of the form `.Bool b` for some `b` -/
theorem genBool_inversion :
    e ∈ SPMF.support genBool → ∃ b, e = .Bool b := by
  intro h
  simp [genBool] at h
  rcases h with h | h
  . obtain ⟨_, heq⟩ := h
    subst heq
    exists false
  . obtain ⟨_, heq⟩ := h
    subst heq
    exists true

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
  Γ.zipIdx.filterMap (fun (τ', i) => if τ' == τ then some (Term.Var i) else none)

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

/-- `genZero` produces either a well-typed `Bool` or an `Abs` -/
theorem genZero_inversion :
    e ∈ SPMF.support (genZero Γ τ) → (∃ b, e = .Bool b ∧ Typing Γ e .Bool) ∨ (∃ e' τ1 τ2, e = .Abs τ1 e' ∧ Typing Γ e (.Fun τ1 τ2)) := by
  intro h
  unfold genZero at h
  cases τ with
  | Bool =>
    dsimp at h
    have htyping : Typing Γ e .Bool := by
      apply genBool_sound
      assumption
    left
    have hb : ∃ b, e = .Bool b := by
      apply genBool_inversion
      assumption
    obtain ⟨b', heq⟩ := hb
    exists b'
  | Fun τ1 τ2 =>
    simp at h
    obtain ⟨e', ⟨hmem, heq⟩⟩ := h
    right
    exists e', τ1, τ2
    constructor
    . assumption
    . subst heq
      constructor
      apply genZero_sound at hmem
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

/-- If `Γ[i]` returns `τ`, then the judgment `lookup Γ i τ` holds -/
theorem getElem?_lookup :
    Γ[i]? = some τ → lookup Γ i τ := by
  intro h
  induction Γ generalizing i τ with
  | nil => contradiction
  | cons τ' Γ' IH =>
    cases i with
    | zero =>
      simp at h
      subst h
      constructor
    | succ i' =>
      apply lookup.Later
      apply IH
      simp at h
      assumption

/-- All terms in the list produced by `varsWithType` are sound -/
theorem varsWithType_sound :
    e ∈ varsWithType Γ τ → Typing Γ e τ := by
  intro h
  simp [varsWithType] at h
  obtain ⟨i, hmem, rfl⟩ := h
  apply Typing.TVar
  rw [mk_mem_zipIdx_iff_getElem?] at hmem
  apply getElem?_lookup
  assumption


/-- Generates a well-typed term at type `τ` in context `Γ`. -/
def genTerm [Gen G] (Γ : Ctx) (τ : Ty) : G Term :=
  let vars := varsWithType Γ τ
  if hne : vars ≠ [] then
    oneOf [
      fun _ => genZero Γ τ,
      fun _ => elements vars hne,
      fun _ => do
        let argTy ← genType
        let e1 ← genTerm Γ (.Fun argTy τ)
        let e2 ← genTerm Γ argTy
        return .App e1 e2,
      fun _ =>
        match τ with
        | .Bool => genBool
        | .Fun τ1 τ2 => do
          let e ← genTerm (τ1 :: Γ) τ2
          return .Abs τ1 e
    ] (by apply cons_ne_nil)
  else
    oneOf [
      fun _ => genZero Γ τ,
      fun _ => do
        let argTy ← genType
        let e1 ← genTerm Γ (.Fun argTy τ)
        let e2 ← genTerm Γ argTy
        return .App e1 e2,
      fun _ =>
        match τ with
        | .Bool => genBool
        | .Fun τ1 τ2 => do
          let e ← genTerm (τ1 :: Γ) τ2
          return .Abs τ1 e
    ] (by apply cons_ne_nil)
partial_fixpoint

theorem genTerm_complete :
    Typing Γ e τ → e ∈ SPMF.support (genTerm Γ τ) := by
  intro h
  induction h with
  | TBool => sorry
  | TVar => sorry
  | TAbs => sorry
  | TApp => sorry

theorem genTerm_sound :
    e ∈ SPMF.support (genTerm Γ τ) → Typing Γ e τ := by
  induction e generalizing Γ τ with
  | Bool b =>
    intro h
    unfold genTerm at h
    cases τ with
    | Bool => exact Typing.TBool Γ b
    | Fun τ1 τ2 =>
      -- `Bool b` cannot be produced at a function type, contradiction
      exfalso
      support_simp [genZero] at h
      simp [varsWithType] at h
  | Var n =>
    intro h
    unfold genTerm at h
    -- A `Var` can only come from the `varsWithType` branch; the `genZero`,
    -- `App`, and `genBool`/`Abs` branches are all constructor clashes.
    cases τ with
    | Bool =>
      support_simp [genZero, genBool] at h
      simp at h
      obtain ⟨_, hv⟩ := h
      apply varsWithType_sound; assumption
    | Fun τ1 τ2 =>
      support_simp [genZero] at h
      simp at h
      obtain ⟨_, hv⟩ := h
      apply varsWithType_sound; assumption
  | Abs τ' e1 IH =>
    intro h
    unfold genTerm at h
    cases τ with
    | Bool =>
      -- Can't have an `Abs` at type `Bool`, a contradiction
      support_simp [genZero, genBool] at h
      simp at h
      obtain ⟨_, hv⟩ := h
      cases varsWithType_sound hv
    | Fun τ1 τ2 =>
      -- An `Abs τ' e1` with type `Fun τ1 τ2` comes from either `genZero` or the
      -- recursive `Abs` branch
      support_simp [genZero] at h
      simp [varsWithType] at h
      rcases h with ⟨_, hz | hg⟩ | ⟨_, hz | hg⟩
      · obtain ⟨a, ha, rfl, rfl⟩ := hz
        apply Typing.TAbs; apply genZero_sound; assumption
      · obtain ⟨a, ha, rfl, rfl⟩ := hg
        apply Typing.TAbs; apply IH; assumption
      · obtain ⟨a, ha, rfl, rfl⟩ := hz
        apply Typing.TAbs; apply genZero_sound; assumption
      · obtain ⟨a, ha, rfl, rfl⟩ := hg
        apply Typing.TAbs; apply IH; assumption
  | App e1 e2 IH1 IH2 =>
    intro h
    unfold genTerm at h
    -- An `App` only comes from the application branch
    cases τ with
    | Bool =>
      support_simp [genZero, genBool] at h
      simp [varsWithType] at h
      rcases h with ⟨_, hf⟩ | ⟨_, hf⟩
      all_goals
        obtain ⟨argTy, _, hf, hx⟩ := hf
        apply Typing.TApp
        · apply IH2; assumption
        · apply IH1; assumption
    | Fun τ1 τ2 =>
      support_simp [genZero] at h
      simp [varsWithType] at h
      rcases h with ⟨_, hf⟩ | ⟨_, hf⟩
      all_goals
        obtain ⟨argTy, _, hf, hx⟩ := hf
        apply Typing.TApp
        · apply IH2; assumption
        · apply IH1; assumption



#guard_msgs(drop info) in
#eval (for _ in [0:3] do
  IO.println <| repr (← genTerm [] .Bool) : IO Unit)

#guard_msgs(drop info) in
#eval (for _ in [0:3] do
  IO.println <| repr (← genTerm [] (.Fun .Bool .Bool)) : IO Unit)
