/-
Copyright (c) 2026 Harrison Goldstein & Ernest Ng. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein & Ernest Ng
-/
import Basalt
import Basalt.PlausibleGen
import BasaltExamples.STLC.Syntax
import BasaltExamples.STLC.GenType
import BasaltExamples.STLC.GenTerm
import BasaltExamples.STLC.TypeCheck

open RandomChoice SPMF List

/-!
# Cost Bound for `genTerm`

This file defines a cost function for `genTerm` (`Term.costInCtx`)
that takes the context `Γ` into account,
and proves that `genTerm Γ τ` makes at most `Term.costInCtx Γ` random choices.

## Why the bound must mention the context

`IsCostBounded g c` needs a cost function `c : Term → Nat` that only takes
the term into account. However, the `App` branch of `genTerm` generates a random argument
type `argTy` for `e2`, but `argTy` isn't apparent in `.App e1 e2`:

```lean
let argTy ← genType            -- costs `argTy.size` (see `genType_cost`)
let e1 ← genTerm Γ (.Fun argTy τ)
let e2 ← genTerm Γ argTy
return .App e1 e2
```

So there is no purely term-structural function that bounds the cost.
However, in STLC, types are unique, so `argTy` is unique, and we can use
an STLC typechecker (that is proven sound & complete with respect to the typing relation)
to determine that `argTy = typeCheck Γ e2`.

This means that in order to recover `argTy`, we need access to the context `Γ`,
so the cost function takes `Γ` as an argument.

## The cost function

The cost function charges the folowing depending on the shape of the generated term:

* `.Bool _`   : call to `oneOf` (1) + call to `genBool`/`genZero`-at-`Bool` (1) = 2
* `.Var _`    : call to `oneOf` (1) + call to `elements` (1)  = 2
* `.Abs τ1 e` : call to `oneOf` (1) + recurse under the extended context `τ1 :: Γ`
* `.App e1 e2`: call to `oneOf` (1) + call `genType` for `argTy` (`argTy.size`) + recurse on `e1` and `e2`

Note on `.Abs`: an `Abs` can be produced by *either* the recursive `Abs` branch *or* `genZero`.
The cost bound for the `Abs` case charges the recursive-branch cost, since
it is greater than the `genZero` cost (since `genZero` makes exactly one choice.)
-/

/-- Context-aware cost bound for `genTerm Γ`. Counts the random choices `genTerm` makes to
    reproduce a term, recovering each discarded application-argument type from `typeCheck`. -/
def Term.costInCtx (Γ : Ctx) (e : Term) : Nat :=
  match e with
  | .Bool _    => 2
  | .Var _     => 2
  | .Abs τ1 e  => 1 + Term.costInCtx (τ1 :: Γ) e
  | .App e1 e2 =>
      let e1_cost := Term.costInCtx Γ e1
      let e2_cost := Term.costInCtx Γ e2
      -- Note: since the typechecker returns an option, we need to call `Option.getD` here
      -- The lemma below establishes that if `Γ ⊢ e2 : τ2`, we always have `(typeCheck Γ e2).getD ... = τ2`
      let genType_cost := ((typeCheck Γ e2).getD .Bool).size
      1 + genType_cost + e1_cost + e2_cost

/-- If `Γ ⊢ e : τ`, then `Option.getD (typeCheck Γ e) default = τ`,
    i.e. the default argument supplied to `Option.getD` is never returned. -/
theorem typeCheck_getD_of_typing {default : Ty} (h : Typing Γ e τ) :
    (typeCheck Γ e).getD default = τ := by
  rw [typeCheck_complete h]; rfl

/-- Every term costs at least 2 choices to generate (one `oneOf` selection plus at least one more
    in the cheapest branch). -/
theorem Term.two_le_costInCtx (Γ : Ctx) (e : Term) : 2 ≤ Term.costInCtx Γ e := by
  induction e generalizing Γ with
  | Bool => simp [Term.costInCtx]
  | Var => simp [Term.costInCtx]
  | Abs τ1 e IH => simp only [Term.costInCtx]; have := IH (τ1 :: Γ); omega
  | App e1 e2 IH1 _ => simp only [Term.costInCtx]; have := IH1 Γ; omega

/-- `genBool` makes exactly one random choice (the coin in `Bool.arbitrary`). -/
theorem genBool.cost_bounded : IsBounded (genBool (G := SPMF.Cost)) (fun _ => 1) := by
  unfold genBool Bool.arbitrary
  apply IsBounded_map
  · apply IsBounded_pick <;> apply IsBounded_pure
  · intro p _; simp

/-- `genZero Γ τ` makes exactly one random choice: the `Abs` wrapping is pure, and only the
    terminal `genBool` flips a coin. -/
theorem genZero.cost_bounded : IsBounded (genZero (G := SPMF.Cost) Γ τ) (fun _ => 1) := by
  induction τ generalizing Γ with
  | Bool => unfold genZero; exact genBool.cost_bounded
  | Fun τ1 τ2 _ IH2 =>
    unfold genZero
    apply IsBounded_bind (cx := fun _ => 1) (cf := fun _ _ => 0)
    · exact IH2
    · intro e; apply IsBounded_pure
    · intro _ _; simp

/-- Inversion lemma for the `SPMF.Cost` interpretation of `genTerm`. -/
theorem genTerm_cost_inv {Γ τ v n}
    (hmem : (v, n) ∈ SPMF.support (genTerm (G := SPMF.Cost) Γ τ)) :
    (∃ nz, (v, nz) ∈ SPMF.support (genZero (G := SPMF.Cost) Γ τ) ∧ n = 1 + nz) ∨
    (v ∈ varsWithType Γ τ ∧ n = 2) ∨
    (∃ argTy e1 e2 nT n1 n2,
        (argTy, nT) ∈ SPMF.support (genType (G := SPMF.Cost)) ∧
        (e1, n1) ∈ SPMF.support (genTerm (G := SPMF.Cost) Γ (argTy.Fun τ)) ∧
        (e2, n2) ∈ SPMF.support (genTerm (G := SPMF.Cost) Γ argTy) ∧
        v = e1.App e2 ∧ n = 1 + (nT + (n1 + n2))) ∨
    (∃ b, τ = Ty.Bool ∧ v = Term.Bool b ∧ n = 2) ∨
    (∃ τ1 τ2 e ne, τ = τ1.Fun τ2 ∧
        (e, ne) ∈ SPMF.support (genTerm (G := SPMF.Cost) (τ1 :: Γ) τ2) ∧
        v = Term.Abs τ1 e ∧ n = 1 + ne) := by
  unfold genTerm at hmem
  cost_support_simp at hmem
  obtain ⟨hne, hmem⟩ | ⟨hne, hmem⟩ := hmem <;>
    unfold oneOf Helpers.oneOfAux at hmem <;>
    cost_support_simp at hmem <;>
    obtain ⟨⟨i, hi0, hilt⟩, n1, n2, ⟨hd, rfl, heq⟩, hmem, rfl⟩ := hmem <;>
    simp only [List.length_cons, List.length_nil] at hilt <;>
    clear hd heq <;>
    dsimp only at hmem
  · -- vars ≠ [] : branches genZero / elements / App / (Bool→genBool | Fun→Abs)
    match i, hilt, hmem with
    | 0, _, hmem =>
      simp only [List.getElem_cons_zero] at hmem
      exact Or.inl ⟨n2, hmem, rfl⟩
    | 1, _, hmem =>
      simp only [List.getElem_cons_succ, List.getElem_cons_zero] at hmem
      unfold elements at hmem
      cost_support_simp at hmem
      obtain ⟨⟨j, hj0, hjlt⟩, _, _, ⟨_, rfl, _⟩, hpure, rfl⟩ := hmem
      dsimp only at hpure
      cost_support_simp at hpure
      obtain ⟨rfl, rfl⟩ := hpure
      refine Or.inr (Or.inl ⟨?_, by omega⟩)
      exact List.getElem_mem _
    | 2, _, hmem =>
      simp only [List.getElem_cons_succ, List.getElem_cons_zero] at hmem
      cost_support_simp at hmem
      obtain ⟨argTy, nT, _, hT, ⟨e1, m1, _, h1, ⟨e2, _, _, h2, ⟨rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩ := hmem
      rename_i m2
      exact Or.inr (Or.inr (Or.inl ⟨argTy, e1, e2, nT, m1, m2, hT, h1, h2, rfl, rfl⟩))
    | 3, _, hmem =>
      simp only [List.getElem_cons_succ, List.getElem_cons_zero] at hmem
      cases τ with
      | Bool =>
        simp only at hmem
        unfold genBool Bool.arbitrary at hmem
        cost_support_simp at hmem
        obtain ⟨a, ⟨m, rfl, hm⟩, rfl⟩ := hmem
        refine Or.inr (Or.inr (Or.inr (Or.inl ⟨a, rfl, rfl, ?_⟩)))
        rcases hm with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> rfl
      | Fun τ1 τ2 =>
        cost_support_simp at hmem
        obtain ⟨e, ne, _, he, ⟨rfl, rfl⟩, rfl⟩ := hmem
        exact Or.inr (Or.inr (Or.inr (Or.inr ⟨τ1, τ2, e, n2, rfl, he, rfl, by omega⟩)))
    | (k+4), hilt, _ => omega
  · -- vars = [] : branches genZero / App / (Bool→genBool | Fun→Abs)
    match i, hilt, hmem with
    | 0, _, hmem =>
      simp only [List.getElem_cons_zero] at hmem
      exact Or.inl ⟨n2, hmem, rfl⟩
    | 1, _, hmem =>
      simp only [List.getElem_cons_succ, List.getElem_cons_zero] at hmem
      cost_support_simp at hmem
      obtain ⟨argTy, nT, _, hT, ⟨e1, m1, _, h1, ⟨e2, _, _, h2, ⟨rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩ := hmem
      rename_i m2
      exact Or.inr (Or.inr (Or.inl ⟨argTy, e1, e2, nT, m1, m2, hT, h1, h2, rfl, rfl⟩))
    | 2, _, hmem =>
      simp only [List.getElem_cons_succ, List.getElem_cons_zero] at hmem
      cases τ with
      | Bool =>
        simp only at hmem
        unfold genBool Bool.arbitrary at hmem
        cost_support_simp at hmem
        obtain ⟨a, ⟨m, rfl, hm⟩, rfl⟩ := hmem
        refine Or.inr (Or.inr (Or.inr (Or.inl ⟨a, rfl, rfl, ?_⟩)))
        rcases hm with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> rfl
      | Fun τ1 τ2 =>
        cost_support_simp at hmem
        obtain ⟨e, ne, _, he, ⟨rfl, rfl⟩, rfl⟩ := hmem
        exact Or.inr (Or.inr (Or.inr (Or.inr ⟨τ1, τ2, e, n2, rfl, he, rfl, by omega⟩)))
    | (k+3), hilt, _ => omega

/-- Cost-level soundness for `genZero`, mirroring `genZero_sound` at `SPMF.Cost`. -/
theorem genZero_cost_sound {Γ τ e n}
    (hmem : (e, n) ∈ SPMF.support (genZero (G := SPMF.Cost) Γ τ)) : Typing Γ e τ := by
  induction τ generalizing Γ e n with
  | Bool =>
    unfold genZero genBool Bool.arbitrary at hmem
    cost_support_simp at hmem
    obtain ⟨a, _, rfl⟩ := hmem
    constructor
  | Fun τ1 τ2 _ IH2 =>
    unfold genZero at hmem
    cost_support_simp at hmem
    obtain ⟨body, nb, _, hbody, ⟨rfl, rfl⟩, rfl⟩ := hmem
    have htbody : Typing (τ1 :: Γ) body τ2 := IH2 hbody
    apply Typing.TAbs; assumption

/-- For any `(e, n)` in the support of the `SPMF.cost` interpretation of `genTerm`,
    `e` is well-typed. This is similar to  `genTerm_sound` (stated at `SPMF`) but at `SPMF.Cost`,
    so it can feed `typeCheck_getD_of_typing` inside the cost proof, where the sub-generators run at `SPMF.Cost`. -/
theorem genTerm_cost_sound {Γ τ e n}
    (hmem : (e, n) ∈ SPMF.support (genTerm (G := SPMF.Cost) Γ τ)) : Typing Γ e τ := by
  induction e generalizing Γ τ n with
  | Bool b =>
    rcases genTerm_cost_inv hmem with
      ⟨_, hz, _⟩ | ⟨hv, _⟩ | ⟨_, _, _, _, _, _, _, _, _, hveq, _⟩ |
      ⟨_, rfl, _, _⟩ | ⟨_, _, _, _, _, _, hveq, _⟩
    · exact genZero_cost_sound hz
    · exact varsWithType_sound hv
    · simp at hveq
    · constructor
    · simp at hveq
  | Var x =>
    rcases genTerm_cost_inv hmem with
      ⟨_, hz, _⟩ | ⟨hv, _⟩ | ⟨_, _, _, _, _, _, _, _, _, hveq, _⟩ |
      ⟨_, _, hveq, _⟩ | ⟨_, _, _, _, _, _, hveq, _⟩
    · exact genZero_cost_sound hz
    · exact varsWithType_sound hv
    · simp at hveq
    · simp at hveq
    · simp at hveq
  | App e1 e2 IH1 IH2 =>
    rcases genTerm_cost_inv hmem with
      ⟨_, hz, _⟩ | ⟨hv, _⟩ |
      ⟨argTy, f1, f2, _, _, _, _, h1, h2, heq, _⟩ |
      ⟨_, _, hveq, _⟩ | ⟨_, _, _, _, _, _, hveq, _⟩
    · exact genZero_cost_sound hz
    · exact varsWithType_sound hv
    · obtain ⟨rfl, rfl⟩ : e1 = f1 ∧ e2 = f2 := by simpa using heq
      have htf : Typing Γ e1 (argTy.Fun τ) := IH1 h1
      have hta : Typing Γ e2 argTy := IH2 h2
      apply Typing.TApp <;> assumption
    · simp at hveq
    · simp at hveq
  | Abs τ1 e IH =>
    rcases genTerm_cost_inv hmem with
      ⟨_, hz, _⟩ | ⟨hv, _⟩ | ⟨_, _, _, _, _, _, _, _, _, hveq, _⟩ |
      ⟨_, _, hveq, _⟩ | ⟨σ1, σ2, f, _, hτ, he, heq, _⟩
    · exact genZero_cost_sound hz
    · exact varsWithType_sound hv
    · simp at hveq
    · simp at hveq
    · obtain ⟨rfl, rfl⟩ : τ1 = σ1 ∧ e = f := by simpa using heq
      subst hτ
      have htbody : Typing (τ1 :: Γ) e σ2 := IH he
      apply Typing.TAbs; assumption

/-- `genTerm Γ τ` makes at most `Term.costInCtx Γ` random choices.

    This is proven by induction on the generated term.
    The inversion lemma `genTerm_cost_inv` inverts one step of the
    generator into its four `oneOf` branches; each is discharged by a cost bound on the sub-generator
    (`genZero.cost_bounded`, `IsBounded_elements`, `genType_cost`) or the IH, with the
    `App e1 e2` branch recovering the type of `e2` via the lemma `typeCheck_getD_of_typing`. -/
theorem genTerm.cost_bounded :
    IsBounded (genTerm (G := SPMF.Cost) Γ τ) (Term.costInCtx Γ) := by
  rw [IsBounded_iff]
  rintro ⟨e, n⟩
  induction e generalizing Γ τ n with
  | Bool b =>
    intro hmem
    show n ≤ Term.costInCtx Γ (Term.Bool b)
    rcases genTerm_cost_inv hmem with
      ⟨nz, hz, rfl⟩ | ⟨hv, rfl⟩ | ⟨_, _, _, _, _, _, _, _, _, hveq, _⟩ |
      ⟨b', _, _, rfl⟩ | ⟨_, _, _, _, _, _, hveq, _⟩
    · have hzc : nz ≤ 1 := IsBounded_iff.mp genZero.cost_bounded (Term.Bool b, nz) hz
      have hlo : 2 ≤ Term.costInCtx Γ (Term.Bool b) := Term.two_le_costInCtx Γ (Term.Bool b)
      omega
    · have hlo : 2 ≤ Term.costInCtx Γ (Term.Bool b) := Term.two_le_costInCtx Γ (Term.Bool b)
      omega
    · simp at hveq
    · simp [Term.costInCtx]
    · simp at hveq
  | Var x =>
    intro hmem
    show n ≤ Term.costInCtx Γ (Term.Var x)
    rcases genTerm_cost_inv hmem with
      ⟨nz, hz, rfl⟩ | ⟨hv, rfl⟩ | ⟨_, _, _, _, _, _, _, _, _, hveq, _⟩ |
      ⟨b', _, hveq, _⟩ | ⟨_, _, _, _, _, _, hveq, _⟩
    · have hzc : nz ≤ 1 := IsBounded_iff.mp genZero.cost_bounded (Term.Var x, nz) hz
      have hlo : 2 ≤ Term.costInCtx Γ (Term.Var x) := Term.two_le_costInCtx Γ (Term.Var x)
      omega
    · simp [Term.costInCtx]
    · simp at hveq
    · simp at hveq
    · simp at hveq
  | App e1 e2 IH1 IH2 =>
    intro hmem
    show n ≤ Term.costInCtx Γ (e1.App e2)
    rcases genTerm_cost_inv hmem with
      ⟨nz, hz, rfl⟩ | ⟨hv, rfl⟩ |
      ⟨argTy, f1, f2, nT, n1, n2, hT, h1, h2, heq, rfl⟩ |
      ⟨b', _, hveq, _⟩ | ⟨_, _, _, _, _, _, hveq, _⟩
    · have hzc : nz ≤ 1 := IsBounded_iff.mp genZero.cost_bounded (e1.App e2, nz) hz
      have hlo : 2 ≤ Term.costInCtx Γ (e1.App e2) := Term.two_le_costInCtx Γ (e1.App e2)
      omega
    · have hlo : 2 ≤ Term.costInCtx Γ (e1.App e2) := Term.two_le_costInCtx Γ (e1.App e2)
      omega
    · obtain ⟨rfl, rfl⟩ : e1 = f1 ∧ e2 = f2 := by simpa using heq
      have hTy : nT ≤ argTy.size := IsBounded_iff.mp genType_cost (argTy, nT) hT
      have hb1 : n1 ≤ Term.costInCtx Γ e1 := IH1 n1 h1
      have hb2 : n2 ≤ Term.costInCtx Γ e2 := IH2 n2 h2
      have harg : (typeCheck Γ e2).getD Ty.Bool = argTy :=
        typeCheck_getD_of_typing (genTerm_cost_sound h2)
      simp only [Term.costInCtx, harg]
      omega
    · simp at hveq
    · simp at hveq
  | Abs τ1 e IH =>
    intro hmem
    show n ≤ Term.costInCtx Γ (Term.Abs τ1 e)
    rcases genTerm_cost_inv hmem with
      ⟨nz, hz, rfl⟩ | ⟨hv, rfl⟩ | ⟨_, _, _, _, _, _, _, _, _, hveq, _⟩ |
      ⟨b', _, hveq, _⟩ | ⟨σ1, σ2, f, ne, hτ, he, heq, rfl⟩
    · have hzc : nz ≤ 1 := IsBounded_iff.mp genZero.cost_bounded (Term.Abs τ1 e, nz) hz
      have hlo : 2 ≤ Term.costInCtx Γ (Term.Abs τ1 e) := Term.two_le_costInCtx Γ (Term.Abs τ1 e)
      omega
    · have hlo : 2 ≤ Term.costInCtx Γ (Term.Abs τ1 e) := Term.two_le_costInCtx Γ (Term.Abs τ1 e)
      omega
    · simp at hveq
    · simp at hveq
    · obtain ⟨rfl, rfl⟩ : τ1 = σ1 ∧ e = f := by simpa using heq
      have hb : ne ≤ Term.costInCtx (τ1 :: Γ) e := IH ne he
      simp only [Term.costInCtx]
      omega
