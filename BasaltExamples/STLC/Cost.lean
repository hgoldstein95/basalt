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

This file defines the *context-aware* cost function for `genTerm` and proves `genTerm.cost_bounded`:
`genTerm Γ τ` makes at most `Term.costInCtx Γ` random choices.

## Why the bound must mention the context

`IsCostBounded g c` needs `c : Term → Nat` — a function of the *output term*. But the `App` branch
of `genTerm` (`BasaltExamples/STLC/GenTerm.lean`) spends `argTy.size` choices generating an argument
type via `genType`, and `argTy` is **not stored** in the produced `.App e1 e2`:

```
let argTy ← genType            -- costs `argTy.size` (see `genType_cost`)
let e1 ← genTerm Γ (.Fun argTy τ)
let e2 ← genTerm Γ argTy
return .App e1 e2
```

So there is no purely term-structural function that bounds the cost. The escape hatch is that this
is Church-style STLC, so **typing is unique**: `argTy` is recoverable as the type of `e2`, and
`e2 : argTy`. Concretely `argTy = typeCheck Γ e2` (the typechecker in `TypeCheck.lean` *is* the
`typeOf` we need, and `typeCheck_complete` *is* the `typeOf_of_Typing` uniqueness fact). Recovering
`argTy` requires knowing `Γ`, so the cost function threads the context.

`Term.costInCtx` must be total, so on ill-typed inputs the `App` case falls back to a default type
via `Option.getD`. That default is never observed by the cost proof: `genTerm`'s support is exactly
the well-typed terms (`genTerm_sound`), and `typeCheck_getD_of_typing` below is the *theorem* — not
a comment — witnessing that the `getD` collapses to the real type on every well-typed term,
regardless of the default. The final `IsCostBounded` guarantee is verified for every term `genTerm`
can produce; the default is invisible to it.

## The cost function

Charge one choice per `oneOf` selection plus the cost of the chosen branch, reading `genTerm`:

* `.Bool _`   : `oneOf` (1) + `genBool`/`genZero`-at-`Bool` (1)               = 2
* `.Var _`    : `oneOf` (1) + `elements` (1)                                  = 2
* `.Abs τ1 e` : `oneOf` (1) + recurse under the extended context `τ1 :: Γ`
* `.App e1 e2`: `oneOf` (1) + `genType` for `argTy` (`argTy.size`) + recurse on `e1` and `e2`

Note on `.Abs`: an `Abs` can be produced by *either* the recursive `Abs` branch *or* `genZero`.
The bound below charges the recursive-branch cost, which dominates the `genZero` path (`genZero`
makes exactly one choice), so it is a valid upper bound for both.
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
      let genType_cost := ((typeCheck Γ e2).getD .Bool).size
      1 + genType_cost + e1_cost + e2_cost

/-- On a well-typed term the `Option.getD` in `Term.costInCtx`'s `App` case collapses to the term's
    actual type, whatever the default `d` is. This is the formal replacement for the "the default is
    never hit" side remark: `genTerm`'s outputs are well-typed (`genTerm_sound`), so the cost proof
    only ever evaluates `costInCtx` where this lemma applies. -/
theorem typeCheck_getD_of_typing {d : Ty} (h : Typing Γ e τ) :
    (typeCheck Γ e).getD d = τ := by
  rw [typeCheck_complete h]; rfl

/-- Every term costs at least 2 choices to generate (one `oneOf` selection plus at least one more
    in the cheapest branch). Used to absorb the `genZero` branch, which costs `≤ 1`, into the bound
    for whatever term it produces. -/
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

/-- One step of `genTerm`'s cost support: every `(v, n)` it can produce comes from one of the four
    `oneOf` branches. The `genZero`/`elements` branches are folded into their generators; the `App`
    and `Abs`/`genBool` branches expose the recursive sub-calls (as *real* `genTerm` calls, so that
    `genTerm_sound` and the structural IH both apply to them). -/
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
    exact Typing.TAbs _ _ _ _ (IH2 hbody)

/-- Cost-level soundness: any `(e, n)` in `genTerm`'s cost support has `e` well-typed. This mirrors
    `genTerm_sound` (stated at `SPMF`) but at `SPMF.Cost`, so it can feed `typeCheck_getD_of_typing`
    inside the cost proof, where the sub-generators run at `SPMF.Cost`. -/
theorem genTerm_cost_sound {Γ τ e n}
    (hmem : (e, n) ∈ SPMF.support (genTerm (G := SPMF.Cost) Γ τ)) : Typing Γ e τ := by
  induction e generalizing Γ τ n with
  | Bool b =>
    rcases genTerm_cost_inv hmem with
      ⟨_, hz, _⟩ | ⟨hv, _⟩ | ⟨_, _, _, _, _, _, _, _, _, hveq, _⟩ |
      ⟨_, rfl, _, _⟩ | ⟨_, _, _, _, _, _, hveq, _⟩
    · exact genZero_cost_sound hz
    · exact varsWithType_sound hv
    · exact absurd hveq (by simp)
    · constructor
    · exact absurd hveq (by simp)
  | Var x =>
    rcases genTerm_cost_inv hmem with
      ⟨_, hz, _⟩ | ⟨hv, _⟩ | ⟨_, _, _, _, _, _, _, _, _, hveq, _⟩ |
      ⟨_, _, hveq, _⟩ | ⟨_, _, _, _, _, _, hveq, _⟩
    · exact genZero_cost_sound hz
    · exact varsWithType_sound hv
    · exact absurd hveq (by simp)
    · exact absurd hveq (by simp)
    · exact absurd hveq (by simp)
  | App e1 e2 IH1 IH2 =>
    rcases genTerm_cost_inv hmem with
      ⟨_, hz, _⟩ | ⟨hv, _⟩ |
      ⟨argTy, f1, f2, _, _, _, _, h1, h2, heq, _⟩ |
      ⟨_, _, hveq, _⟩ | ⟨_, _, _, _, _, _, hveq, _⟩
    · exact genZero_cost_sound hz
    · exact varsWithType_sound hv
    · obtain ⟨rfl, rfl⟩ : e1 = f1 ∧ e2 = f2 := by simpa using heq
      exact Typing.TApp _ _ _ argTy _ (IH2 h2) (IH1 h1)
    · exact absurd hveq (by simp)
    · exact absurd hveq (by simp)
  | Abs τ1 e IH =>
    rcases genTerm_cost_inv hmem with
      ⟨_, hz, _⟩ | ⟨hv, _⟩ | ⟨_, _, _, _, _, _, _, _, _, hveq, _⟩ |
      ⟨_, _, hveq, _⟩ | ⟨σ1, σ2, f, _, hτ, he, heq, _⟩
    · exact genZero_cost_sound hz
    · exact varsWithType_sound hv
    · exact absurd hveq (by simp)
    · exact absurd hveq (by simp)
    · obtain ⟨rfl, rfl⟩ : τ1 = σ1 ∧ e = f := by simpa using heq
      subst hτ
      exact Typing.TAbs _ _ _ _ (IH he)

/-- `genTerm Γ τ` makes at most `Term.costInCtx Γ` random choices.

    Proof: structural induction on the produced term. `genTerm_cost_inv` inverts one step of the
    generator into its four `oneOf` branches; each is discharged by a callee bound
    (`genZero.cost_bounded`, `IsBounded_elements`, `genType_cost`) or the structural IH, with the
    `App` branch recovering the discarded argument type via `typeCheck_getD_of_typing`. Because the
    induction is on the *term* (not `fix_induct`), every sub-call is a real `genTerm`, so
    `genTerm_sound` applies to its outputs. -/
theorem genTerm.cost_bounded :
    IsBounded (genTerm (G := SPMF.Cost) Γ τ) (Term.costInCtx Γ) := by
  rw [IsBounded_iff]
  rintro ⟨v, n⟩
  induction v generalizing Γ τ n with
  | Bool b =>
    intro hmem
    show n ≤ Term.costInCtx Γ (Term.Bool b)
    rcases genTerm_cost_inv hmem with
      ⟨nz, hz, rfl⟩ | ⟨hv, rfl⟩ | ⟨_, _, _, _, _, _, _, _, _, hveq, _⟩ |
      ⟨b', _, _, rfl⟩ | ⟨_, _, _, _, _, _, hveq, _⟩
    · have := IsBounded_iff.mp genZero.cost_bounded (Term.Bool b, nz) hz
      have := Term.two_le_costInCtx Γ (Term.Bool b); omega
    · have := Term.two_le_costInCtx Γ (Term.Bool b); omega
    · exact absurd hveq (by simp)
    · simp [Term.costInCtx]
    · exact absurd hveq (by simp)
  | Var x =>
    intro hmem
    show n ≤ Term.costInCtx Γ (Term.Var x)
    rcases genTerm_cost_inv hmem with
      ⟨nz, hz, rfl⟩ | ⟨hv, rfl⟩ | ⟨_, _, _, _, _, _, _, _, _, hveq, _⟩ |
      ⟨b', _, hveq, _⟩ | ⟨_, _, _, _, _, _, hveq, _⟩
    · have := IsBounded_iff.mp genZero.cost_bounded (Term.Var x, nz) hz
      have := Term.two_le_costInCtx Γ (Term.Var x); omega
    · simp [Term.costInCtx]
    · exact absurd hveq (by simp)
    · exact absurd hveq (by simp)
    · exact absurd hveq (by simp)
  | App e1 e2 IH1 IH2 =>
    intro hmem
    show n ≤ Term.costInCtx Γ (e1.App e2)
    rcases genTerm_cost_inv hmem with
      ⟨nz, hz, rfl⟩ | ⟨hv, rfl⟩ |
      ⟨argTy, f1, f2, nT, n1, n2, hT, h1, h2, heq, rfl⟩ |
      ⟨b', _, hveq, _⟩ | ⟨_, _, _, _, _, _, hveq, _⟩
    · have := IsBounded_iff.mp genZero.cost_bounded (e1.App e2, nz) hz
      have := Term.two_le_costInCtx Γ (e1.App e2); omega
    · have := Term.two_le_costInCtx Γ (e1.App e2); omega
    · obtain ⟨rfl, rfl⟩ : e1 = f1 ∧ e2 = f2 := by simpa using heq
      have hTy : nT ≤ argTy.size := IsBounded_iff.mp genType_cost (argTy, nT) hT
      have hb1 : n1 ≤ Term.costInCtx Γ e1 := IH1 n1 h1
      have hb2 : n2 ≤ Term.costInCtx Γ e2 := IH2 n2 h2
      have harg : (typeCheck Γ e2).getD Ty.Bool = argTy :=
        typeCheck_getD_of_typing (genTerm_cost_sound h2)
      simp only [Term.costInCtx, harg]
      omega
    · exact absurd hveq (by simp)
    · exact absurd hveq (by simp)
  | Abs τ1 e IH =>
    intro hmem
    show n ≤ Term.costInCtx Γ (Term.Abs τ1 e)
    rcases genTerm_cost_inv hmem with
      ⟨nz, hz, rfl⟩ | ⟨hv, rfl⟩ | ⟨_, _, _, _, _, _, _, _, _, hveq, _⟩ |
      ⟨b', _, hveq, _⟩ | ⟨σ1, σ2, f, ne, hτ, he, heq, rfl⟩
    · have := IsBounded_iff.mp genZero.cost_bounded (Term.Abs τ1 e, nz) hz
      have := Term.two_le_costInCtx Γ (Term.Abs τ1 e); omega
    · have := Term.two_le_costInCtx Γ (Term.Abs τ1 e); omega
    · exact absurd hveq (by simp)
    · exact absurd hveq (by simp)
    · obtain ⟨rfl, rfl⟩ : τ1 = σ1 ∧ e = f := by simpa using heq
      have hb : ne ≤ Term.costInCtx (τ1 :: Γ) e := IH ne he
      simp only [Term.costInCtx]
      omega
