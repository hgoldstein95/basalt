/-
Copyright (c) 2026 Harrison Goldstein & Ernest Ng. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein & Ernest Ng
-/
import Basalt
import BasaltExamples.STLC.GenType

/-!
# Well-Typed STLC Terms

`genTerm Γ τ` generates exactly the terms of type `τ` in context `Γ`.
-/

open RandomChoice

/-- Generates an arbitrary `Bool`. -/
def Bool.arbitrary [Gen G] : G Bool :=
  oneOf! [fun _ => pure true, fun _ => pure false]

/-- Generates a Boolean literal. -/
def genBool [Gen G] : G Term :=
  Term.Bool <$> Bool.arbitrary

/-- Finds all variables in `Γ` that have type `τ` -/
def varsWithType (Γ : Ctx) (τ : Ty) : List Term :=
  Γ.zipIdx.filterMap (fun (τ', i) => if τ' == τ then some (Term.Var i) else none)

/-- Generates the smallest terms of type `τ`: a Boolean literal under as many abstractions as `τ`
has arrows. -/
def genZero [Gen G] (Γ : Ctx) (τ : Ty) : G Term :=
  match τ with
  | .Bool => genBool
  | .Fun τ1 τ2 => do
    let e ← genZero (τ1 :: Γ) τ2
    return .Abs τ1 e

/-- All terms in the list produced by `varsWithType` are sound -/
theorem varsWithType_sound :
    e ∈ varsWithType Γ τ → Typing Γ e τ := by
  intro h
  simp [varsWithType] at h
  obtain ⟨i, hmem, rfl⟩ := h
  apply Typing.TVar
  rw [List.mk_mem_zipIdx_iff_getElem?] at hmem
  apply getElem?_lookup
  assumption

/-- If `lookup Γ x τ` holds, then `Var x` is contained in the output of `varsWithType Γ τ` -/
theorem varsWithType_complete :
    lookup Γ x τ → Term.Var x ∈ varsWithType Γ τ := by
  intro h
  simp only [varsWithType, List.mem_filterMap]
  refine ⟨(τ, x), ?_, by simp⟩
  rw [List.mk_mem_zipIdx_iff_getElem?]
  exact lookup_getElem? h

/-- Generates a well-typed term at type `τ` in context `Γ`, choosing uniformly between `genZero`, a
variable when `Γ` has one of type `τ`, an application at an arbitrary argument type, and the
introduction form of `τ`. -/
def genTerm [Gen G] (Γ : Ctx) (τ : Ty) : G Term :=
  let vars := varsWithType Γ τ
  if hne : vars ≠ [] then
    oneOf! [
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
    ]
  else
    oneOf! [
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
    ]
partial_fixpoint

theorem Bool.arbitrary.sound_complete : IsSoundAndComplete Bool.arbitrary ⊤ := by
  refine .intro ?sound ?complete
  case sound => rw [IsSoundFor.iff_obs]; walk <;> trivial
  case complete => intro b _; cases b <;> (rw [SPMF.mem_support_iff_may]; walk)

theorem genZero.sound : IsSoundFor (genZero Γ τ) (Typing Γ · τ) := by
  induction τ generalizing Γ with
  | Bool =>
    unfold genZero; rw [IsSoundFor.iff_obs]; walk [Bool.arbitrary.sound_complete.sound.obs]
    constructor
  | Fun τ1 τ2 _ ih2 =>
    unfold genZero; rw [IsSoundFor.iff_obs]; walk [ih2.obs]; constructor; assumption

theorem genTerm.sound_complete : IsSoundAndComplete (genTerm Γ τ) (Typing Γ · τ) := by
  refine .intro ?sound ?complete
  case sound =>
    rw [IsSoundFor.iff_obs]
    walk fixpoint [genZero.sound.obs, genType.sound_complete.sound.obs,
      Bool.arbitrary.sound_complete.sound.obs]
    all_goals first
      | assumption
      | exact varsWithType_sound ‹_›
      | constructor <;> assumption
  case complete =>
    intro e h
    induction h with
    | TBool Γ b =>
      rw [genTerm, SPMF.mem_support_iff_may]
      walk [genType.sound_complete.complete.obs, Bool.arbitrary.sound_complete.complete.obs]
      split <;> simp
    | TVar Γ x τ hx =>
      have hmem := varsWithType_complete hx
      rw [genTerm.eq_def, SPMF.mem_support_iff_may]
      walk [genType.sound_complete.complete.obs, Bool.arbitrary.sound_complete.complete.obs]
      all_goals simp [List.ne_nil_of_mem hmem, hmem]
    | TAbs Γ body τ1 τ2 _ ih =>
      rw [genTerm, SPMF.mem_support_iff_may]
      walk [genType.sound_complete.complete.obs, Bool.arbitrary.sound_complete.complete.obs]
      split <;> simp [ih]
    | TApp Γ e1 e2 τ1 τ2 _ _ ih2 ih1 =>
      have happ : ∃ argTy, ∃ e1' ∈ SPMF.support (genTerm Γ (.Fun argTy τ2)),
          ∃ e2' ∈ SPMF.support (genTerm Γ argTy), Term.App e1' e2' = .App e1 e2 :=
        ⟨τ1, e1, ih1, e2, ih2, rfl⟩
      rw [genTerm.eq_def, SPMF.mem_support_iff_may]
      walk [genType.sound_complete.complete.obs, Bool.arbitrary.sound_complete.complete.obs]
      all_goals split <;> simp only [happ, or_true]
