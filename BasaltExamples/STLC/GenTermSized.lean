/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt
import BasaltExamples.STLC.GenTerm

/-!
# Sized Well-Typed STLC Terms

`genTermSized n Γ τ` generates terms of type `τ` in context `Γ` with at most `n` nested choices.
It is sound at every size and complete in the limit, and it makes at most `termCost n` choices on
every run. Its leaves are variables wherever one fits, and its weights favor applications.
-/

open RandomChoice

/-- The longest chain of arrows in a type. -/
def Ty.depth : Ty → Nat
  | .Bool => 0
  | .Fun τ1 τ2 => 1 + max τ1.depth τ2.depth

/-- Generates a type of depth at most `size`, with `Bool` twice as likely as an arrow. -/
@[tunable (depth := size)]
def genTypeSized [Gen G] (size : Nat) : G Ty :=
  match size with
  | 0 => pure .Bool
  | n + 1 =>
    frequency! [
      (2, fun _ => pure .Bool),
      (1, fun _ => do
        let τ1 ← genTypeSized n
        let τ2 ← genTypeSized n
        return .Fun τ1 τ2)]

/-- Generates a smallest term of type `τ` that uses what is in scope: a variable when `Γ` has one of
type `τ`, and otherwise the introduction form of `τ` around such a term. -/
def genLeaf [Gen G] (Γ : Ctx) (τ : Ty) : G Term :=
  if hne : varsWithType Γ τ ≠ [] then
    elements (varsWithType Γ τ) hne
  else
    match τ with
    | .Bool => genBool
    | .Fun τ1 τ2 => do
      let e ← genLeaf (τ1 :: Γ) τ2
      return .Abs τ1 e

/-- Generates a well-typed term at type `τ` in context `Γ`. At size `0` it is a `genLeaf`; above, it
chooses between a variable when `Γ` has one of type `τ`, an application at an argument type of depth
at most half the remaining size, and the introduction form of `τ`, weighted separately at `Bool`
(where that form is a literal) and at an arrow (where it is an abstraction). -/
@[tunable (depth := size)]
def genTermSized [Gen G] (size : Nat) (Γ : Ctx) (τ : Ty) : G Term :=
  match size with
  | 0 => genLeaf Γ τ
  | n + 1 =>
    match τ with
    | .Bool =>
      if hne : varsWithType Γ .Bool ≠ [] then
        frequency! [
          (2, fun _ => elements (varsWithType Γ .Bool) hne),
          (4, fun _ => do
            let argTy ← genTypeSized (n / 2)
            let e1 ← genTermSized n Γ (.Fun argTy .Bool)
            let e2 ← genTermSized n Γ argTy
            return .App e1 e2),
          (1, fun _ => genBool)]
      else
        frequency! [
          (4, fun _ => do
            let argTy ← genTypeSized (n / 2)
            let e1 ← genTermSized n Γ (.Fun argTy .Bool)
            let e2 ← genTermSized n Γ argTy
            return .App e1 e2),
          (1, fun _ => genBool)]
    | .Fun τ1 τ2 =>
      if hne : varsWithType Γ (.Fun τ1 τ2) ≠ [] then
        frequency! [
          (2, fun _ => elements (varsWithType Γ (.Fun τ1 τ2)) hne),
          (4, fun _ => do
            let argTy ← genTypeSized (n / 2)
            let e1 ← genTermSized n Γ (.Fun argTy (.Fun τ1 τ2))
            let e2 ← genTermSized n Γ argTy
            return .App e1 e2),
          (2, fun _ => do
            let e ← genTermSized n (τ1 :: Γ) τ2
            return .Abs τ1 e)]
      else
        frequency! [
          (4, fun _ => do
            let argTy ← genTypeSized (n / 2)
            let e1 ← genTermSized n Γ (.Fun argTy (.Fun τ1 τ2))
            let e2 ← genTermSized n Γ argTy
            return .App e1 e2),
          (2, fun _ => do
            let e ← genTermSized n (τ1 :: Γ) τ2
            return .Abs τ1 e)]

/-! ## Types -/

theorem genTypeSized.sound_complete :
    IsSoundAndComplete (genTypeSized n) (fun τ => τ.depth ≤ n) := by
  refine .intro ?sound ?complete
  case sound =>
    induction n with
    | zero => rw [IsSoundFor.iff_obs, genTypeSized]; walk; simp [Ty.depth]
    | succ n ih =>
      rw [IsSoundFor.iff_obs, genTypeSized]; walk [ih.obs]
      all_goals simp only [Ty.depth] at *; omega
  case complete =>
    intro τ
    induction τ generalizing n with
    | Bool =>
      intro _
      cases n <;> (rw [genTypeSized, SPMF.mem_support_iff_may]; walk)
    | Fun τ1 τ2 ih1 ih2 =>
      intro h
      obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp only [Ty.depth] at h; omega⟩
      rw [genTypeSized, SPMF.mem_support_iff_may]; walk
      exact ⟨τ1, ih1 (by simp only [Ty.depth] at h; omega),
        τ2, ih2 (by simp only [Ty.depth] at h; omega), rfl⟩

theorem genTypeSized.terminates : IsAlmostSurelyTerminating (genTypeSized n) := by
  induction n with
  | zero => rw [IsAlmostSurelyTerminating.iff_obs, genTypeSized]; walk; rfl
  | succ n ih =>
    rw [IsAlmostSurelyTerminating.iff_obs, genTypeSized]; walk [ih.obs]
    norm_num [ENNReal.div_self]

/-- The most choices `genTypeSized n` makes: one per arrow of a full tree of depth `n`. -/
def typeCost : Nat → Nat
  | 0 => 0
  | n + 1 => 1 + 2 * typeCost n

theorem genTypeSized.cost_bounded : IsCostBounded (genTypeSized n) (fun _ => typeCost n) := by
  induction n with
  | zero => rw [IsCostBounded.iff_obs, genTypeSized]; walk; simp [typeCost]
  | succ n ih =>
    rw [IsCostBounded.iff_obs, genTypeSized]; walk [ih.obs]
    all_goals simp only [typeCost] at *; omega

theorem genTypeSized.faithful : IsFaithful (genTypeSized n) where
  terminates := genTypeSized.terminates
  below _ _ _ := by
    induction n with
    | zero => unfold genTypeSized; walk
    | succ n ih => unfold genTypeSized; walk
  approx := by
    induction n with
    | zero => unfold genTypeSized; walk
    | succ n ih => unfold genTypeSized; walk

theorem genTypeSized.cost_faithful : IsCostFaithful (genTypeSized n) where
  erasedLe := by
    induction n with
    | zero => unfold genTypeSized; walk
    | succ n ih => unfold genTypeSized; walk
  leErased := by
    induction n with
    | zero => unfold genTypeSized; walk
    | succ n ih => unfold genTypeSized; walk

/-! ## Leaves -/

theorem genLeaf.sound : IsSoundFor (genLeaf Γ τ) (Typing Γ · τ) := by
  induction τ generalizing Γ with
  | Bool =>
    rw [IsSoundFor.iff_obs, genLeaf]; walk [Bool.arbitrary.sound_complete.sound.obs]
    all_goals first | exact varsWithType_sound ‹_› | constructor
  | Fun τ1 τ2 _ ih2 =>
    rw [IsSoundFor.iff_obs, genLeaf]; walk [ih2.obs]
    all_goals first | exact varsWithType_sound ‹_› | constructor; assumption

theorem genLeaf.terminates : IsAlmostSurelyTerminating (genLeaf Γ τ) := by
  induction τ generalizing Γ with
  | Bool =>
    rw [IsAlmostSurelyTerminating.iff_obs, genLeaf]; walk
    split <;> norm_num [ENNReal.div_self]
  | Fun τ1 τ2 _ ih2 =>
    rw [IsAlmostSurelyTerminating.iff_obs, genLeaf]; walk [ih2.obs]
    split <;> norm_num [ENNReal.div_self]

theorem genLeaf.cost_bounded : IsCostBounded (genLeaf Γ τ) (fun _ => 1) := by
  induction τ generalizing Γ with
  | Bool => rw [IsCostBounded.iff_obs, genLeaf]; walk <;> omega
  | Fun τ1 τ2 _ ih2 => rw [IsCostBounded.iff_obs, genLeaf]; walk [ih2.obs] <;> omega

theorem genLeaf.faithful : IsFaithful (genLeaf Γ τ) where
  terminates := genLeaf.terminates
  below _ _ _ := by
    induction τ generalizing Γ with
    | Bool => unfold genLeaf; walk
    | Fun τ1 τ2 _ ih => unfold genLeaf; walk
  approx := by
    induction τ generalizing Γ with
    | Bool => unfold genLeaf; walk
    | Fun τ1 τ2 _ ih => unfold genLeaf; walk

theorem genLeaf.cost_faithful : IsCostFaithful (genLeaf Γ τ) where
  erasedLe := by
    induction τ generalizing Γ with
    | Bool => unfold genLeaf; walk
    | Fun τ1 τ2 _ ih => unfold genLeaf; walk
  leErased := by
    induction τ generalizing Γ with
    | Bool => unfold genLeaf; walk
    | Fun τ1 τ2 _ ih => unfold genLeaf; walk

/-! ## Terms -/

theorem genTermSized.sound : IsSoundFor (genTermSized n Γ τ) (Typing Γ · τ) := by
  induction n generalizing Γ τ with
  | zero => rw [genTermSized]; exact genLeaf.sound
  | succ n ih =>
    rw [IsSoundFor.iff_obs]; unfold genTermSized
    walk [ih.obs, genTypeSized.sound_complete.sound.obs, Bool.arbitrary.sound_complete.sound.obs]
    all_goals first
      | exact varsWithType_sound ‹_›
      | constructor <;> assumption

theorem genTermSized.terminates : IsAlmostSurelyTerminating (genTermSized n Γ τ) := by
  induction n generalizing Γ τ with
  | zero => rw [genTermSized]; exact genLeaf.terminates
  | succ n ih =>
    rw [IsAlmostSurelyTerminating.iff_obs]; unfold genTermSized
    walk [ih.obs, genTypeSized.terminates.obs]
    all_goals norm_num [ENNReal.div_self]

/-- The most choices `genTermSized n` makes: one to choose a branch, and an application's argument
type and two subterms. -/
def termCost : Nat → Nat
  | 0 => 1
  | n + 1 => 1 + typeCost (n / 2) + 2 * termCost n

theorem one_le_termCost (n : Nat) : 1 ≤ termCost n := by
  cases n <;> simp only [termCost] <;> omega

/-- Every run makes at most `termCost n` choices, whatever it produces. -/
theorem genTermSized.cost_bounded : IsCostBounded (genTermSized n Γ τ) (fun _ => termCost n) := by
  induction n generalizing Γ τ with
  | zero => rw [genTermSized]; exact genLeaf.cost_bounded
  | succ n ih =>
    rw [IsCostBounded.iff_obs]; unfold genTermSized
    walk [ih.obs, genTypeSized.cost_bounded.obs]
    all_goals have := one_le_termCost n
    all_goals simp only [termCost] at *; omega

theorem genTermSized.faithful : IsFaithful (genTermSized n Γ τ) where
  terminates := genTermSized.terminates
  below _ _ _ := by
    induction n generalizing Γ τ with
    | zero => unfold genTermSized; walk [genLeaf.faithful.below]
    | succ n ih => unfold genTermSized; walk [genTypeSized.faithful.below]
  approx := by
    induction n generalizing Γ τ with
    | zero => unfold genTermSized; walk [genLeaf.faithful.approx]
    | succ n ih => unfold genTermSized; walk [genTypeSized.faithful.approx]

theorem genTermSized.cost_faithful : IsCostFaithful (genTermSized n Γ τ) where
  erasedLe := by
    induction n generalizing Γ τ with
    | zero => unfold genTermSized; walk [genLeaf.cost_faithful.erasedLe]
    | succ n ih => unfold genTermSized; walk [genTypeSized.cost_faithful.erasedLe]
  leErased := by
    induction n generalizing Γ τ with
    | zero => unfold genTermSized; walk [genLeaf.cost_faithful.leErased]
    | succ n ih => unfold genTermSized; walk [genTypeSized.cost_faithful.leErased]

/-- The worst case bounds the average. -/
theorem genTermSized.expected_cost :
    IsExpectedCostBounded (genTermSized n Γ τ : SPMF.Cost Term) (termCost n) := by
  refine (IsExpectedCostBounded.of_costBounded genTermSized.cost_faithful
    genTermSized.cost_bounded).mono ?_
  exact SPMF.expect_le_of_support fun _ _ => le_rfl

/-- Every well-typed term is generated at every size from some size on. -/
theorem genTermSized.complete (h : Typing Γ e τ) :
    ∃ N, ∀ n ≥ N, e ∈ SPMF.support (genTermSized n Γ τ) := by
  induction h with
  | TBool Γ b =>
    refine ⟨1, fun n hn => ?_⟩
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [SPMF.mem_support_iff_may]; unfold genTermSized
    walk [Bool.arbitrary.sound_complete.complete.obs]
    split <;> simp
  | TVar Γ x τ hx =>
    have hmem := varsWithType_complete hx
    have hne := List.ne_nil_of_mem hmem
    refine ⟨0, fun n _ => ?_⟩
    cases n with
    | zero =>
      rw [genTermSized, genLeaf, dite_eq_left_of_eq_true (eq_true hne),
        SPMF.mem_support_iff_may]
      walk
      exact hmem
    | succ n =>
      rw [SPMF.mem_support_iff_may]; unfold genTermSized; walk
      all_goals split <;> simp_all
  | TAbs Γ body τ1 τ2 _ ih =>
    obtain ⟨N, hN⟩ := ih
    refine ⟨N + 1, fun n hn => ?_⟩
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [SPMF.mem_support_iff_may]; unfold genTermSized; walk
    split <;> simp [hN n (by omega)]
  | TApp Γ e1 e2 τ1 τ2 _ _ ih2 ih1 =>
    obtain ⟨N1, hN1⟩ := ih1
    obtain ⟨N2, hN2⟩ := ih2
    refine ⟨max (max N1 N2) (2 * τ1.depth) + 1, fun n hn => ?_⟩
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hty := (genTypeSized.sound_complete (n := n / 2)).complete τ1 (by omega)
    have happ : ∃ argTy ∈ SPMF.support (genTypeSized (n / 2)),
        ∃ e1' ∈ SPMF.support (genTermSized n Γ (.Fun argTy τ2)),
        ∃ e2' ∈ SPMF.support (genTermSized n Γ argTy), Term.App e1' e2' = .App e1 e2 :=
      ⟨τ1, hty, e1, hN1 n (by omega), e2, hN2 n (by omega), rfl⟩
    rw [SPMF.mem_support_iff_may]; unfold genTermSized; walk
    all_goals split <;> simp only [happ, or_true]
