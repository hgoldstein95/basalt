/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt

/-!
# The `match` Congruence Contract

Pins how the walk enters a `match` (`Basalt/Walk/Match.lean`): the lemma it generates for a matcher,
the bound it makes a `match` in each algebra, the cases a residual `match` is split into, and the
`match` it does not enter.
-/

open RandomChoice

namespace MatchCongrTest

/-! The lemma, generated for a matcher the first time a walk meets it. -/

def pred (n : Nat) : Nat := match n with | 0 => 0 | k + 1 => k

/--
info: [uα, uβ]
∀ {α : Sort uα} {β : Sort uβ} {R : α → β → Prop} (n : ℕ) {alt_1 : Unit → α} {alt_2 : ℕ → α} {c_1 : Unit → β}
  {c_2 : ℕ → β},
  (n = 0 → R (alt_1 ()) (c_1 ())) →
    (∀ (k : ℕ), n = k.succ → R (alt_2 k) (c_2 k)) →
      R
        (match n with
        | 0 => alt_1 ()
        | k.succ => alt_2 k)
        (match n with
        | 0 => c_1 ()
        | k.succ => c_2 k)
-/
#guard_msgs in
set_option linter.auxLemma false in
open Lean Meta in
run_meta do
  let some n ← Basalt.Walk.congrLemma? ``pred.match_1 | throwError "no lemma"
  logInfo m!"{(← getConstInfo n).levelParams}\n{(← getConstInfo n).type}"

/-! A `match` on a drawn value: the precondition is a `match`, split into one goal per case with
the drawn value replaced by its pattern. -/

def genPred [Gen G] : G Nat := do
  let n ← chooseNat 0 3
  match n with
  | 0 => pure 0
  | k + 1 => pure k

/--
trace: h_n✝ : 0 ≤ 0 ∧ 0 ≤ 3
⊢ 0 ≤ 2

k✝ : ℕ
h_n✝ : 0 ≤ k✝.succ ∧ k✝.succ ≤ 3
⊢ k✝ ≤ 2
-/
#guard_msgs in
example : IsSoundFor (genPred : SPMF Nat) (· ≤ 2) := by
  rw [IsSoundFor.iff_obs]
  walk
  trace_state
  all_goals omega

/-! In the angelic algebra the `match` stays in the precondition, under the draw's `∃`. -/

/--
trace: ⊢ ∃ n,
    (0 ≤ n ∧ n ≤ 3) ∧
      match n with
      | 0 => False
      | k.succ => k = 2
-/
#guard_msgs in
example : 2 ∈ SPMF.support (genPred : SPMF Nat) := by
  rw [SPMF.mem_support_iff_may]
  walk
  trace_state
  exact ⟨3, by decide, rfl⟩

/-! One on something in the context is split, each case pruned: the `0` case is closed. -/

def genPredOf [Gen G] (n : Nat) : G Nat :=
  match n with
  | 0 => pure 0
  | k + 1 => pure k

/--
trace: k✝ : ℕ
⊢ k✝ = k✝.succ - 1
-/
#guard_msgs in
example (n : Nat) : n - 1 ∈ SPMF.support (genPredOf n : SPMF Nat) := by
  rw [SPMF.mem_support_iff_may]
  walk
  trace_state
  all_goals omega

/-! In the average algebra it stays in the bound, under the draw's sum. -/

/--
trace: ⊢ (∑ x ∈ Finset.Icc 0 3,
        match x with
        | 0 => ↑0
        | k.succ => ↑k) /
      ↑(3 - 0 + 1) ≤
    2
-/
#guard_msgs in
example : SPMF.expect (genPred : SPMF Nat) (fun n => n) ≤ 2 := by
  rw [SPMF.expect_eq_obs]
  walk
  trace_state
  simp [Finset.sum_Icc_succ_top]
  ennreal_to_real
  norm_num

/-! Overlapping patterns: a later alternative knows the earlier ones did not match. -/

def genOverlap [Gen G] : G Nat := do
  let a ← chooseNat 0 3
  let b ← chooseNat 0 3
  match a, b with
  | 0, _ => pure 0
  | _, 0 => pure 1
  | x + 1, y + 1 => pure (x + y)

/--
trace: b✝ : ℕ
h_b✝ : 0 ≤ b✝ ∧ b✝ ≤ 3
h_a✝ : 0 ≤ 0 ∧ 0 ≤ 3
⊢ 1 + 1 ≤ 0 + 2

a✝ : ℕ
h_a✝ : 0 ≤ a✝ ∧ a✝ ≤ 3
x✝ : a✝ = 0 → False
h_b✝ : 0 ≤ 0 ∧ 0 ≤ 3
⊢ 1 + 1 ≤ 1 + 2

x✝ y✝ : ℕ
h_a✝ : 0 ≤ x✝.succ ∧ x✝.succ ≤ 3
h_b✝ : 0 ≤ y✝.succ ∧ y✝.succ ≤ 3
⊢ 1 + 1 ≤ x✝ + y✝ + 2
-/
#guard_msgs in
example : IsCostBounded (genOverlap : SPMF.Cost Nat) (fun v => v + 2) := by
  rw [IsCostBounded.iff_obs]
  walk
  trace_state
  all_goals omega

/-! `match h :`, whose alternatives take the discriminant's equation. -/

def genSub [Gen G] : G Nat := do
  let n ← chooseNat 0 3
  match h : n with
  | 0 => pure 0
  | _ + 1 => pure (n - 1)

/--
trace: h_n✝ : 0 ≤ 0 ∧ 0 ≤ 3
⊢ 0 ≤ 2

n✝ : ℕ
h_n✝ : 0 ≤ n✝.succ ∧ n✝.succ ≤ 3
⊢ n✝.succ - 1 ≤ 2
-/
#guard_msgs in
example : IsSoundFor (genSub : SPMF Nat) (· ≤ 2) := by
  rw [IsSoundFor.iff_obs]
  walk
  trace_state
  all_goals omega

/-! A nested pattern on a value a draw built: `split` relates the value to the pattern by an
equation, which is solved (`some b = some (k + 1)` to `b = k + 1`, `some b = none` to no case). -/

def genFuel [Gen G] (n : Nat) : G Nat := do
  let o ← oneOf! [fun _ => pure none, fun _ => some <$> chooseNat 0 n]
  match o with
  | none => pure 0
  | some 0 => pure 0
  | some (k + 1) => genFuel k
partial_fixpoint

/--
trace: genFuel : ℕ → SPMF ℕ
ih : ∀ (n : ℕ), SPMF.alwaysObs.spec (genFuel n) fun x => x ≤ n
n : ℕ
⊢ 0 ≤ n

genFuel : ℕ → SPMF ℕ
ih : ∀ (n : ℕ), SPMF.alwaysObs.spec (genFuel n) fun x => x ≤ n
n : ℕ
h_o✝ : 0 ≤ 0 ∧ 0 ≤ n
⊢ 0 ≤ n

genFuel : ℕ → SPMF ℕ
ih : ∀ (n : ℕ), SPMF.alwaysObs.spec (genFuel n) fun x => x ≤ n
n k✝ : ℕ
h_o✝ : 0 ≤ k✝.succ ∧ k✝.succ ≤ n
x✝ : ℕ
h_x✝ : x✝ ≤ k✝
⊢ x✝ ≤ n
-/
#guard_msgs in
example : IsSoundFor (genFuel n) (· ≤ n) := by
  rw [IsSoundFor.iff_obs]
  walk fixpoint
  trace_state
  all_goals omega

/-! A relation: both sides are the same `match`. -/

theorem genPred.terminates : IsAlmostSurelyTerminating genPred := by
  rw [IsAlmostSurelyTerminating.iff_obs, genPred]
  walk
  norm_num [ENNReal.div_self]

example : IsFaithful genPred := by
  faithful_fixpoint [genPred.terminates]

/-! A `match` applied to something further is not entered. -/

def genApplied [Gen G] : G Nat := do
  let b ← chooseNat 0 1
  (match b with | 0 => fun x => pure x | _ => fun x => pure (x + 1)) 5

/--
error: the walk does not enter this `match`:
  (match (motive := ℕ → ℕ → SPMF ℕ) b with
    | 0 => fun x => pure x
    | _unfolded => fun x => pure (x + 1))
    5
It enters one whose type does not depend on its discriminants, that is applied to nothing further, and, on a relation, whose counterpart is the same `match`.
(in the unfolding of `MatchCongrTest.genApplied`)
-/
#guard_msgs in
example : IsSoundFor (genApplied : SPMF Nat) (· ≤ 6) := by
  rw [IsSoundFor.iff_obs]
  walk

end MatchCongrTest
