/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt

/-!
# Facts about the combinators

Concrete `frequency` branch probabilities, computed with `SPMF.frequency_apply` and friends and
pinned here as regression tests, a check that `oneOf`, and the deprecated `pick` defined by it, work
under `partial_fixpoint`, and the contract of `oneOf!`/`frequency!`: no list in the compiled code,
and nothing a proof can tell apart from `oneOf`/`frequency`.
-/

open NNReal ENNReal

namespace FrequencyExamples

open SPMF

example : (frequency [(1, fun _ => Pure.pure 0), (3, fun _ => Pure.pure 1)]
    (by simp) : SPMF Nat) 1 = 3 / 4 := by
  simp

-- Duplicate branches contribute separately: `frequency_apply`'s sums are `List.sum`s, and
-- a `Finset` sum would collapse these two branches and halve the probability.
example : (frequency [(1, fun _ => Pure.pure 0), (1, fun _ => Pure.pure 0)]
    (by simp) : SPMF Nat) 0 = 1 := by
  simp
  rw [one_add_one_eq_two, ENNReal.div_self (by norm_num) (by norm_num)]

-- Equal weights are genuinely uniform.
example : (frequency [(1, fun _ => Pure.pure 0), (1, fun _ => Pure.pure 1),
    (1, fun _ => Pure.pure 2), (1, fun _ => Pure.pure 3)]
    (by simp) : SPMF Nat) 2 = 1 / 4 := by
  simp

example : IsAlmostSurelyTerminating
    (frequency [(2, fun _ => Pure.pure true), (3, fun _ => Pure.pure false)] (by simp)
      : SPMF Bool) := by
  rw [IsAlmostSurelyTerminating.iff_obs]
  walk
  norm_num [ENNReal.div_self]

end FrequencyExamples

-- A tagged sum type `Nat + Float`
inductive NatOrFloat
  | Nat (n : Nat)
  | Float (f : Float)
deriving Repr

-- Generates either a `Nat` or a `Float` that's either 1,
-- a multiple of 2, or a multiple of 3
-- (This generator tests that we can use `oneOf` in functions marked as `partial_fixpoint`)
def myGen [Gen G] : G NatOrFloat :=
  oneOf [
    fun _ => oneOf
      [fun _ => pure (NatOrFloat.Nat 1),
       fun _ => pure (NatOrFloat.Float 1.0)],
    fun _ => do
      let natOrFloat ← myGen
      match natOrFloat with
      | .Nat n => pure (.Nat (n * 2))
      | .Float f => pure (.Float (f * 2)),
    fun _ => do
      let natOrFloat ← myGen
      match natOrFloat with
      | .Nat n => pure (.Nat (n * 3))
      | .Float f => pure (.Float (f * 3))

  ] (by simp)
partial_fixpoint

#guard_msgs(drop info) in
#eval (for _ in [0:10] do
  IO.println <| repr (← myGen) : IO Unit)

-- Sample `permutationOf`: each draw should be a permutation of `[1, 2, 3, 4, 5]`.
#guard_msgs(drop info) in
#eval (for _ in [0:10] do
  IO.println <| repr (← permutationOf [1, 2, 3, 4, 5]).val : IO Unit)

/-! The deprecated `pick` is `oneOf` of two branches: a recursive generator using it still
elaborates as a `partial_fixpoint`, and the walker proves its laws through `oneOf`. -/

namespace DeprecatedPick

set_option linter.deprecated false

open RandomChoice in
def natGen [Gen G] : G Nat :=
  pick (fun _ => pure 0) (fun _ => do let n ← natGen; pure (n + 1))
partial_fixpoint

theorem natGen.cost_bounded : IsCostBounded natGen (fun n => n + 1) := by
  rw [IsCostBounded.iff_obs]
  walk fixpoint
  all_goals omega

end DeprecatedPick

/-! ## Compiled choice -/

namespace CompiledChoice

open Lean Elab Command Term Meta in
/-- `#same_walk tac on a and b` fails unless `tac` leaves the same goals on `a` as on `b`. -/
elab "#same_walk " tac:tactic " on " a:term " and " b:term : command => liftTermElabM do
  let run (stx : Term) : TermElabM String := do
    let ty ← elabType stx
    synthesizeSyntheticMVarsNoPostponing
    let gs ← Tactic.run (← mkFreshExprMVar ty).mvarId! (Tactic.evalTactic tac)
    return toString (← gs.mapM fun g => return (← Meta.ppGoal g).pretty)
  let (ra, rb) := (← run a, ← run b)
  unless ra == rb do throwError "the walks differ:{indentD ra}\nand{indentD rb}"

#same_walk (rw [IsSoundFor.iff_obs]; walk)
  on IsSoundFor (oneOf [fun _ => pure 0, fun _ => chooseNat 1 3] : SPMF Nat) (· ≤ 3)
  and IsSoundFor (oneOf! [fun _ => pure 0, fun _ => chooseNat 1 3] : SPMF Nat) (· ≤ 3)

#same_walk (rw [IsCompleteFor.iff_obs]; intro _ _; walk)
  on IsCompleteFor (oneOf [fun _ => pure 0, fun _ => chooseNat 1 3] : SPMF Nat) (· ≤ 3)
  and IsCompleteFor (oneOf! [fun _ => pure 0, fun _ => chooseNat 1 3] : SPMF Nat) (· ≤ 3)

#same_walk (rw [IsCostBounded.iff_obs]; walk)
  on IsCostBounded (oneOf [fun _ => pure 0, fun _ => chooseNat 1 3]) (fun _ => 2)
  and IsCostBounded (oneOf! [fun _ => pure 0, fun _ => chooseNat 1 3]) (fun _ => 2)

#same_walk (rw [SPMF.expect_eq_obs]; walk)
  on SPMF.expect (oneOf [fun _ => pure 0, fun _ => chooseNat 1 3] : SPMF Nat)
    (fun n => (n : ℝ≥0∞)) ≤ ⊤
  and SPMF.expect (oneOf! [fun _ => pure 0, fun _ => chooseNat 1 3] : SPMF Nat)
    (fun n => (n : ℝ≥0∞)) ≤ ⊤

#same_walk (rw [IsSoundFor.iff_obs]; walk)
  on IsSoundFor (frequency [(1, fun _ => pure 0), (2, fun _ => chooseNat 1 3)] : SPMF Nat) (· ≤ 3)
  and IsSoundFor (frequency! [(1, fun _ => pure 0), (2, fun _ => chooseNat 1 3)] : SPMF Nat) (· ≤ 3)

#same_walk (rw [IsCompleteFor.iff_obs]; intro _ _; walk)
  on IsCompleteFor (frequency [(1, fun _ => pure 0), (2, fun _ => chooseNat 1 3)] : SPMF Nat)
    (· ≤ 3)
  and IsCompleteFor (frequency! [(1, fun _ => pure 0), (2, fun _ => chooseNat 1 3)] : SPMF Nat)
    (· ≤ 3)

#same_walk (rw [IsCostBounded.iff_obs]; walk)
  on IsCostBounded (frequency [(1, fun _ => pure 0), (2, fun _ => chooseNat 1 3)]) (fun _ => 2)
  and IsCostBounded (frequency! [(1, fun _ => pure 0), (2, fun _ => chooseNat 1 3)]) (fun _ => 2)

#same_walk (rw [SPMF.expect_eq_obs]; walk)
  on SPMF.expect (frequency [(1, fun _ => pure 0), (2, fun _ => chooseNat 1 3)] : SPMF Nat)
    (fun n => (n : ℝ≥0∞)) ≤ ⊤
  and SPMF.expect (frequency! [(1, fun _ => pure 0), (2, fun _ => chooseNat 1 3)] : SPMF Nat)
    (fun n => (n : ℝ≥0∞)) ≤ ⊤

/-- `simp` sees the model. -/
example : (frequency! [(1, fun _ => Pure.pure 0), (3, fun _ => Pure.pure 1)] : SPMF Nat) 1
    = 3 / 4 := by
  simp

-- Goals show the source form.
/-- info: oneOf! [fun x => pure 0, fun x => pure 1] : SPMF ℕ -/
#guard_msgs in
#check (oneOf! [fun _ => pure 0, fun _ => pure 1] : SPMF Nat)

/-- Weights that are not literals are summed as `frequencyChain` unfolds them. -/
def weighted [Gen G] (b : Nat) : G Nat :=
  frequency! [(1, fun _ => pure 0), (b, fun _ => pure 1), (b + 2, fun _ => pure 2)]
    (by simp)

def plain [Gen G] : G Nat := oneOf [fun _ => pure 0, fun _ => pure 1, fun _ => pure 2]

def compiled [Gen G] : G Nat := oneOf! [fun _ => pure 0, fun _ => pure 1, fun _ => pure 2]

def compiledWeighted [Gen G] : G Nat :=
  frequency! [(1, fun _ => pure 0), (2, fun _ => oneOf! [fun _ => pure 1, fun _ => pure 2])]

/-- A recursive body under `oneOf!` is monotone through `monotone_oneOfWith`. -/
def compiledRec [Gen G] : G Nat :=
  oneOf! [fun _ => pure 0, fun _ => do let n ← compiledRec; pure (n + 1)]
partial_fixpoint

-- The compiled code of a compiled choice builds no list and calls no combinator; `plain` is the
-- control that the check can see one.
open Lean in
run_cmd do
  let env ← getEnv
  let code (n : Name) : String :=
    (IR.getDecls env).filter (n.isPrefixOf ·.name) |>.foldl (fun acc d => acc ++ toString (format d)) ""
  unless ((code ``plain).splitOn "List.cons").length > 1 do
    throwError "the check cannot see `plain`'s list"
  for n in [``compiled, ``compiledWeighted, ``weighted, ``compiledRec] do
    for c in ["List.cons", "oneOf", "frequency"] do
      unless ((code n).splitOn c).length == 1 do
        throwError "`{n}`'s compiled code mentions `{c}`"

end CompiledChoice
