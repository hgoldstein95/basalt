/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt.SPMF.ExpectBound

/-!
# The `expect_fixpoint` Tactic

`expect_fixpoint` reduces an upper bound on a recursive generator's expectation to one step of the
generator: fixpoint induction over the arguments its recursive calls change, admissible because
`SPMF.expect` is continuous, then `expect_bound`.
-/

open Lean Meta Elab Tactic Lean.Order

namespace Basalt.ExpectFixpoint

open Basalt.Walk Basalt.ExpectBound

/-- `expect_fixpoint` proves `SPMF.expect (gen a₁ … aₙ) f ≤ B`, at `SPMF` or `SPMF.Cost`, up to
arithmetic. It inducts with `gen.fixpoint_induct` over the arguments some recursive call of `gen`
changes, unfolds one step, and runs `expect_bound` (extra facts go in `expect_fixpoint [h₁, h₂]`).
The first goal is the arithmetic one; in it the recursive function is named after `gen`, the bound
on its every call is `ih`, and the changing arguments keep their names. Only an upper bound can be
proved this way. -/
syntax (name := expectFixpointTac) "expect_fixpoint" (" [" term,* "]")? : tactic

elab_rules : tactic
  | `(tactic| expect_fixpoint $[[$extras,*]]?) => withMainContext do
    let extras := (extras.map (·.getElems)).getD #[]
    let (x, f, B, goal) ← parseExpect "expect_fixpoint" (← getMainGoal)
    goal.withContext do
    let adm ← mkAppM ``SPMF.admissible_expect_le #[f, B]
    replaceMainGoal
      (← walkExpect extras (← fixpointStep "expect_fixpoint" "expect_bound" x adm goal))

end Basalt.ExpectFixpoint
