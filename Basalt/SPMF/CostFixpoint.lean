/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt.SPMF.CostBound

/-!
# The `cost_fixpoint` Tactic

`cost_fixpoint` reduces a `.cost_bounded` law to one step of the generator: fixpoint induction over
the arguments its recursive calls change, then `cost_bound`.
-/

open Lean Meta Elab Tactic Lean.Order

namespace Basalt.CostFixpoint

open Basalt.Walk Basalt.CostBound

/-- `cost_fixpoint` proves `IsCostBounded (gen a₁ … aₙ) c` (or `IsBounded`, or
`SPMF.Cost.Always`) up to arithmetic. It inducts with `gen.fixpoint_induct` over the arguments some
recursive call of `gen` changes, unfolds one step, and runs `cost_bound` (extra cost bounds go in
`cost_fixpoint [h₁, h₂]`). In each residual goal the recursive function is named after `gen`, the
bound on its every call is `ih`, and the changing arguments keep their names. A `gen` that is not
recursive is unfolded and walked. -/
syntax (name := costFixpointTac) "cost_fixpoint" (" [" term,* "]")? : tactic

elab_rules : tactic
  | `(tactic| cost_fixpoint $[[$extras,*]]?) => withMainContext do
    let extras := (extras.map (·.getElems)).getD #[]
    let goal ← toAlways (← getMainGoal)
    goal.withContext do
    let ty ← instantiateMVars (← goal.getType)
    let #[_, x, post] := ty.getAppArgs | throwError "cost_fixpoint: internal error"
    let adm ← mkAppM ``SPMF.Cost.admissible_Always #[post]
    replaceMainGoal (← walkCost extras (← fixpointStep "cost_fixpoint" "cost_bound" x adm goal))

end Basalt.CostFixpoint
