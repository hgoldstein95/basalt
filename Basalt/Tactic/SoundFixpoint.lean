/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt.Tactic.Sound

/-!
# The `sound_fixpoint` Tactic

`sound_fixpoint` reduces a soundness law to one step of the generator: fixpoint induction over the
arguments its recursive calls change, admissible because support is continuous, then `sound_bound`.
-/

open Lean Meta Elab Tactic

namespace Basalt.SoundFixpoint

open Basalt.Walk Basalt.SoundBound

/-- `sound_fixpoint` proves `IsSound (gen a₁ … aₙ) P` up to what `P` says. It inducts with
`gen.fixpoint_induct` over the arguments some recursive call of `gen` changes, unfolds one step, and
runs `sound_bound` (extra facts go in `sound_fixpoint [h₁, h₂]`). In each residual goal the
recursive function is named after `gen`, the soundness of its every call is `ih`, and the changing
arguments keep their names. A `gen` that is not recursive is unfolded and walked. -/
syntax (name := soundFixpointTac) "sound_fixpoint" (" [" term,* "]")? : tactic

elab_rules : tactic
  | `(tactic| sound_fixpoint $[[$extras,*]]?) => withMainContext do
    let extras := (extras.map (·.getElems)).getD #[]
    let goal ← getMainGoal
    let ty ← whnfR (← instantiateMVars (← goal.getType))
    -- Any other goal is `sound_bound`'s to reject.
    unless ty.isAppOfArity ``IsSound 3 do
      replaceMainGoal (← walkSound extras goal)
      return
    let adm ← mkAppM ``SPMF.admissible_isSound #[ty.getArg! 2]
    replaceMainGoal
      (← walkSound extras (← fixpointStep "sound_fixpoint" "sound_bound" (ty.getArg! 1) adm goal))

end Basalt.SoundFixpoint
