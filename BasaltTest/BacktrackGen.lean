/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Segev Elazar Mittelman
-/
import Basalt

/-!
# Backtracking Generators

`backtrack`'s verdict on failure depends only on how its branches fail, not on the draws, so each pin
runs it repeatedly and prints the distinct outcomes; a second outcome would show a draw leaking into
the verdict. Also pins that `BacktrackGen` is a `Gen` a `partial_fixpoint` can recurse in.
-/

open BacktrackGen

/-- The distinct outcomes of `n` runs at `Plausible.Gen`. -/
def outcomes (g : BacktrackGen Plausible.Gen Nat) (n : Nat := 20) : IO (List (Outcome Nat)) := do
  let mut seen : List (Outcome Nat) := []
  for _ in [0:n] do
    let o ← Plausible.Gen.run g.run 10
    if !seen.contains o then seen := seen ++ [o]
  return seen

-- Every branch refuted: the whole is refuted.
/-- info: [Outcome.refuted] -/
#guard_msgs in
#eval outcomes (backtrack [(1, fun _ => refute), (3, fun _ => refute)])

-- One branch ran out of budget: the whole is only `exhausted`, whichever order they were tried in.
/-- info: [Outcome.exhausted] -/
#guard_msgs in
#eval outcomes (backtrack [(1, fun _ => refute), (1, fun _ => exhaust), (1, fun _ => refute)])

-- A success is found whichever branch is drawn first: failed branches are dropped and retried.
/-- info: [Outcome.ok 7] -/
#guard_msgs in
#eval outcomes (backtrack [(5, fun _ => refute), (1, fun _ => pure 7), (5, fun _ => exhaust)])

-- A weight-0 branch is never drawn, so its success is never found — and since it was not tried, the
-- failure of the rest does not refute the whole.
/-- info: [Outcome.exhausted] -/
#guard_msgs in
#eval outcomes (backtrack [(0, fun _ => pure 1), (1, fun _ => refute)])

-- No branches at all: nothing applies.
/-- info: [Outcome.refuted] -/
#guard_msgs in
#eval outcomes (backtrack [])

-- `refutedToExhausted` downgrades only the refutation.
/-- info: ([Outcome.exhausted], [Outcome.ok 2]) -/
#guard_msgs in
#eval do return (← outcomes (refutedToExhausted refute), ← outcomes (refutedToExhausted (pure 2)))

/-! ## `BacktrackGen` is a `Gen` -/

/-- A backtracking generator defined by `partial_fixpoint`, using a Basalt combinator inside. -/
def geomUntil [Gen G] (bound : Nat) : BacktrackGen G Nat := do
  let n ← oneOf [fun () => pure 0, fun () => do let m ← geomUntil bound; pure (m + 1)]
  if n ≤ bound then pure n else refute
partial_fixpoint

-- Every success respects the bound, and runs that exceed it fail rather than return.
/-- info: true -/
#guard_msgs in
#eval do
  let os ← outcomes (geomUntil 2) 200
  return os.all fun o => match o with | .ok n => n ≤ 2 | .refuted => true | .exhausted => false

/-! ## At `Plausible.Gen` -/

-- The failures stay distinguishable after conversion.
/-- info: ["Generation failure:Generation failure.", "Generation failure:out of fuel"] -/
#guard_msgs in
#eval do
  let msg := fun (g : BacktrackGen Plausible.Gen Nat) => do
    try discard <| Plausible.Gen.run g.toPlausibleGen 10; return "no error"
    catch e => return e.toString
  return [← msg refute, ← msg exhaust]
