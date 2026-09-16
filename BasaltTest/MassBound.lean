/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt
import BasaltExamples.ArbNat

open RandomChoice ArbNat ENNReal

/-!
# The `mass_bound` Contract

Pins what `mass_bound` leaves behind: a bound whose shape mirrors the generator's, built from one
`@[mass_bound]` rule per combinator, and the message for a combinator that has no rule.
-/

namespace MassBoundTest

/-- One branch per combinator the library has a rule for. `Nat.arbitrary` is a callee, not a
combinator: the tactic finds its `.terminates` law by name. -/
def gen [Gen G] (b : Bool) : G Nat := do
  let x ← oneOf [
    fun () => pure 0,
    fun () => frequency [(1, fun () => chooseNat 0 3), (2, fun () => elements [4, 5])],
    fun () => if b then Nat.arbitrary else (·.down.val) <$> choose 0 1 (by simp)
  ]
  let y ← pick (fun () => pure 1) (fun () => chooseInt 0 2 >>= fun z => pure z.toNat)
  return x + y

-- The residual goal is pure `ℝ≥0∞` arithmetic in the shape of the do-block: `oneOf`'s average over
-- three branches, one of them `frequency`'s weighted average, times `pick`'s.
/--
trace: b : Bool
⊢ 0 ≤
    [1, (List.map (fun p => ↑p.1 * p.2) [(1, 1), (2, 1)]).sum / ↑(List.map Prod.fst [(1, 1), (2, 1)]).sum,
            min 1 1].sum /
        ↑[1, (List.map (fun p => ↑p.1 * p.2) [(1, 1), (2, 1)]).sum / ↑(List.map Prod.fst [(1, 1), (2, 1)]).sum,
              min 1 1].length *
      ((1 / 2 * 1 + 1 / 2 * (1 * 1)) * 1)
-/
#guard_msgs in
example (b : Bool) : (0 : ℝ≥0∞) ≤ (gen b : SPMF Nat).mass := by
  unfold gen
  mass_bound
  trace_state
  exact zero_le

/--
error: mass_bound: no rule, hypothesis, or `.terminates` law bounds the mass of
  g
Tag a lower bound for it `@[mass_bound]`, or pass one to `mass_bound [_]`.
-/
#guard_msgs in
example (g : SPMF Nat) : (1 : ℝ≥0∞) ≤ (g >>= fun _ => pure 0).mass := by
  mass_bound

/-- The same generator, bounded by a fact the caller supplies instead. -/
example (g : SPMF Nat) (hg : SPMF.IsPMF g) : (1 : ℝ≥0∞) ≤ (g >>= fun _ => pure 0).mass := by
  mass_bound [hg]
  norm_num

end MassBoundTest
