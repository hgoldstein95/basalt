/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt
import BasaltExamples.ArbNat

open RandomChoice ArbNat

/-!
# The `cost_bound` Contract

Pins what `cost_bound` leaves behind — one arithmetic goal per path through the generator, named
after it — the messages for a sub-generator nothing bounds, and that every combinator has a rule
for each judgment the walker proves.
-/

namespace CostBoundTest

/-- One branch per combinator that takes no generator argument. -/
def gen [Gen G] (b : Bool) : G Nat := do
  let x ← oneOf [
    fun () => pure 0,
    fun () => frequency [(1, fun () => chooseNat 0 3), (2, fun () => elements [4, 5])],
    fun () => if b then Nat.arbitrary else (·.down.val) <$> choose 0 1 (by simp)
  ]
  let y ← pick (fun () => pure 1) (fun () => chooseInt 0 2 >>= fun z => pure z.toNat)
  let c ← coin (1 / 3)
  if h : c then return x + y else return x

example (b : Bool) : IsCostBounded (gen b) (fun v => v + 6) := by
  unfold gen
  cost_bound
  all_goals omega

-- A drawn value is named after its binder, its cost `n_<value>`, and what is known about it
-- `h_<value>`: a pivot's range, a callee's cost law.
/--
trace: x : ℕ
h_x : 0 ≤ x ∧ x ≤ 3
y n_y : ℕ
h_y : n_y ≤ y + 1
⊢ 1 + (n_y + 0) ≤ x + y + 2
-/
#guard_msgs in
example : IsCostBounded (do let x ← chooseNat 0 3; let y ← Nat.arbitrary; return x + y)
    (fun v => v + 2) := by
  cost_bound
  trace_state
  omega

-- A combinator with a generator argument is bounded in terms of that generator's cost law.
/--
trace: xs : List ℕ
n_xs : ℕ
h_xs : n_xs ≤ xs.length + (List.map (fun n => n + 1) xs).sum + 1
⊢ n_xs + 0 ≤ xs.length + (List.map (fun x => x + 1) xs).sum + 1
-/
#guard_msgs in
example : IsCostBounded (listOf Nat.arbitrary >>= fun xs => pure xs)
    (fun xs => xs.length + (xs.map (· + 1)).sum + 1) := by
  cost_bound
  trace_state
  omega

example : IsCostBounded (vectorOf 2 Nat.arbitrary) (fun xs => (xs.map (· + 1)).sum) := by
  cost_bound; omega

example : IsCostBounded (listOfMaxLength 3 Nat.arbitrary) (fun xs => 1 + (xs.map (· + 1)).sum) := by
  cost_bound; omega

example : IsCostBounded (nonEmptyListOf Nat.arbitrary)
    (fun xs => xs.length + (xs.map (· + 1)).sum) := by
  cost_bound; omega

example : IsCostBounded (optionGen Nat.arbitrary) (fun o => 1 + o.elim 0 (· + 1)) := by
  cost_bound; omega

example : IsCostBounded (biasedOptionGen (1 / 4) Nat.arbitrary) (fun o => 1 + o.elim 0 (· + 1)) := by
  cost_bound; omega

/--
error: cost_bound: no rule, hypothesis, or `.cost_bounded` law bounds the cost of
  g
Tag a rule for it `@[gen_rule]`, or pass a cost bound to `cost_bound [_]`.
-/
#guard_msgs in
example (g : SPMF.Cost Nat) : IsCostBounded (g >>= fun _ => pure 0) (fun _ => 1) := by
  cost_bound

/--
error: cost_bound: no hypothesis or `.cost_bounded` law bounds the cost of the combinator argument
  g
Pass a cost bound for it to `cost_bound [_]`.
-/
#guard_msgs in
example (g : SPMF.Cost Nat) : IsCostBounded (listOf g) (fun _ => 1) := by
  cost_bound

-- A combinator term passed as a generator argument is bounded by its worst case.
/--
trace: xs : List ℕ
n_xs : ℕ
h_xs : n_xs ≤ (List.map (fun x => 1 + max 1 0) xs).sum
⊢ n_xs ≤ 2 * xs.length
-/
#guard_msgs in
example : IsCostBounded (vectorOf 3 (pick (fun _ => chooseNat 0 5) (fun _ => pure 0)))
    (fun xs => 2 * xs.length) := by
  cost_bound
  trace_state
  simp at *
  omega

example : IsCostBounded (listOfMaxLength 3 (chooseNat 0 5 >>= fun x => pure (x + 1)))
    (fun xs => 1 + xs.length) := by
  cost_bound
  simp at *
  omega

/-- A cost bound the caller supplies, here one that is no law of anything. -/
example : IsCostBounded (Nat.arbitrary >>= fun n => pure n) (fun n => n + 2) := by
  cost_bound [IsBounded_mono Nat.arbitrary.cost_bounded (c₂ := fun n => n + 2) (by omega)]
  omega

/-- A recursive occurrence is bounded by a hypothesis, at arguments computed from drawn values. -/
example (g : Int → Int → SPMF.Cost Nat) (ih : ∀ lo hi, IsBounded (g lo hi) fun n => n) (lo : Int) :
    IsCostBounded (chooseInt lo (lo + 3) >>= fun x => g lo (x - 1)) (fun n => n + 1) := by
  cost_bound
  omega

end CostBoundTest

-- Every combinator has a mass rule and a cost rule. The worst-case `IsBounded` rules exist only for
-- the combinators whose runs are bounded.
open Lean Elab Command Basalt.Walk in
run_cmd do
  let reg := genRuleExt.getState (← getEnv)
  let heads (j : Name) : NameSet :=
    ((reg.find? j).getD {}).foldl (fun s k _ => s.insert k) {}
  let mass := heads `SPMF.mass
  let cost := heads `SPMF.Cost.Always
  let missing (a b : NameSet) := a.toList.filter (!b.contains ·)
  unless (missing mass cost).isEmpty && (missing cost mass).isEmpty do
    throwError "gen_rule: combinators with a mass rule but no cost rule: {missing mass cost}; \
      with a cost rule but no mass rule: {missing cost mass}"
