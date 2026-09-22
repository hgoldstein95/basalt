/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt
import BasaltExamples.ArbChar
import BasaltExamples.ArbNat
import BasaltTest.OptionGen

/-!
# The `cost_bound` Contract

Pins what `cost_bound` leaves behind — one arithmetic goal per path through the generator, named
after it — and the messages for a sub-generator nothing bounds.
-/

open RandomChoice ArbNat ArbChar

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
⊢ 1 + n_y ≤ x + y + 2
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

example : IsCostBounded (permutationOf [1, 2, 3] : SPMF.Cost { ys // [1, 2, 3].Perm ys })
    (fun _ => 3) := by
  cost_bound
  simp at *
  omega

-- A definition with no rule is unfolded and walked through: one goal per path through its body, the
-- draws it names under its names, and those it does not under the goal's.
/--
trace: x n_x : ℕ
h_x : n_x ≤ x + 1
⊢ 1 + n_x ≤ 1 + (some x).elim 0 fun x => x + 1

⊢ 1 ≤ 1 + none.elim 0 fun x => x + 1
-/
#guard_msgs in
example : IsCostBounded (optionGen Nat.arbitrary) (fun o => 1 + o.elim 0 (· + 1)) := by
  cost_bound
  trace_state
  all_goals simp only [Option.elim]; omega

example : IsCostBounded (biasedOptionGen (1 / 4) Nat.arbitrary) (fun o => 1 + o.elim 0 (· + 1)) := by
  cost_bound
  all_goals simp only [Option.elim]; omega

/-- A helper with no law. -/
def twoDigits [Gen G] : G (Nat × Nat) := do
  let d₁ ← chooseNat 0 9
  let d₂ ← chooseNat 0 9
  return (d₁, d₂)

/--
trace: d₁ : ℕ
h_d₁ : 0 ≤ d₁ ∧ d₁ ≤ 9
d₂ : ℕ
h_d₂ : 0 ≤ d₂ ∧ d₂ ≤ 9
⊢ 1 + 1 ≤ 2
-/
#guard_msgs in
example : IsCostBounded (twoDigits >>= fun p => pure (p.1 + p.2)) (fun _ => 2) := by
  cost_bound
  trace_state
  omega

/--
error: no rule, `@[gen_map]` lemma, hypothesis, or law bounds
  g
Pass a fact about it to the tactic.
-/
#guard_msgs in
example (g : SPMF.Cost Nat) : IsCostBounded (g >>= fun _ => pure 0) (fun _ => 1) := by
  cost_bound

/-- A helper whose body draws from its argument. -/
def twice [Gen G] (g : G Nat) : G Nat := do
  let a ← g
  let b ← g
  return a + b

/--
error: no rule, `@[gen_map]` lemma, hypothesis, or law bounds
  g
Pass a fact about it to the tactic.
(in the unfolding of `CostBoundTest.twice`)
-/
#guard_msgs in
example (g : SPMF.Cost Nat) : IsCostBounded (twice g) (fun _ => 1) := by
  cost_bound

/--
error: no rule, `@[gen_map]` lemma, hypothesis, or law bounds
  g
Pass a fact about it to the tactic.
-/
#guard_msgs in
example (g : SPMF.Cost Nat) : IsCostBounded (listOf g) (fun _ => 1) := by
  cost_bound

-- A combinator term passed as a generator argument is bounded by its worst case.
/--
trace: xs : List ℕ
n_xs : ℕ
h_xs : n_xs ≤ (List.map (fun x => max (1 + 1) (1 + 0)) xs).sum
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

-- The worst case of a list combinator is the largest of its branches', a callee's included.
/--
trace: xs : List ℕ
n_xs : ℕ
h_xs : n_xs ≤ (List.map (fun x => max (1 + 1) (max (1 + 0) 0)) xs).sum
⊢ n_xs ≤ 2 * xs.length
-/
#guard_msgs in
example : IsCostBounded
    (vectorOf 3 (oneOf [fun _ => chooseNat 0 5, fun _ => pure 0] (by simp)))
    (fun xs => 2 * xs.length) := by
  cost_bound
  trace_state
  simp at *
  omega

example : IsCostBounded
    (vectorOf 3 (frequency [(1, fun _ => Char.arbitrary), (2, fun _ => pure 'a')] (by simp)))
    (fun xs => 2 * xs.length) := by
  cost_bound
  simp at *
  omega

example : IsCostBounded
    (vectorOf 2 (permutationOf [1, 2, 3]) : SPMF.Cost (List { ys // [1, 2, 3].Perm ys }))
    (fun xs => 3 * xs.length) := by
  cost_bound
  simp at *
  omega

/-- A cost bound the caller supplies for a combinator term is used when its rule fails. -/
example (g : SPMF.Cost Nat) (h : IsBounded (listOf g) fun _ => 5) :
    IsCostBounded (listOf g >>= fun xs => pure xs) (fun _ => 5) := by
  cost_bound [h]
  omega

example (g : SPMF.Cost Nat) (h : IsBounded (listOf g) fun _ => 5) :
    IsCostBounded (listOf g) (fun _ => 5) := by
  cost_bound
  omega

/-- A postcondition over a relation with `nil` and `cons` constructors is left as it is. -/
example : SPMF.Cost.Always (pure [1, 2] : SPMF.Cost (List Nat)) (fun xs _ => xs.Perm [2, 1]) := by
  cost_bound
  exact List.Perm.swap 2 1 []

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
