/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt
import BasaltExamples.ArbNat
import BasaltExamples.SortedList

open RandomChoice ArbNat ENNReal

/-!
# The `mass_bound` Contract

Pins what `mass_bound` leaves behind: a bound whose shape mirrors the generator's, built from one
`@[gen_rule]` rule per combinator, and the message for a combinator that has no rule.
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
-- three branches, one of them `frequency`'s weighted average and one a conditional, times `pick`'s.
/--
trace: b : Bool
⊢ 0 ≤
    [1, (List.map (fun p => ↑p.1 * p.2) [(1, 1), (2, 1)]).sum / ↑(List.map Prod.fst [(1, 1), (2, 1)]).sum,
            if b = true then 1 else 1].sum /
        ↑[1, (List.map (fun p => ↑p.1 * p.2) [(1, 1), (2, 1)]).sum / ↑(List.map Prod.fst [(1, 1), (2, 1)]).sum,
              if b = true then 1 else 1].length *
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
Tag a lower bound for it `@[gen_rule]`, or pass one to `mass_bound [_]`.
-/
#guard_msgs in
example (g : SPMF Nat) : (1 : ℝ≥0∞) ≤ (g >>= fun _ => pure 0).mass := by
  mass_bound

/-- The same generator, bounded by a fact the caller supplies instead. -/
example (g : SPMF Nat) (hg : SPMF.IsPMF g) : (1 : ℝ≥0∞) ≤ (g >>= fun _ => pure 0).mass := by
  mass_bound [hg]
  norm_num

-- An unbounded-length list combinator only passes termination through: its bound is `1` exactly
-- when its element generator's is.
/--
trace: ⊢ 1 ≤ if 1 ≤ 1 then 1 else 0
-/
#guard_msgs in
example : (1 : ℝ≥0∞) ≤ (listOf Nat.arbitrary : SPMF (List Nat)).mass := by
  mass_bound
  trace_state
  simp

/-- A recursive bound over a tupled seed, the form a family criterion hands over, closes calls whose
arguments are projections of another seed. -/
example (g : Int → Int → SPMF Nat) (c : ℝ≥0∞)
    (hrec : ∀ j : Int × Int, c ≤ ((fun p : Int × Int => g p.1 p.2) j).mass) (p : Int × Int) :
    c * c ≤ (g p.1 (p.2 - 1) >>= fun _ => g 0 p.2).mass := by
  mass_bound
  exact le_rfl

/-- The same over the `Unit` seed of a single generator. -/
example (g : SPMF Nat) (c : ℝ≥0∞) (hrec : ∀ _ : Unit, c ≤ g.mass) :
    c ≤ (g >>= fun x => pure (x + 1)).mass := by
  mass_bound
  simp

/-- A callee whose `.terminates` law takes an argument is found by name too. -/
example : (1 : ℝ≥0∞) ≤
    ((Nat.arbitrary >>= SortedList.List.genSortedGt : SPMF (List Nat))).mass := by
  mass_bound
  simp

-- A later rule for the same combinator is a fallback. A conditional on a drawn value cannot stay a
-- conditional in a bound outside the draw, so it falls back to the `min` of its branches.
/--
trace: ⊢ 1 ≤ 1 * min 1 1
-/
#guard_msgs in
example : (1 : ℝ≥0∞) ≤
    (chooseNat 0 1 >>= fun x => if x = 0 then pure 0 else pure 1 : SPMF Nat).mass := by
  mass_bound
  trace_state
  simp

-- A continuation whose bound depends on the drawn pivot, as a recursive call on a seed computed from
-- it does, falls back to the average over the range.
/--
trace: g : ℕ → SPMF ℕ
c : ℕ → ℝ≥0∞
hrec : ∀ (j : ℕ), c j ≤ (g j).mass
n : ℕ
⊢ 0 ≤ (∑ x ∈ Finset.Icc 0 n, c x) / ↑(n - 0 + 1)
-/
#guard_msgs in
example (g : Nat → SPMF Nat) (c : Nat → ℝ≥0∞) (hrec : ∀ j, c j ≤ (g j).mass) (n : Nat) :
    0 ≤ (chooseNat 0 n (by omega) >>= g).mass := by
  mass_bound
  trace_state
  exact zero_le

-- A continuation whose bound depends on a value drawn from anything else falls back to the worst
-- case over every value.
/--
trace: ⊢ 1 ≤ 1 * ⨅ x, 1 ^ x
-/
#guard_msgs in
example : (1 : ℝ≥0∞) ≤
    (elements [1, 2] (by simp) >>= fun k => vectorOf k (pure 0) : SPMF (List Nat)).mass := by
  mass_bound
  trace_state
  simp

/-- A drawn value is named after its binder, so a fact passed for a sub-generator can mention it. -/
example (g : Nat → SPMF Nat) (h : ∀ k, k ≤ 3 → 1 ≤ (g k).mass) :
    (1 : ℝ≥0∞) ≤ (ULift.down <$> choose 0 3 (by omega) >>= fun k => g k.1 : SPMF Nat).mass := by
  mass_bound [h k.1 k.2.2]
  simp

/-- A fact over a subtype is matched through the value alone. -/
example (g : Nat → SPMF Nat) (h : ∀ k : {k // 0 ≤ k ∧ k ≤ 3}, 1 ≤ (g k.1).mass) :
    (1 : ℝ≥0∞) ≤ (ULift.down <$> choose 0 3 (by omega) >>= fun k => g k.1 : SPMF Nat).mass := by
  mass_bound
  simp

/-- A fact's premise that its use does not determine is found among the hypotheses. -/
example (b : Bool) (g : SPMF Nat) (h : b = true → 1 ≤ g.mass) :
    (1 : ℝ≥0∞) ≤ (if b = true then g else pure 0 : SPMF Nat).mass := by
  mass_bound
  simp

/-- A generator over a long literal alphabet, and one that calls it. -/
def longChars : List Char :=
  (List.range 32).map (fun i => Char.ofNat (i + 32)) ++ (List.range 96).map (fun i => Char.ofNat (i + 128))

def genLongChar [Gen G] : G Char := elements longChars (by simp [longChars])

theorem genLongChar.terminates : IsAlmostSurelyTerminating (genLongChar : SPMF Char) := by
  mass_fixpoint using SPMF.LfpIsOne.one
  simp

def genLongText [Gen G] (n : Nat) : G (List Char) := listOfMaxLength n genLongChar

/-- A hypothesis about another generator is not tried as a leaf: unifying it with the callee would
unfold both, and the literal alphabet exceeds the recursion depth. -/
example (c : ℝ≥0∞) (_hrec : ∀ _ : Unit, c ≤ (genLongText n : SPMF (List Char)).mass) :
    (1 : ℝ≥0∞) ≤ (genLongChar : SPMF Char).mass := by
  mass_bound
  simp

end MassBoundTest
