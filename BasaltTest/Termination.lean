/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt
import BasaltExamples.BST

open RandomChoice ENNReal

/-!
# The `mass_fixpoint` Contract

Pins what `mass_fixpoint` leaves behind: the context it introduces over a tupled seed, the
certificate goal when no certificate is named, and its failures.
-/

namespace TerminationTest

-- The seed is the tuple of arguments the recursion changes, introduced under their binder names,
-- and the goal is the certificate's `F c` against the bound `mass_bound` computed.
/--
trace: c : ℝ≥0∞
hc1 : c ≤ 1
hrec : ∀ (j : ℤ × ℤ), c ≤ (BST.Tree.genBST j.1 j.2).mass
lo hi : ℤ
⊢ 1 / 2 + 0 * c + 1 / 2 * c ^ 2 ≤
    if lo > hi then 1
    else
      (List.map (fun p => ↑p.1 * p.2) [(1, 1), (1, 1 * (c * (c * 1)))]).sum /
        ↑(List.map Prod.fst [(1, 1), (1, 1 * (c * (c * 1)))]).sum
-/
#guard_msgs in
example (lo hi : Int) : IsAlmostSurelyTerminating (BST.Tree.genBST lo hi) := by
  mass_fixpoint using SPMF.LfpIsOne.quadratic (a := 1 / 2) (b := 0) (d := 1 / 2)
    (by ennreal_to_real; norm_num) (by ennreal_to_real; norm_num) (by norm_num)
  trace_state
  split
  · rw [zero_mul, add_zero]
    calc (1 : ℝ≥0∞) / 2 + 1 / 2 * c ^ 2 ≤ 1 / 2 + 1 / 2 * 1 ^ 2 := by gcongr
      _ = 1 := by rw [one_pow, mul_one, ENNReal.add_halves]
  · simp [sq, ENNReal.div_eq_inv_mul, mul_add]

/-- A generator whose arguments never change has the `Unit` seed. -/
def coins [Gen G] (b : Bool) : G Nat :=
  pick (fun () => pure 0) (fun () => do let n ← coins b; pure (if b then n + 1 else n))
partial_fixpoint

-- Without a certificate, `F` is the computed bound and the certificate is the goal.
/--
trace: case certificate
b : Bool
⊢ SPMF.LfpIsOne fun c => 1 / 2 * 1 + 1 / 2 * (c * 1)
-/
#guard_msgs in
example (b : Bool) : IsAlmostSurelyTerminating (coins b) := by
  mass_fixpoint
  trace_state
  exact SPMF.LfpIsOne.mono (SPMF.LfpIsOne.affine (m := 1 / 2) (by norm_num)) fun c _ => by simp

/-- Weights that depend on the seed. -/
def countdown [Gen G] (n : Nat) : G Nat :=
  if n = 0 then pure 0
  else frequency [(n, fun () => pure n), (1, fun () => countdown (n - 1))] (by simp)
partial_fixpoint

/--
error: mass_fixpoint: the computed bound depends on the seed, so it is no single `F c`:
  if n = 0 then 1 else (List.map (fun p => ↑p.1 * p.2) [(n, 1), (1, c)]).sum / ↑(List.map Prod.fst [(n, 1), (1, c)]).sum
Name a certificate with `mass_fixpoint using _`, or take the bound as a function of the seed with `mass_fixpoint per_seed`.
-/
#guard_msgs in
example (n : Nat) : IsAlmostSurelyTerminating (countdown n) := by
  mass_fixpoint

/--
error: mass_fixpoint: expected a goal `IsAlmostSurelyTerminating (gen …)`, got
  1 = 1
-/
#guard_msgs in
example : 1 = 1 := by
  mass_fixpoint

-- `per_seed` takes the computed bound as a function of the bound family `c` and the seed, so it may
-- depend on the seed, and leaves the certificate for it.
/--
trace: case certificate
n : ℕ
⊢ SPMF.LfpIsOne fun c n =>
    if n = 0 then 1
    else
      (List.map (fun p => ↑p.1 * p.2) [(n, 1), (1, c (n - 1))]).sum / ↑(List.map Prod.fst [(n, 1), (1, c (n - 1))]).sum
-/
#guard_msgs in
example (n : Nat) : IsAlmostSurelyTerminating (countdown n) := by
  mass_fixpoint per_seed
  trace_state
  -- Every seed's bound is `1` once its predecessor's is.
  intro c hc hT
  funext n
  induction n with
  | zero => simpa using le_antisymm (hc 0) (hT 0)
  | succ n ih =>
    refine le_antisymm (hc _) (le_trans (le_of_eq ?_) (hT (n + 1)))
    simp [ih]
    exact (ENNReal.div_self (a := (n : ℝ≥0∞) + 1 + 1) (by simp) (by simp)).symm

-- A combinator term is not a generator definition: there is no seed to find or equation to unfold.
/--
error: mass_fixpoint: `frequency` is a combinator, not a generator definition; prove `SPMF.IsPMF` of a combinator term with `SPMF.IsPMF.of_one_le` and `mass_bound`
-/
#guard_msgs in
example : SPMF.IsPMF (frequency [(1, fun _ => Pure.pure 0), (1, fun _ => Pure.pure 1)]
    (by simp) : SPMF Nat) := by
  mass_fixpoint using SPMF.LfpIsOne.one

/-- A budget-weighted stop leaves a bound whose weights cancel. -/
def stopAfter [Gen G] (n : Nat) : G Nat := stopOrGo n (fun _ => pure 0) (fun _ => pure 1)

example (n : Nat) : IsAlmostSurelyTerminating (stopAfter n) := by
  mass_fixpoint using SPMF.LfpIsOne.one
  simp [ENNReal.div_self]

/-- Matching on an argument makes it no seed when nothing recurses, so an argument whose type
depends on it is harmless. -/
def byCases [Gen G] (n : Nat) (_h : 0 < n) : G Nat :=
  match n with
  | 1 => pure 0
  | _ + 2 => chooseNat 0 1

example (n : Nat) (h : 0 < n) : IsAlmostSurelyTerminating (byCases n h) := by
  match n, h with
  | 1, h => mass_fixpoint using SPMF.LfpIsOne.one; simp
  | _ + 2, h => mass_fixpoint using SPMF.LfpIsOne.one; simp

end TerminationTest
