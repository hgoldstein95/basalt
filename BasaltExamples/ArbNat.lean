/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt

/-!
# Arbitrary Natural Numbers

`Nat.arbitrary` generates an arbitrary natural number by repeatedly flipping a coin to decide
whether to increment. It is the simplest recursive generator in the cookbook and a building block
for several others (`ArbList`, `SortedList`, `Heap`).
-/

open RandomChoice

namespace ArbNat

/-- Generates an arbitrary natural number: flip a coin to stop at `0` or recurse and add one. -/
def Nat.arbitrary [Gen G] : G Nat := do
  oneOf! [
    fun _ => pure 0,
    fun _ => do
      let n ← Nat.arbitrary
      pure (n + 1)
  ]
partial_fixpoint

theorem Nat.arbitrary.sound_complete : IsSoundAndComplete Nat.arbitrary ⊤ := by
  refine .intro (fun _ _ => trivial) ?complete
  intro n
  induction n with
  | zero => intro _; rw [Nat.arbitrary, SPMF.mem_support_iff_may]; walk
  | succ n ih =>
    intro _
    rw [Nat.arbitrary, SPMF.mem_support_iff_may]; walk
    exact ⟨n, ih trivial, rfl⟩

theorem Nat.arbitrary.terminates : IsAlmostSurelyTerminating Nat.arbitrary := by
  mass_fixpoint using SPMF.LfpIsOne.affine (m := 1 / 2) (by norm_num)
  simp [ENNReal.div_eq_inv_mul, mul_add]

/-- Producing `n` costs `n + 1` random choices (one per increment, plus the final stop). -/
theorem Nat.arbitrary.cost_bounded :
    IsCostBounded Nat.arbitrary (fun n => n + 1) := by
  rw [IsCostBounded.iff_obs]
  walk fixpoint
  all_goals omega

theorem Nat.arbitrary.faithful : IsFaithful Nat.arbitrary := by
  faithful_fixpoint [Nat.arbitrary.terminates]

end ArbNat
