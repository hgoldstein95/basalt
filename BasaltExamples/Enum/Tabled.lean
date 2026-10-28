/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Segev Elazar-Mittelman
-/
module

public import Basalt.Enum
public import Basalt.Enum.TabledLaws

/-!
# Recursion With No Measure

Steps in open-recursion form with no measure: each may call any key, its own included. Their supports
(`PolyStep.supports`):

* `loopStep`, `g = pick (pure 0) g`: `{0}`, though it has a path for every number of coin flips;
* `flipStep`, `h = pick (pure true) (not <$> h)`: `{true, false}`, a cycle through a function;
* `bstStep`, BSTs over a range, recursing on the range: finite, as many as there are trees;
* `listStep`, a geometric list: infinite, so it never settles;
* `growStep`, keys that grow forever: infinite too;
* `mixStep`: `0` and `1` call each other and make `{0, 1, 2, …}`, while `2` alone is `{7}`.
-/

@[expose] public section

namespace Basalt.Examples.Enum.Tabled

open Basalt RandomChoice

/-! ## `g = pick (pure 0) g` -/

def loopStep [Monad G] [RandomChoice G] (rec : Unit → G Nat) (u : Unit) : G Nat := do
  if (← choose 0 1 (by omega)).down.val = 0 then pure 0 else rec u

/-! ## A geometric list -/

def listStep [Monad G] [RandomChoice G] (rec : Unit → G (List Nat)) (u : Unit) : G (List Nat) := do
  if (← choose 0 1 (by omega)).down.val = 0 then pure []
  else do
    let x := (← choose 0 1 (by omega)).down.val
    let xs ← rec u
    pure (x :: xs)

/-! ## BSTs over a range -/

inductive Tree where
  | leaf
  | node (l : Tree) (x : Int) (r : Tree)
  deriving BEq

def bstStep [Monad G] [RandomChoice G] (rec : Int × Int → G Tree) : Int × Int → G Tree
  | (lo, hi) =>
    if lo > hi then pure .leaf
    else do
      if (← choose 0 1 (by omega)).down.val = 0 then pure .leaf
      else do
        let x := lo + ((← choose 0 (hi - lo).toNat (Nat.zero_le _)).down.val : Int)
        let l ← rec (lo, x - 1)
        let r ← rec (x + 1, hi)
        pure (.node l x r)

/-! ## A two-key cycle beside a key outside it -/

def mixStep [Monad G] [RandomChoice G] (rec : Nat → G Nat) : Nat → G Nat
  | 0 => do if (← choose 0 1 (by omega)).down.val = 0 then pure 0 else rec 1
  | 1 => do return (← rec 0) + 1
  | _ => pure 7

/-- A cycle through a function: `h = pick (pure true) (not <$> h)`. -/
def flipStep [Monad G] [RandomChoice G] (rec : Unit → G Bool) (u : Unit) : G Bool := do
  if (← choose 0 1 (by omega)).down.val = 0 then pure true else do return !(← rec u)

/-- Keys that grow forever: no cycle to find, and infinitely many values. -/
def growStep [Monad G] [RandomChoice G] (rec : Nat → G Nat) (n : Nat) : G Nat := do
  if (← choose 0 1 (by omega)).down.val = 0 then pure n else rec (n + 1)

/-! ## `g = pick (pure 0) g` succeeds with exactly `0`

A run of `supports` that finished is a theorem about the least fixpoint: the step's obligations are
proved from the construct lemmas. What the run computed is the hypothesis, which the kernel cannot
evaluate (the table is a hash map) and `BasaltTest/Enum.lean` checks by evaluation. -/

open Lean.Order in
theorem loopStep_mono : monotone (loopStep (G := OptionT SPMF)) := by
  intro a b h u
  exact MonoBind.bind_mono_right fun _ => by
    split
    · exact PartialOrder.rel_refl
    · exact h u

def loopPoly : PolyStep Unit Nat := fun _ _ _ _ => loopStep

/-- What the run computes: it finishes, with `[0]` at the one key. -/
def LoopRun : Prop := (PolyStep.supports loopPoly 10 [()]).complete = true ∧
    (PolyStep.supports loopPoly 10 [()]).table[()]? = some [0]

/-- The least fixpoint of `g = pick (pure 0) g` succeeds with `0` and nothing else. -/
theorem loop_succeeds_iff (loop_run : LoopRun) (a : Nat) :
    some a ∈ ((loopPoly.lfp loopStep_mono ()).run).support ↔ a = 0 := by
  rw [← PolyStep.supports_eq loopPoly loopStep_mono
    (fun _ k => SetM.sound_bind (fun _ => SetM.sound_ite (fun _ => SetM.sound_pure 0)
      (fun _ => SetM.sound_lookup k)) (SetM.sound_choose _ _ _))
    (fun _ k => SetM.comp_bind (fun _ => SetM.comp_ite (fun _ => SetM.comp_pure 0)
      (fun _ => SetM.comp_lookup k)) (SetM.comp_choose _ _ _))
    10 [()] loop_run.1 () [0] loop_run.2 a]
  simp

end Basalt.Examples.Enum.Tabled
