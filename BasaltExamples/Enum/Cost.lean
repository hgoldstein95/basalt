/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Segev Elazar-Mittelman
-/
module

public import Basalt.Enum

/-!
# Generators With No Size, Graded by Cost

Run at `CostGraded Finite`, a generator's tier `n` is what it produces in exactly `n` choices. None of these
has a size, and two have infinite supports, so `Finite` alone has only `undef` for them; graded by
cost, every tier is finite.

* `genType`: each constructor is one choice, so cost is `Ty.size`, and tier `2k + 1` is the
  `Catalan k` types with `k` arrows.
* `geomList`: a list of length `k` costs `2k + 1` (a coin per step, a coin per element, a coin to
  stop), so tier `2k + 1` is the `2^k` lists of length `k`.
* `loop`, `g = pick (pure 0) g`: one value, infinitely many paths, one per tier.
-/

@[expose] public section

namespace Basalt.Examples.Enum.Cost

open Basalt RandomChoice

/-- `genType`, as in the STLC example: a coin, then a leaf or two recursive calls. -/
inductive Ty where
  | bool
  | fn (a b : Ty)
  deriving BEq, Repr

def Ty.size : Ty → Nat
  | .bool => 1
  | .fn a b => 1 + a.size + b.size

def genType [Gen G] : G Ty := do
  if (← choose 0 1 (by omega)).down.val = 0 then pure .bool
  else do
    let a ← genType
    let b ← genType
    pure (.fn a b)
partial_fixpoint

/-- A geometric list: a coin to stop or go on, and a coin for each element. -/
def geomList [Gen G] : G (List Bool) := do
  if (← choose 0 1 (by omega)).down.val = 0 then pure []
  else do
    let x := (← choose 0 1 (by omega)).down.val == 1
    let xs ← geomList
    pure (x :: xs)
partial_fixpoint

/-- One value, infinitely many paths to it. -/
def loop [Gen G] : G Nat := do
  if (← choose 0 1 (by omega)).down.val = 0 then pure 0 else loop
partial_fixpoint

end Basalt.Examples.Enum.Cost
