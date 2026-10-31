/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
module

public import Basalt

/-!
# Pairs of Numbers from Five to Ten

`genPairFiveToTen` draws two numbers from `[5, 10]` and pairs them. Its soundness is one `walk` over
two draws, with no recursion and no callee laws.
-/

@[expose] public section

open RandomChoice

namespace PairFiveToTen

def genFiveToTen [Gen G] : G Nat := chooseNat 5 10

def genPairFiveToTen [Gen G] : G (Nat × Nat) := do
  let x ← genFiveToTen
  let y ← genFiveToTen
  return (x, y)

theorem genPairFiveToTen.sound :
    IsSoundFor genPairFiveToTen (fun (x, y) => x ≤ 20 ∧ y ≤ 20) := by
  rw [IsSoundFor.iff_obs]
  walk
  all_goals grind

end PairFiveToTen
