/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
module

public import Basalt.Enum

/-!
# Memoized Tiers: Compositions

The compositions of `n` into parts `1` and `2`, counted by the Fibonacci numbers. Size `n + 2`
consults sizes `n + 1` and `n`, so recursing (`SizedStep.fix`) re-derives each smaller tier a
Fibonacci number of times, while the table (`SizedStep.tiers`) derives each once.
-/

@[expose] public section

namespace Basalt.Examples.Enum.Compositions

open Basalt RandomChoice

/-- The compositions of `n` into parts `1` and `2`. Size `n + 2` consults sizes `n + 1` and `n`,
so recursing re-derives each smaller tier a Fibonacci number of times. -/
def compositions [Monad G] [RandomChoice G] : SizedStep G (List Nat) := fun n rec =>
  match n, rec with
  | 0, _ => pure []
  | 1, _ => pure [1]
  | n + 2, rec => do
    if (← choose 0 1 (by omega)).down.val = 0 then
      (1 :: ·) <$> rec (n + 1) (by omega)
    else
      (2 :: ·) <$> rec n (by omega)

end Basalt.Examples.Enum.Compositions
