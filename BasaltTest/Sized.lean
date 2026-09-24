/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt

open RandomChoice

/-!
# Size-Parameterized Generators

Pins `Basalt/Sized.lean`: `WithSize` is a generator monad at every interpretation and under
`OptionT`, `sized`/`resize` compute as expected, and a recursive generator can use them under
`partial_fixpoint`.
-/

namespace SizedTest

/-! ## Instances -/

example : Gen (WithSize IO) := inferInstance
noncomputable example : Gen (WithSize SPMF) := inferInstance
noncomputable example : MonoSized (WithSize SPMF) := inferInstance
example : Gen (OptionT (WithSize IO)) := inferInstance
example : MonoSized (OptionT (WithSize IO)) := inferInstance

/-! ## `sized` and `resize` -/

example : (getSize : WithSize SPMF Nat).run 7 = pure 7 := rfl
example : (Sized.resize 3 getSize : WithSize SPMF Nat).run 7 = pure 3 := rfl
example : (getSize : OptionT (WithSize SPMF) Nat).run.run 7 = pure (some 7) := rfl

/-- A list no longer than the ambient size: each cons cell shrinks the size by one. -/
def sizedList [Gen G] [Sized G] [MonoSized G] : G (List Nat) :=
  Sized.sized fun
    | 0 => pure []
    | n + 1 => oneOf [
        fun _ => pure [],
        fun _ => do
          let x ← chooseNat 0 9
          let xs ← Sized.resize n sizedList
          pure (x :: xs)
      ]
partial_fixpoint

/-- Draw `sizedList` at size `n` `k` times and check every draw fits. -/
def lengthsBounded (k n : Nat) : IO Bool := do
  let mut ok := true
  for _ in [0:k] do
    ok := ok && (← (sizedList : WithSize IO _).run n).length ≤ n
  pure ok

/-- info: true -/
#guard_msgs in #eval lengthsBounded 100 3

/-- info: [] -/
#guard_msgs in #eval (sizedList : WithSize IO _).run 0

/-! ## Lifting and `OptionT` -/

/-- A size-agnostic `IO` draw is lifted into `WithSize IO` by `←`. -/
def sizePlusDraw : WithSize IO Nat := do
  let n ← getSize
  let x ← (chooseNat 0 0 : IO Nat)
  pure (n + x)

/-- info: 5 -/
#guard_msgs in #eval sizePlusDraw.run 5

/-- A filtering generator that reads the size. -/
def evenSize : OptionT (WithSize IO) Nat := do
  let n ← getSize
  if n % 2 = 0 then pure n else failure

/-- info: (some 4, none) -/
#guard_msgs in #eval return (← evenSize.run.run 4, ← evenSize.run.run 3)

end SizedTest
