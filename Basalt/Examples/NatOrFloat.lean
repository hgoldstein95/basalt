import Basalt.Gen
import Basalt.Combinators

-- A tagged sum type `Nat + Float`
inductive NatOrFloat
  | Nat (n : Nat)
  | Float (f : Float)
deriving Repr

-- Generates either a `Nat` or a `Float` that's either 1,
-- a multiple of 2, or a multiple of 3
-- (This generator tests that we can use `oneOf` in functions marked as `partial_fixpoint`)
def myGen [Gen G] : G NatOrFloat :=
  oneOf [
    fun _ => RandomChoice.pick
      (fun _ => pure (NatOrFloat.Nat 1))
      (fun _ => pure (NatOrFloat.Float 1.0)),
    fun _ => do
      let natOrFloat ← myGen
      match natOrFloat with
      | .Nat n => pure (.Nat (n * 2))
      | .Float f => pure (.Float (f * 2)),
    fun _ => do
      let natOrFloat ← myGen
      match natOrFloat with
      | .Nat n => pure (.Nat (n * 3))
      | .Float f => pure (.Float (f * 3))

  ] (by simp)
partial_fixpoint

#guard_msgs(drop info) in
#eval (for _ in [0:10] do
  IO.println <| repr (← myGen) : IO Unit)
