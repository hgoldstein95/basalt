/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Segev Elazar Mittelman
-/
import Basalt

/-!
# Generator Lookup Classes and the Plausible Bridge

The base instances run; a fueled list respects its fuel; a Basalt-only instance is found through
Plausible's classes; and a native Plausible instance is not displaced by the bridge.
-/

open Basalt

/-- Samples drawn at `Plausible.Gen`. -/
def draw (g : Plausible.Gen α) (n : Nat := 50) : IO (List α) :=
  (List.range n).mapM fun _ => Plausible.Gen.run g 10

-- Every base instance runs.
#guard_msgs(drop info) in
#eval do
  IO.println (repr (← draw (Arbitrary.arbitrary (α := Nat)) 5))
  IO.println (repr (← draw (Arbitrary.arbitrary (α := Int)) 5))
  IO.println (repr (← draw (Arbitrary.arbitrary (α := String)) 5))
  IO.println (repr (← draw (Arbitrary.arbitrary (α := Option (Bool × Fin 3))) 5))
  IO.println (repr (← draw (Arbitrary.arbitrary (α := List (Nat ⊕ Char))) 5))

-- A fueled list is never longer than its fuel.
/-- info: true -/
#guard_msgs in
#eval do
  let xss ← draw (ArbitraryFueled.arbitraryFueled (α := List Nat) 3) 200
  return xss.all (·.length ≤ 3)

-- `Char` stays printable.
/-- info: true -/
#guard_msgs in
#eval do
  return (← draw (Arbitrary.arbitrary (α := Char)) 200).all fun c => 32 ≤ c.toNat ∧ c.toNat ≤ 126

/-! ## The bridge -/

/-- A type with only a Basalt instance. -/
structure Point where
  x : Nat
  y : Nat
  deriving Repr

instance : Arbitrary Point where
  arbitrary := do pure ⟨← Arbitrary.arbitrary, ← Arbitrary.arbitrary⟩

-- It is found through Plausible's class.
#guard_msgs(drop info) in
#eval do IO.println (repr (← draw (Plausible.Arbitrary.arbitrary : Plausible.Gen Point) 3))

-- And for `Nat`, which has both, Plausible's own instance is the one found.
/-- info: Plausible.Nat.Arbitrary -/
#guard_msgs in
#synth Plausible.Arbitrary Nat
