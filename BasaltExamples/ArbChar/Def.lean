/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt.Combinators
import Basalt.Gen

/-!
# Arbitrary Characters (definitions)

The generator definition for `ArbChar`, split from its proofs (`BasaltExamples/ArbChar.lean`) so
that `ArbString` can depend on just the definition. `Char.arbitrary` draws a uniformly random
alphanumeric character with the `elements` combinator.
-/

open RandomChoice

namespace ArbChar

/-- The 62 alphanumeric characters. -/
def alphanumChars : List Char :=
  "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz".toList

/-- Generates a random alphanumeric character -/
def Char.arbitrary [Gen G] : G Char :=
  elements alphanumChars (by decide)

end ArbChar
