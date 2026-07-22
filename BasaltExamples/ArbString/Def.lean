/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt.Gen
import Basalt.Combinators
import BasaltExamples.ArbChar.Def

open RandomChoice ArbChar

/-!
# Arbitrary Strings (definitions)

The generator definitions for `ArbString`, split from their proofs
(`BasaltExamples/ArbString.lean`). `String.arbitrary` maps `String.ofList` over `genCharList`, a
recursive generator of alphanumeric character lists with the same subcritical shape as
`List.arbitrary`.
-/

namespace ArbString

/-- Generates a random (possibly empty) alphanumeric string -/
def String.arbitrary [Gen G] : G String :=
  String.ofList <$> listOf Char.arbitrary

/-- Generates a random, non-empty alphanumeric string -/
def NonEmptyString.arbitrary [Gen G] : G String :=
  String.ofList <$> nonEmptyListOf Char.arbitrary

end ArbString
