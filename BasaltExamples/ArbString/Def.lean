import Basalt.Gen
import Basalt.Combinators
import BasaltExamples.ArbChar.Def

open RandomChoice ArbChar

namespace ArbString

/-- Generates a random (possibly empty) alphanumeric string -/
def String.arbitrary [Gen G] : G String :=
  String.ofList <$> listOf Char.arbitrary

/-- Generates a random, non-empty alphanumeric string -/
def NonEmptyString.arbitrary [Gen G] : G String :=
  String.ofList <$> nonEmptyListOf Char.arbitrary

end ArbString
