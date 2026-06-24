import Basalt.Gen
import Basalt.Examples.ArbChar.Def

open RandomChoice ArbChar

namespace ArbString

/-- Helper function: generates a random list of alphanumeric characters -/
def genCharList [Gen G] : G (List Char) :=
  pick
    (fun _ => pure [])
    (fun () => do
      let x ← Char.arbitrary
      let xs ← genCharList
      return x :: xs)
partial_fixpoint

/-- Generates a random alphanumeric string -/
def String.arbitrary [Gen G] : G String :=
  String.ofList <$> genCharList

end ArbString
