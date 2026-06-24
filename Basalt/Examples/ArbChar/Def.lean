import Basalt.Gen
import Basalt.Combinators

open RandomChoice

namespace ArbChar

/-- The 62 alphanumeric characters. -/
def alphanumChars : List Char :=
  "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz".toList

/-- Generates a random alphanumeric character -/
def Char.arbitrary [Gen G] : G Char :=
  elements alphanumChars (by decide)

end ArbChar
