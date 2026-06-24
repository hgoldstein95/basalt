import Basalt.Gen

open RandomChoice

namespace ArbChar

def indexToChar (n : Nat) : Char :=
  if n < 10 then Char.ofNat (n + 48)
  else if n < 36 then Char.ofNat (n - 10 + 65)
  else Char.ofNat (n - 36 + 97)

/-- Generates a random alphanumeric character -/
def Char.arbitrary [Gen G] : G Char := do
  let n ← choose 0 61 (by omega)
  pure (indexToChar n.down.val)

end ArbChar
