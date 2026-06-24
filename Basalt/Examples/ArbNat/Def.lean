import Basalt.Gen

open RandomChoice

namespace ArbNat

def Nat.arbitrary [Gen G] : G Nat := do
  pick
    (fun () => pure 0)
    (fun () => do
      let n ← Nat.arbitrary
      pure (n + 1))
partial_fixpoint

end ArbNat
