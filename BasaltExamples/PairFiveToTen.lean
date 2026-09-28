import Basalt

open RandomChoice

def genFiveToTen [Gen G] : G Nat := chooseNat 5 10

def genPairFiveToTen [Gen G] : G (Nat × Nat) := do
  let x ← genFiveToTen
  let y ← genFiveToTen
  return (x, y)

theorem genPairFiveToTen.sound :
    IsSoundFor genPairFiveToTen (fun (x, y) => x ≤ 20 ∧ y ≤ 20) := by
  rw [IsSoundFor.iff_obs]
  walk
  all_goals grind
