import Basalt
import Batteries.Data.Char

open RandomChoice

namespace ArbChar

private def indexToChar (n : Nat) : Char :=
  if n < 10 then Char.ofNat (n + 48)
  else if n < 36 then Char.ofNat (n - 10 + 65)
  else Char.ofNat (n - 36 + 97)

/-- Generates a random alphanumeric character -/
def Char.arbitrary [Gen G] : G Char := do
  let n ← choose 0 61 (by omega)
  pure (indexToChar n.down)

private theorem indexToChar_isAlphanum :
    ∀ n, n ≤ 61 → (indexToChar n).isAlphanum = true := by decide

private theorem isAlphanum_exists_index :
    ∀ c : Char, c.isAlphanum = true → ∃ n, n ≤ 61 ∧ indexToChar n = c := by native_decide

theorem Char.arbitrary_support :
    c ∈ SPMF.support Char.arbitrary ↔ c.isAlphanum = true := by
  constructor
  · -- c ∈ SPMF.support Char.arbitrary -> c.isAlphanum = true
    intro h
    rw [Char.arbitrary] at h
    simp at h
    exact h.elim (fun n ⟨hhi, hc⟩ => hc ▸ indexToChar_isAlphanum n hhi)
  · -- c.isAlphanum = true -> c ∈ SPMF.support Char.arbitrary
    intro h
    rw [Char.arbitrary]
    simp
    obtain ⟨n, hhi, hc⟩ := isAlphanum_exists_index c h
    exact ⟨n, hhi, hc.symm⟩

theorem Char.arbitrary_terminates : SPMF.IsPMF Char.arbitrary := by
  unfold Char.arbitrary
  exact SPMF.IsPMF_bind_pure (SPMF.IsPMF_choose 0 61 (by omega))

#guard_msgs(drop info) in
#eval (for _ in [0:20] do
  IO.println <| repr (← Char.arbitrary) : IO Unit)

end ArbChar
