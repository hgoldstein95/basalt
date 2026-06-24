import Basalt
import Batteries.Data.Char
import Basalt.Examples.ArbChar.Def

open RandomChoice

namespace ArbChar

private theorem indexToChar_isAlphanum :
    ∀ n, n ≤ 61 → (indexToChar n).isAlphanum = true := by decide

-- `decide` is too inefficient here, so we need to use `native_decide`
private theorem isAlphanum_exists_index :
    ∀ c : Char, c.isAlphanum = true → ∃ n, n ≤ 61 ∧ indexToChar n = c := by native_decide

/-- All alphanumeric characters are generable by `Char.arbitrary` -/
theorem Char.arbitrary_support :
    c ∈ SPMF.support Char.arbitrary ↔ c.isAlphanum = true := by
  constructor
  · -- c ∈ SPMF.support Char.arbitrary -> c.isAlphanum = true
    intro h
    rw [Char.arbitrary] at h
    simp at h
    obtain ⟨n, hle, rfl⟩ := h
    apply indexToChar_isAlphanum
    assumption
  · -- c.isAlphanum = true -> c ∈ SPMF.support Char.arbitrary
    intro h
    rw [Char.arbitrary]
    simp
    obtain ⟨n, hhi, hc⟩ := isAlphanum_exists_index c h
    exists n
    constructor
    . assumption
    . apply hc.symm

/-- `Char.arbitrary` almost surely terminates -/
theorem Char.arbitrary_terminates : SPMF.IsPMF Char.arbitrary := by
  unfold Char.arbitrary
  apply SPMF.IsPMF_bind_pure
  apply SPMF.IsPMF_choose

-- Proof is similar to `Nat.arbitrary_cost`, but `Char.arbitrary` makes only
-- one random choice, so `fun _ => 1` suffices as the cost function
theorem Char.arbitrary_cost :
    IsBounded Char.arbitrary (fun _ => 1) := by
  rw [IsBounded_iff]
  rintro ⟨c, cost⟩ h
  rw [Char.arbitrary] at h
  simp [SPMF.Cost.mem_support_bind_iff, SPMF.Cost.mem_support_choose_iff,
          SPMF.Cost.mem_support_pure_iff] at h
  omega

#guard_msgs(drop info) in
#eval (for _ in [0:20] do
  IO.println <| repr (← Char.arbitrary) : IO Unit)

end ArbChar
