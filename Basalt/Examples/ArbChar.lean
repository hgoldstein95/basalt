import Basalt
import Batteries.Data.Char

open RandomChoice

namespace ArbChar

-- The space of Unicode values that correspond to alphanumeric chars
-- consist of 3 disjoint intervals (48–57, 65–90, 97–122),
-- so we can't just generate an arbitrary `Nat` and then pass it to `Char.ofNat`.
-- Instead, we define this helper function, which we call in `Char.arbitrary` below
-- so that we can just generate a `Nat` in the interval [0, 61], which simplifes
-- the proofs below.
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
    exact h.elim (fun n ⟨hhi, hc⟩ => hc ▸ indexToChar_isAlphanum n hhi)
  · -- c.isAlphanum = true -> c ∈ SPMF.support Char.arbitrary
    intro h
    rw [Char.arbitrary]
    simp
    obtain ⟨n, hhi, hc⟩ := isAlphanum_exists_index c h
    exact ⟨n, hhi, hc.symm⟩

theorem Char.arbitrary_terminates : SPMF.IsPMF Char.arbitrary := by
  unfold Char.arbitrary
  apply SPMF.IsPMF_bind_pure
  apply SPMF.IsPMF_choose

-- `Char.arbitrary` makes just one call to `RandomChoice.choose`,
-- so `fun _ => 1` suffices as the cost function
theorem Char.arbitrary_cost :
    IsBounded Char.arbitrary (fun _ => (1 : Nat)) := by
  rw [IsBounded_iff]
  intro ⟨c, cost⟩ h
  rw [Char.arbitrary] at h
  simp [SPMF.Cost.mem_support_bind_iff, SPMF.Cost.mem_support_choose_iff,
          SPMF.Cost.mem_support_pure_iff] at h
  obtain ⟨ n, ⟨ _, h_eq ⟩, _ ⟩ := h
  subst h_eq
  rfl

#guard_msgs(drop info) in
#eval (for _ in [0:20] do
  IO.println <| repr (← Char.arbitrary) : IO Unit)

end ArbChar
