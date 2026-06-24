import Basalt
import Batteries.Data.Char
import Basalt.Examples.ArbChar.Def

open RandomChoice

namespace ArbChar

private theorem alphanumChars_eq_filter :
    ∀ c : Char, c ∈ alphanumChars ↔ c.isAlphanum = true := by native_decide

/-- All alphanumeric characters are generable by `Char.arbitrary` -/
theorem Char.arbitrary_support :
    c ∈ SPMF.support Char.arbitrary ↔ c.isAlphanum = true := by
  rw [Char.arbitrary, SPMF.mem_support_elements_iff]
  exact alphanumChars_eq_filter c

/-- `Char.arbitrary` almost surely terminates -/
theorem Char.arbitrary_terminates : SPMF.IsPMF Char.arbitrary := by
  unfold Char.arbitrary
  apply SPMF.IsPMF_elements

theorem Char.arbitrary_cost :
    IsBounded Char.arbitrary (fun _ => 1) := by
  rw [IsBounded_iff]
  rintro ⟨c, cost⟩ h
  rw [Char.arbitrary, elements] at h
  simp only [SPMF.Cost.mem_support_bind_iff, Functor.map] at h
  obtain ⟨⟨i, hi⟩, n1, n2, h1, h2, rfl⟩ := h
  -- h2: (c, n2) ∈ support of (pure alphanumChars[i]) in Cost monad → n2 = 0
  have hlen : alphanumChars.length = 62 := by native_decide
  replace h2 : n2 = 0 := by
    split at h2
    simp only [Pure.pure, SPMF.mem_support_pure_iff, Prod.mk.injEq] at h2
    exact h2.2
  subst h2
  -- h1: (⟨i,hi⟩, n1) ∈ support of (ULift.down <$> choose) in Cost monad → n1 = 1
  replace h1 : n1 = 1 := by
    revert h1
    simp [SPMF.mem_support_bind_iff, SPMF.mem_support_pure_iff]
  subst h1
  simp

#guard_msgs(drop info) in
#eval (for _ in [0:20] do
  IO.println <| repr (← Char.arbitrary) : IO Unit)

end ArbChar
