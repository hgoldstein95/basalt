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
  unfold Char.arbitrary
  exact IsBounded_elements _

#guard_msgs(drop info) in
#eval (for _ in [0:20] do
  IO.println <| repr (← Char.arbitrary) : IO Unit)

end ArbChar
