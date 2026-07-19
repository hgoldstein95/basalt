import Basalt
import Batteries.Data.Char
import BasaltExamples.ArbChar.Def

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

end ArbChar
