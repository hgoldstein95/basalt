import Basalt
import Basalt.Examples.ArbNat.Def

open RandomChoice

namespace ArbNat

theorem Nat.arbitrary_support : n ∈ SPMF.support Nat.arbitrary := by
  induction n <;> rw [Nat.arbitrary] <;> simp [*]

theorem Nat.arbitrary_terminates : SPMF.IsPMF Nat.arbitrary := by
  -- Static seed, mean offspring 1/2: subcritical.
  refine SPMF.IsPMF_of_subcritical_mass (m := 1 / 2) (by norm_num) ?_
  rw [ENNReal.one_sub_half]
  conv_rhs => rw [Nat.arbitrary]
  simp

theorem Nat.arbitrary_cost :
    IsBounded Nat.arbitrary (fun n => n + 1) := by
  open Lean.Order in
  delta arbitrary
  apply fix_induct (motive := fun (g : SPMF.Cost Nat) => IsBounded g (fun n => n + 1)) _ ?admissible ?step
  case admissible =>
    apply admissible_IsBounded
  case step =>
    intro arbitrary_rec ih
    rw [IsBounded_iff]
    rintro ⟨n, c⟩ hmem
    cost_support_simp at hmem
    obtain ⟨m, rfl, h | h⟩ := hmem
    · obtain ⟨rfl, rfl⟩ := h
      omega
    · obtain ⟨a, n1, n2, ha, ⟨hn, hn2⟩, hm⟩ := h
      have h1 : n1 ≤ a + 1 := ih (a, n1) ha
      show 1 + m ≤ n + 1
      omega

instance : LawfulGenerator Nat.arbitrary ⊤ (fun n => n + 1) where
  support_iff := by simp [Nat.arbitrary_support]
  is_pmf := Nat.arbitrary_terminates
  is_bounded := Nat.arbitrary_cost

#guard_msgs(drop info) in
#eval (for _ in [0:20] do
  IO.println <| repr (← Nat.arbitrary) : IO Unit)

end ArbNat
