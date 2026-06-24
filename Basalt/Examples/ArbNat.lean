import Basalt
import Basalt.Examples.ArbNat.Def

open RandomChoice

namespace ArbNat

theorem Nat.arbitrary_support : n ∈ SPMF.support Nat.arbitrary := by
  induction n <;> rw [Nat.arbitrary] <;> simp [*]

theorem Nat.arbitrary_terminates : SPMF.IsPMF Nat.arbitrary := by
  refine (SPMF.IsPMF_of_mass_fixpoint
    (g := fun () => (Nat.arbitrary : SPMF Nat))
    (F := fun c => 1 / 2 + 1 / 2 * c)
    ?bounds ?mass) ()
  case bounds =>
    intro c hle hge
    apply ENNReal.eq_one_of_fixed_ineq' hle hge
    intro hmono
    rw [ENNReal.toReal_add (by norm_num) (by aesop), ENNReal.toReal_mul] at hmono
    norm_num at hmono; linarith
  case mass =>
    intro () h
    conv_lhs => rw [Nat.arbitrary]
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
    simp [IsBounded_iff] at *
    intro n c hn
    grind only [
      pick,
      SPMF.Cost.mem_support_bind_iff,
      SPMF.Cost.mem_support_choose_iff,
      SPMF.Cost.mem_support_pure_iff
    ]

instance : LawfulGenerator Nat.arbitrary ⊤ (fun n => n + 1) where
  support_iff := by simp [Nat.arbitrary_support]
  is_pmf := Nat.arbitrary_terminates
  is_bounded := Nat.arbitrary_cost

#guard_msgs(drop info) in
#eval (for _ in [0:20] do
  IO.println <| repr (← Nat.arbitrary) : IO Unit)

end ArbNat
