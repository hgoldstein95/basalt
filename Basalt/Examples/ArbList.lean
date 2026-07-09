import Basalt
import Basalt.Examples.ArbNat

open RandomChoice ArbNat

namespace ArbList

def List.arbitrary [Gen G] : G (List Nat) := do
  pick
    (fun () => pure [])
    (fun () => do
      let x ← Nat.arbitrary
      let xs ← List.arbitrary
      return x :: xs)
partial_fixpoint

-- Variant of `List.arbitrary` that uses the `vectorOf` combinator
-- to generate a length-`n` list of `Nat`s (where `n` is randomly chosen)
-- Note: the proofs below are about `List.arbitrary`
def List.arbitrary' [Gen G] : G (List Nat) := do
  let n ← Nat.arbitrary
  vectorOf n Nat.arbitrary

theorem List.arbitrary_support : xs ∈ SPMF.support List.arbitrary := by
  induction xs <;> rw [List.arbitrary]
  case _ => simp
  case _ x xs ih => simp [ih, Nat.arbitrary_support]

theorem List.arbitrary_terminates : SPMF.IsPMF List.arbitrary := by
  refine (SPMF.IsPMF_of_mass_fixpoint
    (g := fun () => (List.arbitrary : SPMF (List Nat)))
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
    conv_lhs => rw [List.arbitrary]
    simp only [SPMF.mass_pick, SPMF.mass_pure, mul_one]
    gcongr
    apply SPMF.mass_bind_ge_of_isPMF Nat.arbitrary_terminates
    intro x
    rw [SPMF.mass_bind_pure]
    exact SPMF.mass_ge_iInf _ ()

theorem List.arbitrary_cost :
    IsBounded List.arbitrary (fun xs => 2 * xs.length + xs.sum + 1) := by
  open Lean.Order in
  delta arbitrary
  apply fix_induct (motive := fun (g : SPMF.Cost (List Nat)) =>
    IsBounded g (fun xs => 2 * xs.length + xs.sum + 1)) _ ?admissible ?step
  case admissible =>
    apply admissible_IsBounded
  case step =>
    intro arbitrary_rec ih
    simp [IsBounded_iff] at *
    have := IsBounded_iff.mp Nat.arbitrary_cost
    intro xs c hxs
    grind [
      pick,
      SPMF.Cost.mem_support_bind_iff,
      SPMF.Cost.mem_support_choose_iff,
      SPMF.Cost.mem_support_pure_iff
    ]

instance : LawfulGenerator List.arbitrary ⊤ (fun xs => 2 * xs.length + xs.sum + 1) where
  support_iff := by simp [List.arbitrary_support]
  is_pmf := List.arbitrary_terminates
  is_bounded := List.arbitrary_cost

#guard_msgs(drop info) in
#eval (for _ in [0:20] do
  IO.println <| repr (← List.arbitrary) : IO Unit)

#guard_msgs(drop info) in
#eval (for _ in [0:10] do
  IO.println <| repr (← List.arbitrary') : IO Unit)


end ArbList
