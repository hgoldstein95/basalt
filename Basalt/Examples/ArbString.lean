import Basalt
import Batteries.Data.Char
import Basalt.Examples.ArbChar

open RandomChoice ArbChar

namespace ArbString

def genCharList [Gen G] : G (List Char) :=
  pick
    (fun _ => pure [])
    (fun () => do
      let x ← Char.arbitrary
      let xs ← genCharList
      return x :: xs)
partial_fixpoint

def String.arbitrary [Gen G] : G String :=
  String.ofList <$> genCharList

theorem genCharList_support :
    cs ∈ SPMF.support genCharList ↔ ∀ c ∈ cs, c.isAlphanum = true := by
  induction cs with
  | nil =>
    unfold genCharList
    simp
  | cons c cs ih =>
    unfold genCharList
    simp [Char.arbitrary_support, ih]

theorem String.arbitrary_support :
    s ∈ SPMF.support String.arbitrary ↔ (∀ c ∈ s.toList, c.isAlphanum = true) := by
  simp only [String.arbitrary, SPMF.mem_support_map_iff]
  constructor
  · rintro ⟨cs, hcs, heq⟩
    rw [genCharList_support] at hcs
    subst heq
    simpa using hcs
  · intro h
    let cs := s.toList
    exists cs
    constructor
    . apply genCharList_support.mpr
      assumption
    . rw [String.ofList_toList]

-- This proof is largely the same as `List.arbitrary_terminates`,
-- except with calls to `List.arbitrary` / `Nat.arbitrary` replaced with
-- `genCharList` / `Char.arbitrary` respectively
theorem genCharList_terminates : SPMF.IsPMF genCharList := by
  refine (SPMF.IsPMF_of_mass_fixpoint
    (g := fun () => (genCharList : SPMF (List Char)))
    (F := fun c => 1 / 2 + 1 / 2 * c)
    ?bounds ?mass) ()
  case bounds =>
    intro c hle hge
    dsimp at hge
    apply ENNReal.eq_one_of_fixed_ineq' hle hge
    intro hmono
    rw [ENNReal.toReal_add (by norm_num) (by aesop), ENNReal.toReal_mul] at hmono
    norm_num at hmono; linarith
  case mass =>
    intro () h
    conv_lhs => rw [genCharList]
    simp only [SPMF.mass_pick, SPMF.mass_pure, mul_one]
    gcongr
    apply SPMF.mass_bind_ge_of_isPMF Char.arbitrary_terminates
    intro c
    rw [SPMF.mass_bind_pure]
    exact SPMF.mass_ge_iInf _ ()

theorem String.arbitrary_terminates : SPMF.IsPMF String.arbitrary := by
  unfold String.arbitrary SPMF.IsPMF
  rw [SPMF.mass_map]
  apply genCharList_terminates

-- Proof is similar to `List.arbitrary_cost`
theorem genCharList_cost :
    IsBounded genCharList (fun cs => 2 * cs.length + (Char.toNat <$> cs).sum + 1) := by
  open Lean.Order in
  delta genCharList
  apply fix_induct (motive := fun (g : SPMF.Cost (List Char)) =>
    IsBounded g (fun cs => 2 * cs.length + (Char.toNat <$> cs).sum + 1)) _ ?admissible ?step
  case admissible =>
    apply admissible_IsBounded
  case step =>
    intro arbitrary_rec ih
    simp [IsBounded_iff] at *
    have := IsBounded_iff.mp Char.arbitrary_cost
    intro xs c hxs
    grind [
      pick,
      SPMF.Cost.mem_support_bind_iff,
      SPMF.Cost.mem_support_choose_iff,
      SPMF.Cost.mem_support_pure_iff
    ]

end ArbString
