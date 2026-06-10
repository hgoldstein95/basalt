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
    rw [genCharList]
    simp
  | cons c cs ih =>
    rw [genCharList]
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
    exact ⟨s.toList, genCharList_support.mpr h, by simp⟩

theorem genCharList_terminates : SPMF.IsPMF genCharList := by
  unfold genCharList
  apply SPMF.IsPMF_pick
  . apply SPMF.IsPMF_pure
  . sorry

end ArbString
