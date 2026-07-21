import Basalt
import Batteries.Data.Char
import BasaltExamples.ArbChar
import BasaltExamples.ArbString.Def

open RandomChoice ArbChar

namespace ArbString

/-- `genCharList`'s support is exactly the set of alphanumeric characters -/
theorem genCharList_mem_support :
    cs ∈ SPMF.support genCharList ↔ ∀ c ∈ cs, c.isAlphanum = true := by
  induction cs with
  | nil =>
    unfold genCharList
    simp
  | cons c cs ih =>
    unfold genCharList
    simp [Char.arbitrary_mem_support, ih]

theorem genCharList.sound_complete :
    IsSoundAndComplete genCharList (fun cs => ∀ c ∈ cs, c.isAlphanum = true) :=
  fun _ => genCharList_mem_support

/-- `String.arbitrary`'s support is exactly the set of alphanumeric characters -/
theorem String.arbitrary.sound_complete :
    IsSoundAndComplete String.arbitrary (fun s => ∀ c ∈ s.toList, c.isAlphanum = true) := by
  intro s
  simp only [String.arbitrary, SPMF.mem_support_map_iff]
  constructor
  · rintro ⟨cs, hcs, heq⟩
    rw [genCharList_mem_support] at hcs
    subst heq
    simpa using hcs
  · intro h
    let cs := s.toList
    exists cs
    constructor
    . apply genCharList_mem_support.mpr
      assumption
    . rw [String.ofList_toList]

-- This proof is largely the same as `List.arbitrary.terminates`,
-- except with calls to `List.arbitrary` / `Nat.arbitrary` replaced with
-- `genCharList` / `Char.arbitrary` respectively
theorem genCharList.terminates : IsAlmostSurelyTerminating genCharList := by
  -- Static seed, mean offspring 1/2: subcritical.
  refine SPMF.IsPMF_of_subcritical_mass (m := 1 / 2) (by norm_num) ?_
  conv_rhs => rw [genCharList]
  simp only [SPMF.mass_pick, SPMF.mass_pure, mul_one]
  gcongr
  · simp_all
  · apply SPMF.mass_bind_ge_of_isPMF Char.arbitrary.terminates
    intro c
    rw [SPMF.mass_bind_pure]

/-- `String.arbitrary` almost surely terminates -/
theorem String.arbitrary.terminates : IsAlmostSurelyTerminating String.arbitrary := by
  unfold String.arbitrary IsAlmostSurelyTerminating SPMF.IsPMF
  rw [SPMF.mass_map]
  apply genCharList.terminates

-- Proof is similar to `List.arbitrary.cost_bounded`, except here the cost function
-- is just the no. of calls to `pick` + `Char.arbitrary` (`2 * cs.length`),
-- along with one final call to `pick` to produce the end of the list
theorem genCharList.cost_bounded :
    IsCostBounded genCharList (fun cs => 2 * cs.length + 1) := by
  open Lean.Order in
  delta genCharList
  -- Apply fixpoint induction
  apply fix_induct (motive := fun (g : SPMF.Cost (List Char)) =>
    IsBounded g (fun cs => 2 * cs.length + 1)) _ ?admissible ?step
  case admissible =>
    apply admissible_IsBounded
  case step =>
    intro arbitrary_rec ih
    rw [IsBounded_iff]
    rintro ⟨cs, c⟩ hmem
    cost_support_simp at hmem
    obtain ⟨m, rfl, h | h⟩ := hmem
    · obtain ⟨rfl, rfl⟩ := h
      simp
    · obtain ⟨ch, n1, n2, hch, ⟨tl, n3, n4, htl, ⟨rfl, hn4⟩, hn2⟩, hm⟩ := h
      have hhead : n1 ≤ 1 := IsBounded_iff.mp Char.arbitrary.cost_bounded (ch, n1) hch
      have htail : n3 ≤ 2 * tl.length + 1 := ih (tl, n3) htl
      show 1 + m ≤ 2 * (ch :: tl).length + 1
      simp only [List.length_cons]
      omega

theorem String.arbitrary.cost_bounded :
    IsCostBounded String.arbitrary (fun s => 2 * s.length + 1) := by
  unfold String.arbitrary IsCostBounded
  simp [IsBounded_iff]
  intro s cost cs hcs heq
  subst heq
  have hcost : cost ≤ 2 * cs.length + 1 :=
    IsBounded_iff.mp genCharList.cost_bounded (cs, cost) hcs
  simpa [String.length_ofList] using hcost

end ArbString
