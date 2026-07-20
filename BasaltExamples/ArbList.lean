import Basalt
import BasaltExamples.ArbNat

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

theorem List.arbitrary.sound_complete : IsSoundAndComplete List.arbitrary ⊤ := by
  intro xs
  simp only [Pi.top_apply]
  induction xs <;> rw [List.arbitrary]
  case _ => simp
  case _ x xs ih => simp [ih, Nat.arbitrary_mem_support]

theorem List.arbitrary.terminates : IsAlmostSurelyTerminating List.arbitrary := by
  -- Static seed, mean offspring 1/2: subcritical.
  refine SPMF.IsPMF_of_subcritical_mass (m := 1 / 2) (by norm_num) ?_
  rw [ENNReal.one_sub_half]
  conv_rhs => rw [List.arbitrary]
  simp only [SPMF.mass_pick, SPMF.mass_pure, mul_one]
  gcongr
  apply SPMF.mass_bind_ge_of_isPMF Nat.arbitrary.terminates
  intro x
  rw [SPMF.mass_bind_pure]

theorem List.arbitrary.cost_bounded :
    IsCostBounded List.arbitrary (fun xs => 2 * xs.length + xs.sum + 1) := by
  open Lean.Order in
  delta arbitrary
  apply fix_induct (motive := fun (g : SPMF.Cost (List Nat)) =>
    IsBounded g (fun xs => 2 * xs.length + xs.sum + 1)) _ ?admissible ?step
  case admissible =>
    apply admissible_IsBounded
  case step =>
    intro arbitrary_rec ih
    rw [IsBounded_iff]
    rintro ⟨xs, c⟩ hmem
    cost_support_simp at hmem
    obtain ⟨m, rfl, h | h⟩ := hmem
    · obtain ⟨rfl, rfl⟩ := h
      simp
    · obtain ⟨x, n1, n2, hx, ⟨tl, n3, n4, htl, ⟨rfl, hn4⟩, hn2⟩, hm⟩ := h
      have hhead : n1 ≤ x + 1 := IsBounded_iff.mp Nat.arbitrary.cost_bounded (x, n1) hx
      have htail : n3 ≤ 2 * tl.length + tl.sum + 1 := ih (tl, n3) htl
      show 1 + m ≤ 2 * (x :: tl).length + (x :: tl).sum + 1
      simp only [List.length_cons, List.sum_cons]
      omega

end ArbList
