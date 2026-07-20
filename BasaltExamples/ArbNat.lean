import Basalt

open RandomChoice

namespace ArbNat

def Nat.arbitrary [Gen G] : G Nat := do
  pick
    (fun () => pure 0)
    (fun () => do
      let n ← Nat.arbitrary
      pure (n + 1))
partial_fixpoint

theorem Nat.arbitrary_mem_support : n ∈ SPMF.support Nat.arbitrary := by
  induction n <;> rw [Nat.arbitrary] <;> simp [*]

theorem Nat.arbitrary_support : IsSoundAndComplete Nat.arbitrary ⊤ :=
  fun _ => iff_of_true Nat.arbitrary_mem_support trivial

theorem Nat.arbitrary_terminates : IsAlmostSurelyTerminating Nat.arbitrary := by
  -- Static seed, mean offspring 1/2: subcritical.
  refine SPMF.IsPMF_of_subcritical_mass (m := 1 / 2) (by norm_num) ?_
  rw [ENNReal.one_sub_half]
  conv_rhs => rw [Nat.arbitrary]
  simp

theorem Nat.arbitrary_cost :
    IsCostBounded Nat.arbitrary (fun n => n + 1) := by
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

end ArbNat
