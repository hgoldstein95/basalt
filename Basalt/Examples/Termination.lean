import Basalt
import Basalt.Examples.NatList

open RandomChoice

namespace NatListExample

theorem Nat.SPMF.IsPMF_arbitrary : SPMF.IsPMF Nat.arbitrary := by
  apply SPMF.IsPMF_pick_pure_of_mass_eq
  . rw [Nat.arbitrary]
  . exact SPMF.mass_bind_pure

theorem List.SPMF.IsPMF_arbitrary : SPMF.IsPMF List.arbitrary := by
  apply SPMF.IsPMF_pick_pure_of_mass_eq
  . rw [List.arbitrary]
  . apply SPMF.mass_bind_of_const_mass
    . exact Nat.SPMF.IsPMF_arbitrary
    . exact fun _ => SPMF.mass_bind_pure

theorem List.not_SPMF.IsPMF_diverge : ¬SPMF.IsPMF List.diverge := by
  have : (List.diverge : SPMF (List Nat)).mass = 0 := by
    apply SPMF.mass_eq_zero_of_support_empty
    ext xs
    induction xs <;> rw [List.diverge] <;> simp
    grind
  rw [SPMF.IsPMF, this]
  simp

theorem List.not_SPMF.IsPMF_pick_pure_nil_diverge :
    ¬SPMF.IsPMF (pick (fun () => pure []) (fun () => List.diverge)) := by
  have : (List.diverge : SPMF (List Nat)).mass = 0 := by
    apply SPMF.mass_eq_zero_of_support_empty
    ext xs
    induction xs <;> rw [List.diverge] <;> simp
    grind
  rw [SPMF.IsPMF, SPMF.mass_pick, this, SPMF.mass_pure]
  simp

end NatListExample
