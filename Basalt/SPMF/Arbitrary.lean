/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Segev Elazar Mittelman
-/
import Basalt.Arbitrary
import Basalt.Laws
import Basalt.Walk.Complete
import Basalt.Walk.Entry
import Basalt.Walk.Sound

/-!
# Laws of the Base `Arbitrary` Instances

The recursive and finite base generators of `Basalt/Arbitrary.lean` reach every value of their type.
-/

namespace Basalt

theorem Nat.arbitraryGen.sound_complete : IsSoundAndComplete (Nat.arbitraryGen (G := SPMF)) ⊤ := by
  refine .intro (fun _ _ => trivial) ?complete
  intro n
  induction n with
  | zero => intro _; rw [Nat.arbitraryGen, SPMF.mem_support_iff_may]; walk
  | succ n ih =>
    intro _
    rw [Nat.arbitraryGen, SPMF.mem_support_iff_may]; walk
    exact ⟨n, ih trivial, rfl⟩

theorem Nat.mem_support_arbitraryGen (n : Nat) : n ∈ (Nat.arbitraryGen : SPMF Nat).support :=
  Nat.arbitraryGen.sound_complete.complete n trivial

theorem Bool.arbitrary.sound_complete :
    IsSoundAndComplete (Arbitrary.arbitrary (α := Bool) (G := SPMF)) ⊤ := by
  refine .intro (fun _ _ => trivial) ?complete
  intro b _
  rw [SPMF.mem_support_iff_may]
  simp only [Arbitrary.arbitrary]
  walk
  cases b
  · exact ⟨1, by omega, rfl⟩
  · exact ⟨0, by omega, rfl⟩

end Basalt
