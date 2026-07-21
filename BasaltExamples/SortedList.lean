import Basalt
import BasaltExamples.ArbNat

open RandomChoice ArbNat

namespace SortedList

def List.genSortedGt [Gen G] (m : Nat) : G (List Nat) := do
  pick
    (fun () => pure [])
    (fun () => do
      let delta ← Nat.arbitrary
      let x := m + delta
      let xs ← List.genSortedGt x
      return x :: xs)
partial_fixpoint

def List.genSorted [Gen G] : G (List Nat) := List.genSortedGt 0

def List.genSorted.costBound (xs : List Nat) : Nat :=
  xs.length + 1 + -- Cost of choosing `xs.length` cons-cells and one nil.
  xs.sum + xs.length -- Cost of choosing `xs.length` natural numbers `n`, each of which costs `n + 1`.

def List.sorted (xs : List Nat) : Prop :=
  match xs with
  | [] => True
  | [_] => True
  | x :: y :: xs => x <= y ∧ List.sorted (y :: xs)

lemma List.sorted_cons_forall_le : List.sorted (x :: xs) → List.Forall (x ≤ ·) xs := by
  intro h
  induction xs
  case _ => simp
  case _ x xs ih => grind [= sorted.eq_def, sorted, List.forall_cons]

theorem List.genSortedGt_mem_support (xs : List Nat) (m : Nat) :
    xs ∈ SPMF.support (List.genSortedGt m) ↔ (List.sorted xs ∧ List.Forall (m ≤ ·) xs) := by
  fun_induction List.sorted generalizing m
  case _ =>
    unfold genSortedGt
    simp
  case _ x =>
    unfold genSortedGt
    simp
    constructor
    . grind
    . intro h
      exists x - m
      apply And.intro Nat.arbitrary_mem_support
      constructor
      . unfold genSortedGt
        simp
      . grind
  case _ x y xs ih =>
    unfold genSortedGt
    simp [ih, List.Forall, List.forall_cons]
    constructor
    . grind only [List.forall_iff_forall_mem, List.forall_cons]
    . intro h
      exists x - m
      grind only [
        List.forall_iff_forall_mem, List.Forall.eq_def, List.Forall.imp, List.sorted_cons_forall_le,
        sorted.eq_def, Nat.arbitrary_mem_support]

theorem List.genSortedGt.sound_complete :
    IsSoundAndComplete (List.genSortedGt m)
      (fun xs => List.sorted xs ∧ List.Forall (m ≤ ·) xs) :=
  fun xs => List.genSortedGt_mem_support xs m

theorem List.genSorted.sound_complete : IsSoundAndComplete List.genSorted List.sorted := by
  intro xs
  unfold genSorted
  simp [genSortedGt_mem_support, List.forall_iff_forall_mem]

theorem List.genSortedGt.terminates (m : Nat) : IsAlmostSurelyTerminating (List.genSortedGt m) := by
  -- Subcritical (mean offspring 1/2); the recursion re-indexes the seed, hence the family form.
  refine SPMF.IsPMF_of_subcritical_mass_family
    (fun (m : Nat) => (List.genSortedGt m : SPMF (List Nat)))
    (m := 1 / 2) (by norm_num) ?_ m
  intro n
  conv_rhs => unfold List.genSortedGt
  simp only [SPMF.mass_pick, SPMF.mass_pure, mul_one]
  gcongr
  · simp_all
  · apply SPMF.mass_bind_ge_of_isPMF Nat.arbitrary.terminates
    intro x
    simp only [SPMF.mass_bind_pure]
    exact SPMF.mass_ge_iInf _ (n + x)

theorem List.genSorted.terminates : IsAlmostSurelyTerminating List.genSorted :=
  List.genSortedGt.terminates 0

theorem List.genSortedGt.cost_bounded :
    IsCostBounded (List.genSortedGt m) (fun xs => xs.length + xs.sum + xs.length + 1) := by
  open Lean.Order in
  delta genSortedGt
  apply (fix_induct (motive := fun (g : Nat → SPMF.Cost (List Nat)) =>
    ∀ m, IsBounded (g m) (fun xs => xs.length + xs.sum + xs.length + 1)) _ ?admissible ?step) m
  case admissible =>
    exact admissible_pi_apply _ fun _ => admissible_IsBounded _
  case step =>
    intro genSortedGt_rec ih m
    rw [IsBounded_iff]
    rintro ⟨xs, c⟩ hmem
    cost_support_simp at hmem
    obtain ⟨k, rfl, h | h⟩ := hmem
    · obtain ⟨rfl, rfl⟩ := h
      simp
    · obtain ⟨delta, n1, n2, hdelta, ⟨tl, n3, n4, htl, ⟨rfl, hn4⟩, hn2⟩, hk⟩ := h
      have hhead : n1 ≤ delta + 1 := IsBounded_iff.mp Nat.arbitrary.cost_bounded (delta, n1) hdelta
      have htail : n3 ≤ tl.length + tl.sum + tl.length + 1 := ih (m + delta) (tl, n3) htl
      show 1 + k ≤ ((m + delta) :: tl).length + ((m + delta) :: tl).sum
        + ((m + delta) :: tl).length + 1
      simp only [List.length_cons, List.sum_cons]
      omega

theorem List.genSorted.cost_bounded :
    IsCostBounded List.genSorted List.genSorted.costBound :=
  IsBounded_mono List.genSortedGt.cost_bounded (by unfold genSorted.costBound; intro xs; omega)

end SortedList
