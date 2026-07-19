import Basalt

open RandomChoice

def AllTwos (l : List Nat) : Prop := ∀ x ∈ l, x = 2

def AllTwos.cost (l : List Nat) : Nat := l.length + 1

def genAllTwos [Gen G] : G (List Nat) :=
  pick
    (fun () => pure [])
    (fun () => do
      let xs ← genAllTwos
      return 2 :: xs)
partial_fixpoint

theorem genAllTwos_support : a ∈ SPMF.support genAllTwos ↔ AllTwos a := by
  induction a with
  | nil =>
    rw [genAllTwos]
    simp [AllTwos]
  | cons x xs ih =>
    rw [genAllTwos]
    simp [ih, AllTwos, and_comm]

theorem genAllTwos_terminates : SPMF.IsPMF genAllTwos := by
  -- Static seed, mean offspring 1/2: subcritical.
  refine SPMF.IsPMF_of_subcritical_mass (m := 1 / 2) (by norm_num) ?_
  rw [ENNReal.one_sub_half]
  conv_rhs => rw [genAllTwos]
  simp

theorem genAllTwos_cost : IsBounded genAllTwos AllTwos.cost := by
  open Lean.Order in
  delta genAllTwos
  apply fix_induct (motive := fun (g : SPMF.Cost (List Nat)) =>
    IsBounded g AllTwos.cost) _ ?admissible ?step
  case admissible =>
    apply admissible_IsBounded
  case step =>
    intro genAllTwos_rec ih
    rw [IsBounded_iff]
    rintro ⟨xs, c⟩ hmem
    cost_support_simp at hmem
    obtain ⟨m, rfl, h | h⟩ := hmem
    · obtain ⟨rfl, rfl⟩ := h
      simp [AllTwos.cost]
    · obtain ⟨tl, n1, n2, htl, ⟨rfl, hn2⟩, hm⟩ := h
      have h1 : n1 ≤ AllTwos.cost tl := ih (tl, n1) htl
      show 1 + m ≤ AllTwos.cost (2 :: tl)
      simp only [AllTwos.cost, List.length_cons] at *
      omega

instance : LawfulGenerator genAllTwos AllTwos AllTwos.cost where
  support_iff := genAllTwos_support
  is_pmf      := genAllTwos_terminates
  is_bounded  := genAllTwos_cost
