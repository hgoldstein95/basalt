/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt
import BasaltExamples.SkipList.Def

open RandomChoice

/-!
# Generating Skip Lists

`SkipList.genSkipList` generates the skip lists satisfying `SkipList.Valid`. The bounds are the
generator's parameters, so the recursion is structural on the length bound and completeness is
exact: the support is every skip list the bounds admit.
-/

namespace SkipList

/-- Generates a skip list of at most `fuel` entries with keys in `[lo, maxVal]`: stop, or draw a key
and a tower height and recurse above that key. The stop-or-continue choice is `stopOrGo` rather than
`pick`, which makes the length uniform on `[0, maxLen]` rather than geometric. -/
def genSkipListFrom [Gen G] (maxHeight maxVal : Nat) (hh : 1 ≤ maxHeight) :
    Nat → Nat → G (List Entry)
  | 0, _ => pure []
  | fuel + 1, lo =>
    if h : lo ≤ maxVal then
      stopOrGo fuel
        (fun () => pure [])
        (fun () => do
          let v ← chooseNat lo maxVal h
          let ht ← chooseNat 1 maxHeight hh
          let rest ← genSkipListFrom maxHeight maxVal hh fuel (v + 1)
          return ⟨v, ht⟩ :: rest)
    else
      pure []

/-- Generates a skip list within the bounds of `SkipList.Valid`. -/
def genSkipList [Gen G] (maxHeight maxLen maxVal : Nat) (hh : 1 ≤ maxHeight) : G (List Entry) :=
  genSkipListFrom maxHeight maxVal hh maxLen 0

theorem genSkipListFrom_mem_support {maxHeight maxVal : Nat} {hh : 1 ≤ maxHeight} (xs : List Entry)
    (fuel lo : Nat) :
    xs ∈ SPMF.support (genSkipListFrom maxHeight maxVal hh fuel lo) ↔
      xs.length ≤ fuel ∧
      xs.Pairwise (fun d e => d.val < e.val) ∧
      ∀ e ∈ xs, lo ≤ e.val ∧ e.val ≤ maxVal ∧ 1 ≤ e.height ∧ e.height ≤ maxHeight := by
  induction xs generalizing fuel lo with
  | nil =>
    cases fuel
    · simp [genSkipListFrom]
    · simp [genSkipListFrom]; omega
  | cons e rest ih =>
    obtain ⟨v, ht⟩ := e
    cases fuel with
    | zero => simp [genSkipListFrom]
    | succ fuel =>
      rw [genSkipListFrom]
      split
      · simp [ih, List.pairwise_cons]
        grind
      · simp only [SPMF.mem_support_pure_iff]
        constructor
        · simp
        · rintro ⟨-, -, hb⟩
          have := hb ⟨v, ht⟩ (by simp)
          omega

theorem genSkipListFrom.terminates {maxHeight maxVal : Nat} {hh : 1 ≤ maxHeight} :
    ∀ (fuel lo : Nat), IsAlmostSurelyTerminating (genSkipListFrom maxHeight maxVal hh fuel lo) := by
  intro fuel
  induction fuel with
  | zero => intro lo; rw [genSkipListFrom]; exact SPMF.IsPMF_pure _
  | succ fuel ih =>
    intro lo
    rw [genSkipListFrom]
    split
    · exact SPMF.IsPMF_stopOrGo (SPMF.IsPMF_pure _)
        (SPMF.IsPMF_bind (SPMF.IsPMF_chooseNat _ _ _) fun _ =>
          SPMF.IsPMF_bind (SPMF.IsPMF_chooseNat _ _ _) fun _ =>
            SPMF.IsPMF_bind (ih _) fun _ => SPMF.IsPMF_pure _)
    · exact SPMF.IsPMF_pure _

theorem genSkipList.terminates {maxHeight maxLen maxVal : Nat} {hh : 1 ≤ maxHeight} :
    IsAlmostSurelyTerminating (genSkipList maxHeight maxLen maxVal hh) :=
  genSkipListFrom.terminates _ _

theorem genSkipList.sound_complete {maxHeight maxLen maxVal : Nat} {hh : 1 ≤ maxHeight} :
    IsSoundAndComplete (genSkipList maxHeight maxLen maxVal hh)
      (Valid maxHeight maxLen maxVal) := by
  intro xs
  rw [genSkipList, genSkipListFrom_mem_support]
  simp [Valid]

end SkipList
