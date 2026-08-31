/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt
import BasaltExamples.SortedIntList.Def

open RandomChoice

/-!
# Gap-Bounded Sorted Lists

`List.genBoundedGapped` generates the specialized sorted lists of
`BasaltExamples/SortedIntList/Def`, where consecutive elements are at most `k` apart. The gap enters
as the upper bound `min hi (lo + k)` on each element after the first; the first element, which the
predicate leaves free, is the one the top-level generator draws from all of `[0, maxVal]`.
-/

namespace SortedIntList

/-- Generates a gap-bounded list of at most `n` elements, all of them in `[lo, hi]` and the first of
them within `k` of `lo`. -/
def List.genGappedFrom [Gen G] (k : Nat) : Nat → Int → Int → G (List Int)
  | 0, _, _ => pure []
  | n + 1, lo, hi =>
    if h : lo ≤ hi then
      stopOrGo n
        (fun () => pure [])
        (fun () => do
          let x ← chooseInt lo (min hi (lo + k)) (by omega)
          let xs ← List.genGappedFrom k n x hi
          return x :: xs)
    else
      pure []

/-- Generates a gap-bounded sorted list: the first element is drawn from all of `[0, maxVal]`, the
rest by `genGappedFrom`. Both use `stopOrGo` rather than `pick`, so the length is uniform on
`[0, maxLen]`. -/
def List.genBoundedGapped [Gen G] (k : Nat) : Nat → Int → G (List Int)
  | 0, _ => pure []
  | n + 1, maxVal =>
    if h : (0 : Int) ≤ maxVal then
      stopOrGo n
        (fun () => pure [])
        (fun () => do
          let x ← chooseInt 0 maxVal h
          let xs ← List.genGappedFrom k n x maxVal
          return x :: xs)
    else
      pure []

/-- Any chain relation refining `≤` bounds the whole list below by the prefixed element. -/
theorem List.isChain_cons_forall_le {R : Int → Int → Prop} (hR : ∀ a b, R a b → a ≤ b)
    {lo : Int} {xs : List Int} (h : (lo :: xs).IsChain R) : ∀ x ∈ xs, lo ≤ x :=
  fun _ hx => (h.imp fun _ _ hab => hR _ _ hab).rel_cons hx

theorem List.genGappedFrom_mem_support (k n : Nat) (lo hi : Int) (xs : List Int) :
    xs ∈ SPMF.support (List.genGappedFrom k n lo hi) ↔
      xs.length ≤ n ∧ (∀ x ∈ xs, x ≤ hi) ∧
        (lo :: xs).IsChain (fun x y => x ≤ y ∧ y - x ≤ (k : Int)) := by
  induction n generalizing lo xs with
  | zero => cases xs <;> simp [List.genGappedFrom]
  | succ n ih =>
    simp only [List.genGappedFrom]
    support_simp [ih]
    cases xs <;> simp <;> grind

theorem List.genGappedFrom.terminates : ∀ (k n : Nat) (lo hi : Int),
    IsAlmostSurelyTerminating (List.genGappedFrom k n lo hi) := by
  intro k n
  induction n with
  | zero => intro lo hi; rw [List.genGappedFrom]; exact SPMF.IsPMF_pure _
  | succ n ih =>
    intro lo hi
    rw [List.genGappedFrom]
    split
    · exact SPMF.IsPMF_stopOrGo (SPMF.IsPMF_pure _)
        (SPMF.IsPMF_bind (SPMF.IsPMF_chooseInt _ _ _) fun _ =>
          SPMF.IsPMF_bind (ih _ _) fun _ => SPMF.IsPMF_pure _)
    · exact SPMF.IsPMF_pure _

theorem List.genBoundedGapped.terminates (k maxLen : Nat) (maxVal : Int) :
    IsAlmostSurelyTerminating (List.genBoundedGapped k maxLen maxVal) := by
  cases maxLen with
  | zero => rw [List.genBoundedGapped]; exact SPMF.IsPMF_pure _
  | succ n =>
    rw [List.genBoundedGapped]
    split
    · exact SPMF.IsPMF_stopOrGo (SPMF.IsPMF_pure _)
        (SPMF.IsPMF_bind (SPMF.IsPMF_chooseInt _ _ _) fun _ =>
          SPMF.IsPMF_bind (List.genGappedFrom.terminates _ _ _ _) fun _ => SPMF.IsPMF_pure _)
    · exact SPMF.IsPMF_pure _

theorem List.genBoundedGapped.sound_complete :
    IsSoundAndComplete (List.genBoundedGapped k maxLen maxVal)
      (List.boundedGapped k maxLen maxVal) := by
  intro xs
  unfold List.boundedGapped
  cases maxLen with
  | zero => cases xs <;> simp [List.genBoundedGapped]
  | succ n =>
    simp only [List.genBoundedGapped]
    support_simp [List.genGappedFrom_mem_support]
    cases xs with
    | nil => simp; omega
    | cons x ys =>
      simp
      constructor
      · rintro ⟨⟨hx0, hxm⟩, hlen, hub, -, hch⟩
        exact ⟨hlen, ⟨⟨hx0, hxm⟩, fun a ha =>
          ⟨hx0.trans (List.isChain_cons_forall_le (fun _ _ h => h.1) hch a ha), hub a ha⟩⟩, hch⟩
      · rintro ⟨hlen, ⟨⟨hx0, hxm⟩, hall⟩, hch⟩
        exact ⟨⟨hx0, hxm⟩, hlen, fun a ha => (hall a ha).2, hx0.trans hxm, hch⟩

end SortedIntList
