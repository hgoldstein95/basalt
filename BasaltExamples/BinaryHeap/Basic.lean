/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt
import BasaltExamples.BinaryHeap.Def

open RandomChoice

/-!
# Bounded-Exhaustive Array Heaps

`genHeap maxSize maxVal` generates every array-backed binary min-heap with at most `maxSize`
elements and values in `[0, maxVal]`. Positions are filled from the last index down, so the two
children of a position are already fixed when it is drawn and its whole range is admissible.
-/

namespace BinaryHeap

/-- The heap condition at a single index, as an unconditional statement about `a[i]?`. -/
private def HeapAt (maxVal : Nat) (a : List Nat) (i : Nat) : Prop :=
  ∀ p ∈ a[i]?, p ≤ maxVal ∧ (∀ l ∈ a[2 * i + 1]?, p ≤ l) ∧ (∀ r ∈ a[2 * i + 2]?, p ≤ r)

private theorem isHeap_iff_heapAt {maxVal : Nat} {a : List Nat} :
    IsHeap maxVal a ↔ ∀ i, HeapAt maxVal a i := by
  constructor
  · rintro ⟨hb, hc⟩ i p hp
    exact ⟨hb p (List.mem_iff_getElem?.mpr ⟨i, hp⟩), (hc i p hp).1, (hc i p hp).2⟩
  · intro h
    refine ⟨fun x hx => ?_, fun i p hp => ⟨(h i p hp).2.1, (h i p hp).2.2⟩⟩
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hx
    exact (h i x hi).1

/-- The largest value admissible at index `k` once `acc`, the array from index `k + 1` on, is
fixed: `maxVal`, capped by whichever of the two children exist. -/
private def childBound (maxVal : Nat) (acc : List Nat) (k : Nat) : Nat :=
  min maxVal (min (acc[k]?.getD maxVal) (acc[k + 1]?.getD maxVal))

private theorem le_childBound_iff {maxVal x : Nat} {acc : List Nat} {k : Nat} :
    x ≤ childBound maxVal acc k ↔
      x ≤ maxVal ∧ (∀ l ∈ acc[k]?, x ≤ l) ∧ (∀ r ∈ acc[k + 1]?, x ≤ r) := by
  unfold childBound
  cases hl : acc[k]? <;> cases hr : acc[k + 1]? <;> simp [and_comm]

/-- Fills indices `k - 1, …, 0` in front of `acc`, drawing each position from `[0, childBound]`. -/
def genFrom [Gen G] (maxVal : Nat) : Nat → List Nat → G (List Nat)
  | 0, acc => pure acc
  | k + 1, acc => do
    let x ← chooseNat 0 (childBound maxVal acc k) (Nat.zero_le _)
    genFrom maxVal k (x :: acc)

private theorem getElem?_drop_zero (l : List Nat) (n : Nat) : (l.drop n)[0]? = l[n]? := by
  rw [List.getElem?_drop]
  simp

private theorem genFrom_mem_support (maxVal : Nat) (k : Nat) :
    ∀ (acc a : List Nat), a ∈ SPMF.support (genFrom maxVal k acc) ↔
      a.length = k + acc.length ∧ a.drop k = acc ∧ ∀ i < k, HeapAt maxVal a i := by
  induction k with
  | zero =>
    intro acc a
    rw [genFrom]
    simp only [SPMF.mem_support_pure_iff, Nat.zero_add, List.drop_zero, Nat.not_lt_zero,
      false_implies, forall_const, and_true]
    exact ⟨fun h => ⟨by rw [h], h⟩, fun h => h.2⟩
  | succ k ih =>
    intro acc a
    rw [genFrom]
    support_simp [ih]
    constructor
    · rintro ⟨x, ⟨-, hx⟩, hlen, hdrop, hall⟩
      have hxk : a[k]? = some x := by
        rw [← getElem?_drop_zero, hdrop]; rfl
      have hdrop' : a.drop (k + 1) = acc := by
        rw [← List.tail_drop, hdrop]; rfl
      refine ⟨by simp at hlen ⊢; omega, hdrop', fun i hi => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · exact hall i hi
      · intro p hp
        rw [hxk] at hp
        obtain rfl : p = x := by simpa using hp.symm
        obtain ⟨h1, h2, h3⟩ := le_childBound_iff.mp hx
        refine ⟨h1, fun l hl => h2 l ?_, fun r hr => h3 r ?_⟩
        · rw [← hdrop', List.getElem?_drop]
          rw [show i + 1 + i = 2 * i + 1 by omega]; exact hl
        · rw [← hdrop', List.getElem?_drop]
          rw [show i + 1 + (i + 1) = 2 * i + 2 by omega]; exact hr
    · rintro ⟨hlen, hdrop, hall⟩
      have hk : k < a.length := by omega
      refine ⟨a[k], ⟨Nat.zero_le _, ?_⟩, ?_, ?_, fun i hi => hall i (by omega)⟩
      · refine le_childBound_iff.mpr ?_
        obtain ⟨h1, h2, h3⟩ := hall k (by omega) a[k] (by simp)
        refine ⟨h1, fun l hl => h2 l ?_, fun r hr => h3 r ?_⟩
        · rw [← hdrop, List.getElem?_drop] at hl
          rw [show k + 1 + k = 2 * k + 1 by omega] at hl; exact hl
        · rw [← hdrop, List.getElem?_drop] at hr
          rw [show k + 1 + (k + 1) = 2 * k + 2 by omega] at hr; exact hr
      · simp; omega
      · rw [List.drop_eq_getElem_cons hk, hdrop]

/-- Generates every heap of at most `maxSize` values drawn from `[0, maxVal]`. -/
def genHeap [Gen G] (maxSize maxVal : Nat) : G (List Nat) := do
  let n ← chooseNat 0 maxSize (Nat.zero_le _)
  genFrom maxVal n []

theorem genHeap_mem_support {maxSize maxVal : Nat} {a : List Nat} :
    a ∈ SPMF.support (genHeap maxSize maxVal) ↔ a.length ≤ maxSize ∧ IsHeap maxVal a := by
  rw [genHeap]
  support_simp [genFrom_mem_support]
  constructor
  · rintro ⟨n, ⟨-, hn⟩, hlen, -, hall⟩
    simp only [List.length_nil, Nat.add_zero] at hlen
    subst hlen
    refine ⟨hn, isHeap_iff_heapAt.mpr fun i => ?_⟩
    by_cases hi : i < a.length
    · exact hall i hi
    · intro p hp
      rw [List.getElem?_eq_none (by omega)] at hp
      exact absurd hp.symm (by simp)
  · rintro ⟨hle, hheap⟩
    exact ⟨a.length, ⟨Nat.zero_le _, hle⟩, by simp, by simp, fun i _ => isHeap_iff_heapAt.mp hheap i⟩

theorem genHeap.sound_complete :
    IsSoundAndComplete (genHeap maxSize maxVal)
      (fun a => a.length ≤ maxSize ∧ IsHeap maxVal a) :=
  fun _ => genHeap_mem_support

end BinaryHeap
