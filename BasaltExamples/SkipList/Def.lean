/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt

/-!
# Skip Lists

The tower-height encoding of a skip list's DAG: a `List Entry` in key order, each entry carrying the
height of its tower, so that the level-`i` express lane (`SkipList.lane`) is the sublist of entries
whose towers reach above level `i`. `SkipList.Valid` is the invariant — strictly increasing keys,
towers of height at least one, everything inside the bounds of Dewey, Nichols & Hardekopf's Table I
(max height, max number of elements, max element value; the minimum element value is `0`, which
`Nat` gives for free).
-/

namespace SkipList

/-- One element of a skip list: its key, and the height of its tower. -/
structure Entry where
  val : Nat
  height : Nat
deriving Repr, DecidableEq

/-- The level-`i` express lane: the entries whose towers reach above level `i`. A traversal at that
level visits exactly these, skipping everything between them in one operation. -/
def lane (i : Nat) (xs : List Entry) : List Entry :=
  xs.filter (fun e => decide (i < e.height))

/-- The number of entries whose tower has the maximum height. -/
def tallCount (maxHeight : Nat) (xs : List Entry) : Nat :=
  xs.countP (fun e => e.height == maxHeight)

/-- A skip list is valid within the bounds when it has at most `maxLen` entries, its keys strictly
increase and stay within `[0, maxVal]`, and every tower has height in `[1, maxHeight]`. -/
def Valid (maxHeight maxLen maxVal : Nat) (xs : List Entry) : Prop :=
  xs.length ≤ maxLen ∧
  xs.Pairwise (fun d e => d.val < e.val) ∧
  ∀ e ∈ xs, e.val ≤ maxVal ∧ 1 ≤ e.height ∧ e.height ≤ maxHeight

/-- The top express lane holds exactly the entries `tallCount` counts. -/
theorem length_lane_pred (maxHeight : Nat) (hh : 1 ≤ maxHeight) {xs : List Entry}
    (hb : ∀ e ∈ xs, e.height ≤ maxHeight) :
    (lane (maxHeight - 1) xs).length = tallCount maxHeight xs := by
  induction xs with
  | nil => simp [lane, tallCount]
  | cons e rest ih =>
    have he : e.height ≤ maxHeight := hb e (by simp)
    have hrest : ∀ f ∈ rest, f.height ≤ maxHeight := fun f hf => hb f (by simp [hf])
    simp only [lane, tallCount, List.filter_cons, List.countP_cons, beq_iff_eq,
      decide_eq_true_eq] at *
    split <;> split <;> simp_all
    omega

end SkipList
