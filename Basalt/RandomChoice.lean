/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
module


/-!
# Abstracting Over Random Choices

This file defines a type class for random choices: a uniform draw from a range and a weighted
choice of an index. `LawfulPick` says an instance's weighted choice is its uniform draw below the
total weight, as every instance a proof reads is.
-/

@[expose] public section

namespace RandomChoice

/-- The total of `w i` over `j ≤ i < n`. -/
@[specialize] def totalFrom (w : Fin n → Nat) (j : Nat) : Nat :=
  if h : j < n then w ⟨j, h⟩ + totalFrom w (j + 1) else 0
termination_by n - j

/-- The first index from `j` at which the running total of `w`, counted from `j`, exceeds `k`. -/
@[specialize] def scanFrom (w : Fin n → Nat) (k j : Nat) : Nat :=
  if h : j < n then if k < w ⟨j, h⟩ then j else scanFrom w (k - w ⟨j, h⟩) (j + 1) else j
termination_by n - j

theorem scanFrom_spec (w : Fin n → Nat) (k j : Nat) (hk : k < totalFrom w j) :
    ∃ h : scanFrom w k j < n, 0 < w ⟨_, h⟩ := by
  rw [totalFrom] at hk
  by_cases hj : j < n
  · rw [dite_eq_left hj] at hk
    by_cases hlt : k < w ⟨j, hj⟩
    · have he : scanFrom w k j = j := by rw [scanFrom, dite_eq_left hj, ite_eq_left hlt]
      rw [he]
      exact ⟨hj, by omega⟩
    · have he : scanFrom w k j = scanFrom w (k - w ⟨j, hj⟩) (j + 1) := by
        rw [scanFrom, dite_eq_left hj, ite_eq_right hlt]
      rw [he]
      exact scanFrom_spec w _ (j + 1) (by omega)
  · rw [dite_eq_right hj] at hk
    omega
termination_by n - j

theorem scanFrom_lt (w : Fin n → Nat) {k j : Nat} (hk : k < totalFrom w j) :
    scanFrom w k j < n := by
  obtain ⟨h, _⟩ := scanFrom_spec w k j hk
  exact h

theorem scanFrom_pos (w : Fin n → Nat) {k j : Nat} (hk : k < totalFrom w j) :
    0 < w ⟨scanFrom w k j, scanFrom_lt w hk⟩ := by
  obtain ⟨_, h⟩ := scanFrom_spec w k j hk
  exact h

theorem totalFrom_pos (w : Fin n → Nat) (i : Fin n) (hi : 0 < w i) (j : Nat) (hj : j ≤ i.val) :
    0 < totalFrom w j := by
  have hjn : j < n := by omega
  rw [totalFrom, dite_eq_left hjn]
  by_cases he : j = i.val
  · subst he
    exact Nat.lt_of_lt_of_le hi (Nat.le_add_right _ _)
  · exact Nat.lt_of_lt_of_le (totalFrom_pos w i hi (j + 1) (by omega)) (Nat.le_add_left _ _)
termination_by n - j

/-- A weighted choice of an index, as a uniform draw below the total weight scanned against the
running total. -/
@[specialize] def pickVia [Monad m] (choose : (lo hi : Nat) → lo ≤ hi → m (ULift {x : Nat // lo ≤ x ∧ x ≤ hi}))
    (n : Nat) (w : Fin n → Nat) (h : ∃ i, 0 < w i) : m (ULift {i : Fin n // 0 < w i}) :=
  choose 0 (totalFrom w 0 - 1) (Nat.zero_le _) >>= fun k =>
    have hk : k.down.val < totalFrom w 0 := by
      obtain ⟨i, hi⟩ := h
      have := totalFrom_pos w i hi 0 (Nat.zero_le _)
      have := k.down.property.2
      omega
    pure ⟨⟨⟨_, scanFrom_lt w hk⟩, scanFrom_pos w hk⟩⟩

end RandomChoice

class RandomChoice (m : Type u → Type v) where
  /-- An inclusive choice over a nonempty range of natural numbers. -/
  choose : (lo hi : Nat) → (h : lo ≤ hi) → m (ULift {x : Nat // lo ≤ x ∧ x ≤ hi})
  /-- A choice of an index below `n` by its weight in `w`. No index of weight `0` is chosen. -/
  pick : (n : Nat) → (w : Fin n → Nat) → (h : ∃ i, 0 < w i) → m (ULift {i : Fin n // 0 < w i})

namespace RandomChoice

/-- The instance whose weighted choice is `pickVia choose`. -/
abbrev ofChoose [Monad m]
    (choose : (lo hi : Nat) → lo ≤ hi → m (ULift {x : Nat // lo ≤ x ∧ x ≤ hi})) :
    RandomChoice m :=
  ⟨choose, pickVia choose⟩

/-- An instance whose weighted choice is its uniform draw below the total weight. An instance that
sees a weighted choice as more than its draw, such as an enumeration, is not one. -/
class LawfulPick (m : Type u → Type v) [Monad m] [RandomChoice m] : Prop where
  pick_eq : ∀ n w h, (pick n w h : m _) = pickVia choose n w h

/-- A weighted binary choice. -/
def coin [Monad m] [RandomChoice m] (r : Rat) : m Bool := do
  if (ULift.down (← choose 0 (r.den - 1) (by simp))).val < r.num then pure true else pure false

end RandomChoice
