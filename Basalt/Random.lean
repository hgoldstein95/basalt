/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
/-!
# Facts About Core's `randNat`

Lemmas about `Init.Data.Random` that core does not state, shared by the interpretations whose
`choose` is built on `randNat`.
-/

/-- `randNat` stays in `[lo, hi]` for any generator state, so a `choose` built on it needs no
clamp. -/
theorem randNat_mem {gen : Type u} [RandomGen gen] (g : gen) {lo hi : Nat} (h : lo ≤ hi) :
    lo ≤ (randNat g lo hi).1 ∧ (randNat g lo hi).1 ≤ hi := by
  have key : ∀ v, lo + v % (hi - lo + 1) ≤ hi := fun v => by
    have := Nat.mod_lt v (show hi - lo + 1 > 0 by omega); omega
  have : ¬ lo > hi := by omega
  simp only [randNat, this, if_false]
  exact ⟨Nat.le_add_right _ _, key _⟩
