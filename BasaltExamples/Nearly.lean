/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt

/-!
# Nearly Valid Values

A value is nearly `P` when it is not `P` and one edit makes it so (`Repairs`), and `genNearly`
generates such values with an edit that repairs them, from a generator for `P` and a generator of
edits: mutate a valid value, and retry until the result is invalid. Its laws are proved here once,
from laws of its arguments; an instance supplies the edits and their generator
(`BasaltExamples/BST/Nearly.lean`).
-/

open RandomChoice
open scoped ENNReal

/-- `e` repairs `a`: `a` is not `P`, and applying `e` to it gives a value that is. -/
def Repairs (apply : ε → α → Option α) (P : α → Prop) (a : α) (e : ε) : Prop :=
  ¬ P a ∧ ∃ b, apply e a = some b ∧ P b

/-- Draws a value from `gen` and edits it with `mutate`, which returns the result with an edit that
undoes its own, and retries until `valid` rejects the result. -/
def genNearly [Gen G] (gen : G α) (mutate : α → G (α × ε)) (valid : α → Bool) : G (α × ε) :=
  suchThat (do let b ← gen; mutate b) (fun c => !valid c.1)

section laws

variable {α ε : Type} {gen : SPMF α} {mutate : α → SPMF (α × ε)} {valid : α → Bool}
  {apply : ε → α → Option α} {P U : α → Prop}

/-- Rejection sampling terminates when its source does and reaches a value that is accepted. -/
theorem SPMF.isAlmostSurelyTerminating_suchThat_of_mem_support {g : SPMF α} {p : α → Bool} {a : α}
    (hg : IsAlmostSurelyTerminating g) (ha : a ∈ g.support) (hp : p a = true) :
    IsAlmostSurelyTerminating (suchThat g p) := by
  classical
  refine SPMF.isAlmostSurelyTerminating_suchThat (r := 1 - SPMF.prob g {a}) hg ?_
    (ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero (SPMF.mem_support_iff_prob_pos.mp ha).ne')
  have hsum : SPMF.expect g (fun x => if p x then 0 else 1) + SPMF.prob g {a} ≤ 1 := by
    rw [SPMF.prob, ← SPMF.expect_add]
    refine (SPMF.expect_mono fun x => ?_).trans ((SPMF.expect_one g).trans_le (SPMF.mass_le_one g))
    by_cases hx : x = a
    · simp [hx, hp]
    · simp [hx]; split <;> simp
  exact ENNReal.le_sub_of_add_le_right
    (ne_top_of_le_ne_top ENNReal.one_ne_top ((SPMF.prob_le_mass g _).trans (SPMF.mass_le_one g)))
    hsum

/-- `U` is what the mutants are drawn from: the invalid values a repair is asked of. `mutate` must
reach every invalid value of `U` with each of its repairs, and no valid one, so an edit that never
breaks validity is one it can skip. -/
theorem genNearly.sound_complete (hvalid : ∀ a, valid a = true ↔ P a)
    (hgen : IsSoundAndComplete gen P)
    (hsound : ∀ b, P b → IsSoundFor (mutate b) fun c => U c.1 ∧ apply c.2 c.1 = some b)
    (hcomplete : ∀ b a e, P b → U a → ¬ P a → apply e a = some b → (a, e) ∈ (mutate b).support) :
    IsSoundAndComplete (genNearly gen mutate valid) fun c => U c.1 ∧ Repairs apply P c.1 c.2 := by
  have hreject : ∀ a, (!valid a) = true ↔ ¬ P a := fun a => by simp [← hvalid]
  refine ⟨fun c hc => ?_, fun c ⟨hU, hna, b, he, hb⟩ => ?_⟩
  · obtain ⟨⟨b, hb, hcb⟩, hv⟩ :=
      (SPMF.mem_support_suchThat.trans (and_congr_left' SPMF.mem_support_bind_iff)).mp hc
    have hPb := hgen.sound b hb
    obtain ⟨hU, he⟩ := hsound b hPb c hcb
    exact ⟨hU, (hreject c.1).mp hv, b, he, hPb⟩
  · exact SPMF.mem_support_suchThat.mpr ⟨SPMF.mem_support_bind_iff.mpr
      ⟨b, hgen.complete b hb, hcomplete b c.1 c.2 hb hU hna he⟩, (hreject c.1).mpr hna⟩

/-- Termination needs no bound on how often a mutant is still valid: one nearly valid value is
enough, since completeness puts it in reach of every draw. -/
theorem genNearly.terminates (hvalid : ∀ a, valid a = true ↔ P a) (hgen : IsCompleteFor gen P)
    (hcomplete : ∀ b a e, P b → U a → ¬ P a → apply e a = some b → (a, e) ∈ (mutate b).support)
    (hgt : IsAlmostSurelyTerminating gen) (hmt : ∀ b, IsAlmostSurelyTerminating (mutate b))
    {a : α} {e : ε} (hU : U a) (ha : Repairs apply P a e) :
    IsAlmostSurelyTerminating (genNearly gen mutate valid) := by
  obtain ⟨hna, b, he, hb⟩ := ha
  refine SPMF.isAlmostSurelyTerminating_suchThat_of_mem_support (a := (a, e)) ?_
    (SPMF.mem_support_bind_iff.mpr ⟨b, hgen b hb, hcomplete b a e hb hU hna he⟩)
    (by simpa [← hvalid] using hna)
  rw [IsAlmostSurelyTerminating.iff_obs]
  walk [hgt.obs, fun b => (hmt b).obs]
  simp

end laws
