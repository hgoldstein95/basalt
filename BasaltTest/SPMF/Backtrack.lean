/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Segev Elazar Mittelman
-/
import Basalt

/-!
# Support of Backtracking Generators

Each theorem of `Basalt/SPMF/Backtrack.lean` applied to a concrete `backtrack`, and the shape of
argument a generator derived from an inductive relation reduces to: branches that only succeed on
values satisfying `P` make a `backtrack` that only succeeds on them.
-/

open BacktrackGen

/-- A retry over a failing branch and two succeeding ones. -/
noncomputable def pool : List (Nat × (Unit → BacktrackGen SPMF Nat)) :=
  [(2, fun _ => refute), (1, fun _ => pure 3), (1, fun _ => pure 5)]

-- Both successes are reachable, and nothing else is.
example : Outcome.ok 3 ∈ (backtrack pool).run.support :=
  mem_support_backtrack_of_branch pool (1, fun _ => pure 3) (by simp [pool]) (by decide) 3 (by simp)

example (a : Nat) (h : Outcome.ok a ∈ (backtrack pool).run.support) : a = 3 ∨ a = 5 := by
  obtain ⟨p, hp, -, hpa⟩ := mem_support_backtrack_ok pool a h
  simp only [pool, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl <;> simp at hpa <;> omega

-- One branch always succeeds, so the whole cannot fail — in particular it never refutes.
example : NeverFails (backtrack pool) :=
  neverFails_backtrack pool (1, fun _ => pure 3) (by simp [pool]) (by decide) (neverFails_pure 3)

example : Outcome.refuted ∉ (backtrack pool).run.support := fun h => by
  have := mem_support_backtrack_refuted pool h (1, fun _ => pure 3) (by simp [pool])
  simp at this

-- Every branch refutes, so the whole can.
example : Outcome.refuted ∈ (backtrack [(1, fun _ => (refute : BacktrackGen SPMF Nat)),
    (4, fun _ => refute)]).run.support :=
  mem_support_backtrack_refuted_of_all _ (by simp) (by simp)

-- Wrapping a truncated disjunction keeps its successes and removes its refutation.
example : Outcome.ok 3 ∈ (refutedToExhausted (backtrack pool)).run.support :=
  (mem_support_refutedToExhausted_ok_iff _ 3).mpr
    (mem_support_backtrack_of_branch pool (1, fun _ => pure 3) (by simp [pool]) (by decide) 3 (by simp))

example : Outcome.refuted ∉ (refutedToExhausted (backtrack pool)).run.support :=
  not_mem_support_refutedToExhausted _

/-- Soundness of a derived generator reduces to soundness of each branch. -/
example {α : Type} (P : α → Prop) (gs : List (Nat × (Unit → BacktrackGen SPMF α)))
    (hbranch : ∀ p ∈ gs, ∀ a, Outcome.ok a ∈ (p.2 ()).run.support → P a) :
    ∀ a, Outcome.ok a ∈ (backtrack gs).run.support → P a := fun a h =>
  let ⟨p, hp, _, hpa⟩ := mem_support_backtrack_ok gs a h
  hbranch p hp a hpa

-- The base instances reach every value.
example (n : Nat) : n ∈ (Basalt.Nat.arbitraryGen : SPMF Nat).support := Basalt.Nat.mem_support_arbitraryGen n
example (b : Bool) : b ∈ (Basalt.Arbitrary.arbitrary : SPMF Bool).support :=
  Basalt.Bool.arbitrary.sound_complete.complete b trivial
