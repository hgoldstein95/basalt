/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt.Laws
import Basalt.SizeErasure
import Basalt.Tactic.MassFixpoint
import Basalt.Walk.Complete
import Basalt.Walk.Cost
import Basalt.Walk.Entry
import Basalt.Walk.ExpectedCost
import Basalt.Walk.Mass
import Basalt.Walk.Sound

/-!
# The Laws of QuickCheck's Combinators

Each combinator `Basalt/Combinators.lean` takes from QuickCheck has its soundness, completeness,
termination, and cost from its arguments' laws: one that reads the size has them at every size,
proved by evaluating it there (`size_erasure`) and walking what is left.
-/

open SPMF

variable {α β : Type} {R : α → Prop}

/-- `scale` only changes the size its argument runs at, so every law of `g` at `f n` is one of
`scale f g` at `n`. -/
theorem scale.run (f : Nat → Nat) (g : WithSize SPMF α) (n : Nat) :
    (scale f g).run n = g.run (f n) :=
  rfl

/-! ## Soundness -/

theorem listOf.sound (g : WithSize SPMF α) (n : Nat) (hg : IsSoundFor (g.run n) R) :
    IsSoundFor ((listOf g).run n) fun xs => xs.length ≤ n ∧ ∀ x ∈ xs, R x := by
  rw [IsSoundFor.iff_obs]; simp only [size_erasure]; walk [hg.obs]
  all_goals simp_all

theorem listOf1.sound (g : WithSize SPMF α) (n : Nat) (hg : IsSoundFor (g.run n) R) :
    IsSoundFor ((listOf1 g).run n) fun xs => xs ≠ [] ∧ xs.length ≤ max 1 n ∧ ∀ x ∈ xs, R x := by
  rw [IsSoundFor.iff_obs]; simp only [size_erasure]; walk [hg.obs]
  all_goals grind

theorem growingElements.sound (xs : List α) (hne : xs ≠ []) (n : Nat) :
    IsSoundFor ((growingElements xs hne : WithSize SPMF α).run n) (· ∈ xs) := by
  rw [IsSoundFor.iff_obs]; simp only [size_erasure]; walk
  exact List.mem_of_mem_take ‹_›

theorem sublistOf.sound (xs : List α) : IsSoundFor (sublistOf xs) (·.Sublist xs) := by
  rw [IsSoundFor.iff_obs]; walk
  assumption

theorem shuffle.sound (xs : List α) : IsSoundFor (shuffle xs) (·.Perm xs) := by
  rw [IsSoundFor.iff_obs]; walk
  assumption

/-- A retry loop asks for a fact at every size it might try. -/
theorem suchThatMaybe.sound (g : WithSize SPMF α) (p : α → Bool) (n : Nat)
    (hg : ∀ m, IsSoundFor (g.run m) R) :
    IsSoundFor ((suchThatMaybe g p).run n) fun o => ∀ a, o = some a → p a ∧ R a := by
  rw [IsSoundFor.iff_obs]; simp only [size_erasure]; walk [fun m => (hg m).obs]
  all_goals
    obtain ⟨j, a, -, -, hR, hg⟩ := ‹∀ b, _ = some b → _› _ ‹_›
    rw [Option.guard_eq_some_iff] at hg
    obtain ⟨rfl, hp⟩ := hg
    simp_all

@[inherit_doc suchThatMaybe.sound]
theorem suchThat.sound (g : WithSize SPMF α) (p : α → Bool) (n : Nat)
    (hg : ∀ m, IsSoundFor (g.run m) R) :
    IsSoundFor ((suchThat g p).run n) fun a => p a ∧ R a := by
  rw [IsSoundFor.iff_obs]; simp only [size_erasure]; walk [fun m => (hg m).obs]
  all_goals
    obtain ⟨j, a, -, hR, hg⟩ := ‹∃ j a, _›
    rw [Option.guard_eq_some_iff] at hg
    obtain ⟨rfl, hp⟩ := hg
    simp_all

@[inherit_doc suchThatMaybe.sound]
theorem suchThatMap.sound (g : WithSize SPMF α) (f : α → Option β) (n : Nat)
    (hg : ∀ m, IsSoundFor (g.run m) R) :
    IsSoundFor ((suchThatMap g f).run n) fun b => ∃ a, R a ∧ f a = some b := by
  rw [IsSoundFor.iff_obs]; simp only [size_erasure]; walk [fun m => (hg m).obs]
  obtain ⟨j, a, -, hR, hf⟩ := ‹∃ j a, _›
  exact ⟨a, hR, hf⟩

/-! ## Completeness

A retry loop reaches what its first draw does, at the size it starts from. -/

theorem listOf.complete (g : WithSize SPMF α) (n : Nat) (hg : IsCompleteFor (g.run n) R) :
    IsCompleteFor ((listOf g).run n) fun xs => xs.length ≤ n ∧ ∀ x ∈ xs, R x := by
  rw [IsCompleteFor.iff_obs]; intro xs hxs; simp only [size_erasure]; walk [hg.obs]
  exact hxs

theorem listOf1.complete (g : WithSize SPMF α) (n : Nat) (hg : IsCompleteFor (g.run n) R) :
    IsCompleteFor ((listOf1 g).run n)
      fun xs => xs ≠ [] ∧ xs.length ≤ max 1 n ∧ ∀ x ∈ xs, R x := by
  rw [IsCompleteFor.iff_obs]; intro xs hxs; simp only [size_erasure]; walk [hg.obs]
  exact ⟨xs.length, ⟨List.length_pos_iff.mpr hxs.1, hxs.2.1⟩, rfl, hxs.2.2⟩

theorem growingElements.complete (xs : List α) (hne : xs ≠ []) (n : Nat) :
    IsCompleteFor ((growingElements xs hne : WithSize SPMF α).run n)
      (· ∈ xs.take (max 1 ((logRound n + 1) * xs.length / logRound 100))) := by
  rw [IsCompleteFor.iff_obs]; intro a ha; simp only [size_erasure]; walk
  exact ha

theorem sublistOf.complete (xs : List α) : IsCompleteFor (sublistOf xs) (·.Sublist xs) := by
  rw [IsCompleteFor.iff_obs]; intro ys hys; walk
  exact hys

theorem shuffle.complete (xs : List α) (hn : xs.length ≤ 2 ^ 63) :
    IsCompleteFor (shuffle xs) (·.Perm xs) := by
  rw [IsCompleteFor.iff_obs]; intro ys hys; walk
  exact ⟨hn, hys⟩

theorem suchThatMaybe.complete (g : WithSize SPMF α) (p : α → Bool) (n : Nat)
    (hg : IsCompleteFor (g.run n) R) :
    IsCompleteFor ((suchThatMaybe g p).run n) fun o => ∃ a, o = some a ∧ p a ∧ R a := by
  rw [IsCompleteFor.iff_obs]; intro o ho; simp only [size_erasure]; walk [hg.obs]
  obtain ⟨a, rfl, hp, hR⟩ := ho
  exact ⟨a, ⟨a, hR, Option.guard_eq_some_iff.mpr ⟨rfl, hp⟩⟩, rfl⟩

theorem suchThat.complete (g : WithSize SPMF α) (p : α → Bool) (n : Nat)
    (hg : IsCompleteFor (g.run n) R) :
    IsCompleteFor ((suchThat g p).run n) fun a => p a ∧ R a := by
  rw [IsCompleteFor.iff_obs]; intro a ha; simp only [size_erasure]; walk [hg.obs]
  exact ⟨a, ha.2, Option.guard_eq_some_iff.mpr ⟨rfl, ha.1⟩⟩

theorem suchThatMap.complete (g : WithSize SPMF α) (f : α → Option β) (n : Nat)
    (hg : IsCompleteFor (g.run n) R) :
    IsCompleteFor ((suchThatMap g f).run n) fun b => ∃ a, R a ∧ f a = some b := by
  rw [IsCompleteFor.iff_obs]; intro b hb; simp only [size_erasure]; walk [hg.obs]
  exact hb

/-! ## Termination -/

theorem listOf.terminates (g : WithSize SPMF α) (n : Nat)
    (hg : IsAlmostSurelyTerminating (g.run n)) :
    IsAlmostSurelyTerminating ((listOf g).run n) := by
  rw [IsAlmostSurelyTerminating.iff_obs]; simp only [size_erasure]; walk [hg.obs]
  simp

theorem listOf1.terminates (g : WithSize SPMF α) (n : Nat)
    (hg : IsAlmostSurelyTerminating (g.run n)) :
    IsAlmostSurelyTerminating ((listOf1 g).run n) := by
  rw [IsAlmostSurelyTerminating.iff_obs]; simp only [size_erasure]; walk [hg.obs]
  exact le_rfl

theorem growingElements.terminates (xs : List α) (hne : xs ≠ []) (n : Nat) :
    IsAlmostSurelyTerminating ((growingElements xs hne : WithSize SPMF α).run n) := by
  rw [IsAlmostSurelyTerminating.iff_obs]; simp only [size_erasure]; walk
  exact le_rfl

theorem sublistOf.terminates (xs : List α) :
    IsAlmostSurelyTerminating (sublistOf xs : SPMF (List α)) := by
  rw [IsAlmostSurelyTerminating.iff_obs]; walk
  exact le_rfl

theorem shuffle.terminates (xs : List α) :
    IsAlmostSurelyTerminating (shuffle xs : SPMF (List α)) := by
  rw [IsAlmostSurelyTerminating.iff_obs]; walk
  exact le_rfl

theorem suchThatMaybe.terminates (g : WithSize SPMF α) (p : α → Bool) (n : Nat)
    (hg : ∀ m, IsAlmostSurelyTerminating (g.run m)) :
    IsAlmostSurelyTerminating ((suchThatMaybe g p).run n) := by
  rw [IsAlmostSurelyTerminating.iff_obs]; simp only [size_erasure]; walk [fun m => (hg m).obs]
  simp

/-- The loop terminates when every size it tries does, and rejects with a chance at most `r < 1`:
`p`'s own rejections, for `suchThat`. -/
theorem suchThat.terminates (g : WithSize SPMF α) (p : α → Bool) (n : Nat) (r : ENNReal)
    (hr1 : r < 1) (hg : ∀ m, n ≤ m → IsAlmostSurelyTerminating (g.run m))
    (hr : ∀ m, n ≤ m → expectObs.spec (g.run m) (fun a => if p a then 0 else 1) ≤ r) :
    IsAlmostSurelyTerminating ((suchThat g p).run n) := by
  rw [IsAlmostSurelyTerminating.iff_obs]; simp only [size_erasure]
  walk [fun m hm => (hg m hm).obs, hr]
  simp [hr1]

@[inherit_doc suchThat.terminates]
theorem suchThatMap.terminates (g : WithSize SPMF α) (f : α → Option β) (n : Nat) (r : ENNReal)
    (hr1 : r < 1) (hg : ∀ m, n ≤ m → IsAlmostSurelyTerminating (g.run m))
    (hr : ∀ m, n ≤ m → expectObs.spec (g.run m) (fun a => if (f a).isSome then 0 else 1) ≤ r) :
    IsAlmostSurelyTerminating ((suchThatMap g f).run n) := by
  rw [IsAlmostSurelyTerminating.iff_obs]; simp only [size_erasure]
  walk [fun m hm => (hg m hm).obs, hr]
  simp [hr1]

/-! ## Cost -/

theorem listOf.cost_bounded (g : WithSize SPMF.Cost α) (c : α → Nat) (n : Nat)
    (hg : IsCostBounded (g.run n) c) :
    IsCostBounded ((listOf g).run n) fun xs => 1 + (xs.map c).sum := by
  rw [IsCostBounded.iff_obs]; simp only [size_erasure]; walk [hg.obs]
  assumption

theorem listOf1.cost_bounded (g : WithSize SPMF.Cost α) (c : α → Nat) (n : Nat)
    (hg : IsCostBounded (g.run n) c) :
    IsCostBounded ((listOf1 g).run n) fun xs => 1 + (xs.map c).sum := by
  rw [IsCostBounded.iff_obs]; simp only [size_erasure]; walk [hg.obs]
  omega

theorem growingElements.cost_bounded (xs : List α) (hne : xs ≠ []) (n : Nat) :
    IsCostBounded ((growingElements xs hne : WithSize SPMF.Cost α).run n) fun _ => 1 := by
  rw [IsCostBounded.iff_obs]; simp only [size_erasure]; walk
  exact le_rfl

theorem sublistOf.cost_bounded (xs : List α) :
    IsCostBounded (sublistOf xs) fun _ => xs.length := by
  rw [IsCostBounded.iff_obs]; walk
  assumption

theorem shuffle.cost_bounded (xs : List α) : IsCostBounded (shuffle xs) fun _ => xs.length := by
  rw [IsCostBounded.iff_obs]; walk
  assumption

/-- One draw per size tried, and `suchThatMaybe` tries `n + 1` of them. -/
theorem suchThatMaybe.cost_bounded (g : WithSize SPMF.Cost α) (p : α → Bool) (K n : Nat)
    (hg : ∀ m, IsCostBounded (g.run m) fun _ => K) :
    IsCostBounded ((suchThatMaybe g p).run n) fun _ => (n + 1) * K := by
  rw [IsCostBounded.iff_obs]; simp only [size_erasure]; walk [fun m => (hg m).obs]
  simpa using ‹_ ≤ ∑ i ∈ Finset.range (n + 1), K›

/-- The loop has no worst case: its expected cost is the rejection sampler's, `C / (1 - r)`. -/
theorem suchThat.cost (g : WithSize SPMF.Cost α) (p : α → Bool) (n : Nat) (C r : ENNReal)
    (hg : ∀ m, n ≤ m → IsExpectedCostBounded (g.run m) C)
    (hr : ∀ m, n ≤ m →
      SPMF.Cost.expectObs.spec (g.run m) (fun a _ => if p a then 0 else 1) ≤ r) :
    IsExpectedCostBounded ((suchThat g p).run n) (C / (1 - r)) := by
  rw [IsExpectedCostBounded.iff_obs]; simp only [size_erasure]
  walk [fun m hm => (hg m hm).obs, hr]
  simp

@[inherit_doc suchThat.cost]
theorem suchThatMap.cost (g : WithSize SPMF.Cost α) (f : α → Option β) (n : Nat) (C r : ENNReal)
    (hg : ∀ m, n ≤ m → IsExpectedCostBounded (g.run m) C)
    (hr : ∀ m, n ≤ m →
      SPMF.Cost.expectObs.spec (g.run m) (fun a _ => if (f a).isSome then 0 else 1) ≤ r) :
    IsExpectedCostBounded ((suchThatMap g f).run n) (C / (1 - r)) := by
  rw [IsExpectedCostBounded.iff_obs]; simp only [size_erasure]
  walk [fun m hm => (hg m hm).obs, hr]
  simp
