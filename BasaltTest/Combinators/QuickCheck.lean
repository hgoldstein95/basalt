/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt

/-!
# QuickCheck's Combinators, at Every Size

Pins `Basalt/Combinators/QuickCheck.lean` and its rules: each combinator, evaluated at a size by
`size_erasure`, has its soundness, completeness, termination, and cost proved by `walk` from its
arguments' laws, leaving only logic and arithmetic.
-/

open SPMF QuickCheck

namespace QuickCheckTest

variable {α β : Type} (n : Nat) {R : α → Prop}

/-! ## Soundness -/

example (f : Nat → Nat) (g : WithSize SPMF α) (hg : ∀ m, IsSoundFor (g m) R) :
    IsSoundFor ((scale f g : WithSize SPMF α) n) R := by
  rw [IsSoundFor.iff_obs]; simp only [size_erasure]; walk [(hg (f n)).obs]
  assumption

example (g : WithSize SPMF α) (hg : ∀ m, IsSoundFor (g m) R) :
    IsSoundFor ((QuickCheck.listOf g : WithSize SPMF (List α)) n)
      fun xs => xs.length ≤ n ∧ ∀ x ∈ xs, R x := by
  rw [IsSoundFor.iff_obs]; simp only [size_erasure]; walk [(hg n).obs]
  all_goals simp_all

example (g : WithSize SPMF α) (hg : ∀ m, IsSoundFor (g m) R) :
    IsSoundFor ((listOf1 g : WithSize SPMF (List α)) n)
      fun xs => xs ≠ [] ∧ xs.length ≤ max 1 n ∧ ∀ x ∈ xs, R x := by
  rw [IsSoundFor.iff_obs]; simp only [size_erasure]; walk [(hg n).obs]
  all_goals grind

example (xs : List α) (hne : xs ≠ []) :
    IsSoundFor ((growingElements xs hne : WithSize SPMF α) n) (· ∈ xs) := by
  rw [IsSoundFor.iff_obs]; simp only [size_erasure]; walk
  exact List.mem_of_mem_take ‹_›

example (xs : List α) :
    IsSoundFor ((sublistOf xs : WithSize SPMF (List α)) n) (·.Sublist xs) := by
  rw [IsSoundFor.iff_obs]; simp only [size_erasure]; walk
  assumption

example (xs : List α) : IsSoundFor ((shuffle xs : WithSize SPMF (List α)) n) (·.Perm xs) := by
  rw [IsSoundFor.iff_obs]; simp only [size_erasure]; walk
  assumption

/-- The retry loops ask for a fact at every size they might try. -/
example (g : WithSize SPMF α) (p : α → Bool) (hg : ∀ m, IsSoundFor (g m) R) :
    IsSoundFor ((suchThatMaybe g p : WithSize SPMF (Option α)) n)
      fun o => ∀ a, o = some a → p a ∧ R a := by
  rw [IsSoundFor.iff_obs]; simp only [size_erasure]; walk [fun m => (hg m).obs]
  all_goals
    obtain ⟨j, a, -, -, hR, hg⟩ := ‹∀ b, _ = some b → _› _ ‹_›
    rw [Option.guard_eq_some_iff] at hg
    obtain ⟨rfl, hp⟩ := hg
    simp_all

example (g : WithSize SPMF α) (p : α → Bool) (hg : ∀ m, IsSoundFor (g m) R) :
    IsSoundFor ((QuickCheck.suchThat g p : WithSize SPMF α) n) fun a => p a ∧ R a := by
  rw [IsSoundFor.iff_obs]; simp only [size_erasure]; walk [fun m => (hg m).obs]
  all_goals
    obtain ⟨j, a, -, hR, hg⟩ := ‹∃ j a, _›
    rw [Option.guard_eq_some_iff] at hg
    obtain ⟨rfl, hp⟩ := hg
    simp_all

example (g : WithSize SPMF α) (f : α → Option β) (hg : ∀ m, IsSoundFor (g m) R) :
    IsSoundFor ((suchThatMap g f : WithSize SPMF β) n) fun b => ∃ a, R a ∧ f a = some b := by
  rw [IsSoundFor.iff_obs]; simp only [size_erasure]; walk [fun m => (hg m).obs]
  obtain ⟨j, a, -, hR, hf⟩ := ‹∃ j a, _›
  exact ⟨a, hR, hf⟩

/-! ## Completeness

A retry loop reaches what its first draw does, at the size it starts from. -/

example (g : WithSize SPMF α) (hg : ∀ m, IsCompleteFor (g m) R) :
    IsCompleteFor ((QuickCheck.listOf g : WithSize SPMF (List α)) n)
      fun xs => xs.length ≤ n ∧ ∀ x ∈ xs, R x := by
  rw [IsCompleteFor.iff_obs]; intro xs hxs; simp only [size_erasure]; walk [(hg n).obs]
  exact hxs

example (g : WithSize SPMF α) (hg : ∀ m, IsCompleteFor (g m) R) :
    IsCompleteFor ((listOf1 g : WithSize SPMF (List α)) n)
      fun xs => xs ≠ [] ∧ xs.length ≤ max 1 n ∧ ∀ x ∈ xs, R x := by
  rw [IsCompleteFor.iff_obs]; intro xs hxs; simp only [size_erasure]; walk [(hg n).obs]
  exact ⟨xs.length, ⟨List.length_pos_iff.mpr hxs.1, hxs.2.1⟩, rfl, hxs.2.2⟩

example (xs : List α) (hne : xs ≠ []) :
    IsCompleteFor ((growingElements xs hne : WithSize SPMF α) n)
      (· ∈ xs.take (max 1 ((logRound n + 1) * xs.length / logRound 100))) := by
  rw [IsCompleteFor.iff_obs]; intro a ha; simp only [size_erasure]; walk
  exact ha

example (xs : List α) :
    IsCompleteFor ((sublistOf xs : WithSize SPMF (List α)) n) (·.Sublist xs) := by
  rw [IsCompleteFor.iff_obs]; intro ys hys; simp only [size_erasure]; walk
  exact hys

example (xs : List α) (hn : xs.length ≤ 2 ^ 64) :
    IsCompleteFor ((shuffle xs : WithSize SPMF (List α)) n) (·.Perm xs) := by
  rw [IsCompleteFor.iff_obs]; intro ys hys; simp only [size_erasure]; walk
  exact ⟨hn, hys⟩

example (g : WithSize SPMF α) (p : α → Bool) (hg : IsCompleteFor (g n) R) :
    IsCompleteFor ((suchThatMaybe g p : WithSize SPMF (Option α)) n)
      fun o => ∃ a, o = some a ∧ p a ∧ R a := by
  rw [IsCompleteFor.iff_obs]; intro o ho; simp only [size_erasure]; walk [hg.obs]
  obtain ⟨a, rfl, hp, hR⟩ := ho
  exact ⟨a, ⟨a, hR, Option.guard_eq_some_iff.mpr ⟨rfl, hp⟩⟩, rfl⟩

example (g : WithSize SPMF α) (p : α → Bool) (hg : IsCompleteFor (g n) R) :
    IsCompleteFor ((QuickCheck.suchThat g p : WithSize SPMF α) n) fun a => p a ∧ R a := by
  rw [IsCompleteFor.iff_obs]; intro a ha; simp only [size_erasure]; walk [hg.obs]
  exact ⟨a, ha.2, Option.guard_eq_some_iff.mpr ⟨rfl, ha.1⟩⟩

example (g : WithSize SPMF α) (f : α → Option β) (hg : IsCompleteFor (g n) R) :
    IsCompleteFor ((suchThatMap g f : WithSize SPMF β) n) fun b => ∃ a, R a ∧ f a = some b := by
  rw [IsCompleteFor.iff_obs]; intro b hb; simp only [size_erasure]; walk [hg.obs]
  exact hb

/-! ## Termination -/

example (g : WithSize SPMF α) (hg : ∀ m, IsAlmostSurelyTerminating (g m)) :
    IsAlmostSurelyTerminating ((QuickCheck.listOf g : WithSize SPMF (List α)) n) := by
  rw [IsAlmostSurelyTerminating.iff_obs]; simp only [size_erasure]; walk [(hg n).obs]
  simp

example (g : WithSize SPMF α) (hg : ∀ m, IsAlmostSurelyTerminating (g m)) :
    IsAlmostSurelyTerminating ((listOf1 g : WithSize SPMF (List α)) n) := by
  rw [IsAlmostSurelyTerminating.iff_obs]; simp only [size_erasure]; walk [(hg n).obs]
  exact le_rfl

example (xs : List α) (hne : xs ≠ []) :
    IsAlmostSurelyTerminating ((growingElements xs hne : WithSize SPMF α) n) := by
  rw [IsAlmostSurelyTerminating.iff_obs]; simp only [size_erasure]; walk
  exact le_rfl

example (xs : List α) :
    IsAlmostSurelyTerminating ((sublistOf xs : WithSize SPMF (List α)) n) := by
  rw [IsAlmostSurelyTerminating.iff_obs]; simp only [size_erasure]; walk
  exact le_rfl

example (xs : List α) : IsAlmostSurelyTerminating ((shuffle xs : WithSize SPMF (List α)) n) := by
  rw [IsAlmostSurelyTerminating.iff_obs]; simp only [size_erasure]; walk
  exact le_rfl

example (g : WithSize SPMF α) (p : α → Bool) (hg : ∀ m, IsAlmostSurelyTerminating (g m)) :
    IsAlmostSurelyTerminating ((suchThatMaybe g p : WithSize SPMF (Option α)) n) := by
  rw [IsAlmostSurelyTerminating.iff_obs]; simp only [size_erasure]; walk [fun m => (hg m).obs]
  simp

/-- The loop terminates when every size it tries does, and rejects with a chance at most `r < 1`:
`p`'s own rejections, for `suchThat`. -/
example (g : WithSize SPMF α) (p : α → Bool) (r : ENNReal) (hr1 : r < 1)
    (hg : ∀ m, n ≤ m → IsAlmostSurelyTerminating (g m))
    (hr : ∀ m, n ≤ m → expectObs.spec (g m) (fun a => if p a then 0 else 1) ≤ r) :
    IsAlmostSurelyTerminating ((QuickCheck.suchThat g p : WithSize SPMF α) n) := by
  rw [IsAlmostSurelyTerminating.iff_obs]; simp only [size_erasure]
  walk [fun m hm => (hg m hm).obs, hr]
  simp [hr1]

example (g : WithSize SPMF α) (f : α → Option β) (r : ENNReal) (hr1 : r < 1)
    (hg : ∀ m, n ≤ m → IsAlmostSurelyTerminating (g m))
    (hr : ∀ m, n ≤ m → expectObs.spec (g m) (fun a => if (f a).isSome then 0 else 1) ≤ r) :
    IsAlmostSurelyTerminating ((suchThatMap g f : WithSize SPMF β) n) := by
  rw [IsAlmostSurelyTerminating.iff_obs]; simp only [size_erasure]
  walk [fun m hm => (hg m hm).obs, hr]
  simp [hr1]

/-! ## Cost -/

example (g : WithSize SPMF.Cost α) (c : α → Nat) (hg : ∀ m, IsCostBounded (g m) c) :
    IsCostBounded ((QuickCheck.listOf g : WithSize SPMF.Cost (List α)) n)
      fun xs => 1 + (xs.map c).sum := by
  rw [IsCostBounded.iff_obs]; simp only [size_erasure]; walk [(hg n).obs]
  assumption

example (g : WithSize SPMF.Cost α) (c : α → Nat) (hg : ∀ m, IsCostBounded (g m) c) :
    IsCostBounded ((listOf1 g : WithSize SPMF.Cost (List α)) n)
      fun xs => 1 + (xs.map c).sum := by
  rw [IsCostBounded.iff_obs]; simp only [size_erasure]; walk [(hg n).obs]
  omega

example (xs : List α) (hne : xs ≠ []) :
    IsCostBounded ((growingElements xs hne : WithSize SPMF.Cost α) n) fun _ => 1 := by
  rw [IsCostBounded.iff_obs]; simp only [size_erasure]; walk
  exact le_rfl

example (xs : List α) :
    IsCostBounded ((sublistOf xs : WithSize SPMF.Cost (List α)) n) fun _ => xs.length := by
  rw [IsCostBounded.iff_obs]; simp only [size_erasure]; walk
  assumption

example (xs : List α) :
    IsCostBounded ((shuffle xs : WithSize SPMF.Cost (List α)) n) fun _ => xs.length := by
  rw [IsCostBounded.iff_obs]; simp only [size_erasure]; walk
  assumption

/-- One draw per size tried, and `suchThatMaybe` tries `n + 1` of them. -/
example (g : WithSize SPMF.Cost α) (p : α → Bool) (K : Nat)
    (hg : ∀ m, IsCostBounded (g m) fun _ => K) :
    IsCostBounded ((suchThatMaybe g p : WithSize SPMF.Cost (Option α)) n)
      fun _ => (n + 1) * K := by
  rw [IsCostBounded.iff_obs]; simp only [size_erasure]; walk [fun m => (hg m).obs]
  simpa using ‹_ ≤ ∑ i ∈ Finset.range (n + 1), K›

/-- The loop has no worst case: its expected cost is the rejection sampler's, `C / (1 - r)`. -/
example (g : WithSize SPMF.Cost α) (p : α → Bool) (C r : ENNReal)
    (hg : ∀ m, n ≤ m → IsExpectedCostBounded (g m) C)
    (hr : ∀ m, n ≤ m → SPMF.Cost.expectObs.spec (g m) (fun a _ => if p a then 0 else 1) ≤ r) :
    IsExpectedCostBounded ((QuickCheck.suchThat g p : WithSize SPMF.Cost α) n) (C / (1 - r)) := by
  rw [IsExpectedCostBounded.iff_obs]; simp only [size_erasure]
  walk [fun m hm => (hg m hm).obs, hr]
  simp

example (g : WithSize SPMF.Cost α) (f : α → Option β) (C r : ENNReal)
    (hg : ∀ m, n ≤ m → IsExpectedCostBounded (g m) C)
    (hr : ∀ m, n ≤ m →
      SPMF.Cost.expectObs.spec (g m) (fun a _ => if (f a).isSome then 0 else 1) ≤ r) :
    IsExpectedCostBounded ((suchThatMap g f : WithSize SPMF.Cost β) n) (C / (1 - r)) := by
  rw [IsExpectedCostBounded.iff_obs]; simp only [size_erasure]
  walk [fun m hm => (hg m hm).obs, hr]
  simp

end QuickCheckTest
