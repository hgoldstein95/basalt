/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt.SPMF.Cost
import Basalt.Walk.Attr

/-!
# Walking Completeness

What the walk needs of `SPMF.mayObs`, on which `a ∈ SPMF.support g` is `mayObs.spec g (· = a)`:
how a fact about a sub-generator closes a leaf, and the rules of the list combinators. A lower bound
on a least fixed point needs a ranking, which is the user's induction (`IsCompleteFor.of_measure`),
so there is no admissibility here, and a recursive occurrence is left in the precondition as
itself.
-/

open RandomChoice

namespace SPMF

/-! ## Leaves -/

@[obs_leaf]
theorem le_may_of_may {x : SPMF α} {R p : α → Prop} (hx : ∀ a, R a → mayObs.spec x (· = a)) :
    (∃ a, R a ∧ p a) ≤ mayObs.spec x p := fun ⟨a, hR, hp⟩ =>
  ⟨a, mem_support_iff_may.mpr (hx a hR), hp⟩

/-- The reflexive leaf: a generator nothing is known about is reached through its own support. -/
@[obs_leaf self]
theorem le_may_self {x : SPMF α} {p : α → Prop} :
    (∃ a, a ∈ x.support ∧ p a) ≤ mayObs.spec x p := fun ⟨a, ha, hp⟩ => ⟨a, ha, hp⟩

/-- The induction hypothesis of `IsCompleteFor.of_measure`, as a leaf. -/
@[obs_leaf]
theorem le_may_of_measure {σ α : Type} {gen : σ → SPMF α} {P : σ → α → Prop} {μ : σ → α → Nat}
    {n : Nat} (ih : ∀ s a, μ s a < n → P s a → a ∈ (gen s).support) (s : σ) (p : α → Prop) :
    (∃ a, (μ s a < n ∧ P s a) ∧ p a) ≤ mayObs.spec (gen s) p :=
  fun ⟨a, ⟨h1, h2⟩, hp⟩ => ⟨a, ih s a h1 h2, hp⟩

/-! ## The combinators that take a generator

They ask for the may observation of the generator at each value a predicate admits, which the
list's postcondition says nothing about: a fact supplies it. Each bridges the combinator's support
law. -/

section generatorArgument

variable {α : Type} {g : SPMF α} {R : α → Prop} {p : List α → Prop}

private theorem mem_of_may (hg : ∀ a, R a → mayObs.spec g (· = a)) : ∀ a, R a → a ∈ g.support :=
  fun a h => mem_support_iff_may.mpr (hg a h)

@[gen_rule]
theorem le_may_vectorOf {n : Nat} (hg : ∀ a, R a → mayObs.spec g (· = a)) :
    (∃ xs, (xs.length = n ∧ ∀ x ∈ xs, R x) ∧ p xs) ≤ mayObs.spec (vectorOf n g) p :=
  fun ⟨xs, ⟨hn, hR⟩, hp⟩ =>
    ⟨xs, mem_support_vectorOf_iff.mpr ⟨hn, fun x hx => mem_of_may hg x (hR x hx)⟩, hp⟩

@[gen_rule]
theorem le_may_listOfMaxLength {n : Nat} (hg : ∀ a, R a → mayObs.spec g (· = a)) :
    (∃ xs, (xs.length ≤ n ∧ ∀ x ∈ xs, R x) ∧ p xs) ≤ mayObs.spec (listOfMaxLength n g) p :=
  fun ⟨xs, ⟨hn, hR⟩, hp⟩ =>
    ⟨xs, mem_support_listOfMaxLength_iff.mpr ⟨hn, fun x hx => mem_of_may hg x (hR x hx)⟩, hp⟩

@[gen_rule]
theorem le_may_listOf (hg : ∀ a, R a → mayObs.spec g (· = a)) :
    (∃ xs, (∀ x ∈ xs, R x) ∧ p xs) ≤ mayObs.spec (listOf g) p :=
  fun ⟨xs, hR, hp⟩ => ⟨xs, mem_support_listOf.mpr fun x hx => mem_of_may hg x (hR x hx), hp⟩

@[gen_rule]
theorem le_may_nonEmptyListOf (hg : ∀ a, R a → mayObs.spec g (· = a)) :
    (∃ xs, (xs ≠ [] ∧ ∀ x ∈ xs, R x) ∧ p xs) ≤ mayObs.spec (nonEmptyListOf g) p :=
  fun ⟨xs, ⟨hne, hR⟩, hp⟩ =>
    ⟨xs, mem_support_nonEmptylistOf.mpr ⟨hne, fun x hx => mem_of_may hg x (hR x hx)⟩, hp⟩

end generatorArgument

@[gen_rule]
theorem le_may_permutationOf {α : Type} {xs : List α} {p : { ys // xs.Perm ys } → Prop} :
    (∃ a, p a) ≤ mayObs.spec (permutationOf xs) p :=
  fun ⟨a, hp⟩ => ⟨a, mem_support_permutationOf_iff.mpr trivial, hp⟩

end SPMF

namespace SPMF.Cost

/-! ## The cost interpretation

A run with its cost, `(a, n) ∈ SPMF.support g`, is the may observation at `fun b m => b = a ∧ m = n`.
There is no law to find here, so a callee stays in the precondition as a recursive occurrence
does. -/

@[obs_leaf self]
theorem le_may_self {x : SPMF.Cost α} {p : α → Nat → Prop} :
    (∃ a n, (a, n) ∈ SPMF.support x ∧ p a n) ≤ mayObs.spec x p :=
  fun ⟨a, n, ha, hp⟩ => ⟨(a, n), ha, hp⟩

end SPMF.Cost
