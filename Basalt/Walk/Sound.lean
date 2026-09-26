/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt.SPMF.Support
import Basalt.Walk.Attr

/-!
# Walking Soundness

What the walk needs of `SPMF.alwaysObs`, on which `IsSoundFor g P` is `alwaysObs.spec g P`: how a
fact about a sub-generator closes a leaf, the rules of the list combinators, and the admissibility
`walk fixpoint` inducts with.
-/

open RandomChoice

namespace SPMF

open Lean.Order in
theorem alwaysObs.admissible (P : α → Prop) : admissible fun x : SPMF α => alwaysObs.spec x P := by
  intro c hc ih a ha
  rw [mem_support_csup hc] at ha
  obtain ⟨x, hxc, hxa⟩ := ha
  exact ih x hxc a hxa

/-! ## Leaves

A fact about a sub-generator is used under the postcondition the walk arrives with: what it has to
imply is the bound. -/

@[obs_leaf]
theorem le_always_of_always {x : SPMF α} {R p : α → Prop} (hx : alwaysObs.spec x R) :
    (∀ a, R a → p a) ≤ alwaysObs.spec x p := fun h a ha => h a (hx a ha)

/-! ## The combinators that take a generator

They ask for the always observation of the generator, at a postcondition the list's says nothing
about: a fact supplies it. Each bridges the combinator's support law. -/

section generatorArgument

variable {α : Type} {g : SPMF α} {R : α → Prop} {p : List α → Prop}

@[gen_rule]
theorem le_always_vectorOf {n : Nat} (hg : alwaysObs.spec g R) :
    (∀ xs, (xs.length = n ∧ ∀ x ∈ xs, R x) → p xs) ≤ alwaysObs.spec (vectorOf n g) p :=
  fun h xs hxs =>
    have hxs := mem_support_vectorOf_iff.mp hxs
    h xs ⟨hxs.1, fun x hx => hg x (hxs.2 x hx)⟩

@[gen_rule]
theorem le_always_listOfMaxLength {n : Nat} (hg : alwaysObs.spec g R) :
    (∀ xs, (xs.length ≤ n ∧ ∀ x ∈ xs, R x) → p xs) ≤ alwaysObs.spec (listOfMaxLength n g) p :=
  fun h xs hxs =>
    have hxs := mem_support_listOfMaxLength_iff.mp hxs
    h xs ⟨hxs.1, fun x hx => hg x (hxs.2 x hx)⟩

@[gen_rule]
theorem le_always_listOf (hg : alwaysObs.spec g R) :
    (∀ xs, (∀ x ∈ xs, R x) → p xs) ≤ alwaysObs.spec (listOf g) p :=
  fun h xs hxs => h xs fun x hx => hg x (mem_support_listOf.mp hxs x hx)

@[gen_rule]
theorem le_always_nonEmptyListOf (hg : alwaysObs.spec g R) :
    (∀ xs, (xs ≠ [] ∧ ∀ x ∈ xs, R x) → p xs) ≤ alwaysObs.spec (nonEmptyListOf g) p :=
  fun h xs hxs =>
    have hxs := mem_support_nonEmptylistOf.mp hxs
    h xs ⟨hxs.1, fun x hx => hg x (hxs.2 x hx)⟩

end generatorArgument

/-- `permutationOf` produces every permutation of its list, and its subtype says so: there is no
support law to bridge. -/
@[gen_rule]
theorem le_always_permutationOf {α : Type} {xs : List α} {p : { ys // xs.Perm ys } → Prop} :
    (∀ a, p a) ≤ alwaysObs.spec (permutationOf xs) p :=
  fun h a _ => h a

end SPMF
