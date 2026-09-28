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
fact about a sub-generator closes a leaf, the rules of the list combinators and of `suchThat`, and
the admissibility `walk fixpoint` inducts with.
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

/-- A value `suchThat` returns is one `g` produces, and `p` accepts it. -/
@[gen_rule]
theorem le_always_suchThat {α : Type} {g : SPMF α} {p : α → Bool} {R post : α → Prop}
    (hg : alwaysObs.spec g R) :
    (∀ a, (R a ∧ p a = true) → post a) ≤ alwaysObs.spec (suchThat g p) post :=
  fun h a ha =>
    have ha := mem_support_suchThat.mp ha
    h a ⟨hg a ha.1, ha.2⟩

/-- With no fact about `g`, what `p` accepts. -/
@[gen_rule]
theorem le_always_suchThat_accept {α : Type} {g : SPMF α} {p : α → Bool} {post : α → Prop} :
    (∀ a, p a = true → post a) ≤ alwaysObs.spec (suchThat g p) post :=
  fun h a ha => h a (mem_support_suchThat.mp ha).2

/-- `permutationOf` produces every permutation of its list, and its subtype says so: there is no
support law to bridge. -/
@[gen_rule]
theorem le_always_permutationOf {α : Type} {xs : List α} {p : { ys // xs.Perm ys } → Prop} :
    (∀ a, p a) ≤ alwaysObs.spec (permutationOf xs) p :=
  fun h a _ => h a

/-- **A generator that produces nothing is sound for every postcondition.** `Gen`'s `Inhabited`
instance is `⊥`, whose mass is 0 everywhere, so a branch a generator cannot fill reaches no value and
there is nothing for `p` to hold of.

A generator that selects a branch on a `dite` typically writes `else default` for the branch whose
guard fails — one per unfillable leaf. Without this rule the walk stops at each of them and asks the
caller for a fact, and the fact has to name the postcondition, which is bespoke at every site. With
it, `walk` closes such a leaf on its own. -/
@[gen_rule]
theorem le_always_default {α : Type} {p : α → Prop} :
    (True : Prop) ≤ alwaysObs.spec (default : SPMF α) p := by
  intro _ a ha
  exact absurd ha (by
    simp only [mem_support_iff, default, Bot.bot, ne_eq, Decidable.not_not]
    rfl)

end SPMF
