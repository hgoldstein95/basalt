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

/-! ## QuickCheck's combinators

A size-indexed family, as `trySizes` and `suchThatFrom` take, asks for a fact at every size. -/

section quickCheck

open QuickCheck

@[gen_rule]
theorem le_always_sublistOf {α : Type} {xs : List α} {p : List α → Prop} :
    (∀ ys, ys.Sublist xs → p ys) ≤ alwaysObs.spec (sublistOf xs) p :=
  fun h ys hys => h ys (mem_support_sublistOf_iff.mp hys)

@[gen_rule]
theorem le_always_shuffle {α : Type} {xs : List α} {p : List α → Prop} :
    (∀ ys, ys.Perm xs → p ys) ≤ alwaysObs.spec (shuffle xs) p :=
  fun h ys hys => h ys (perm_of_mem_support_shuffle hys)

variable {α β : Type} {gs : Nat → SPMF α} {f : α → Option β}

/-- What `trySizes` returns, if anything, is what `f` gives of a value drawn at one of its sizes. -/
@[gen_rule]
theorem le_always_trySizes {m k : Nat} {R : Nat → α → Prop} {post : Option β → Prop}
    (hg : ∀ j, alwaysObs.spec (gs j) (R j)) :
    (∀ o, (∀ b, o = some b → ∃ j a, m ≤ j ∧ j < m + k ∧ R j a ∧ f a = some b) → post o)
      ≤ alwaysObs.spec (trySizes gs f m k) post :=
  fun h o ho => h o fun b hb => by
    subst hb
    obtain ⟨j, a, hj, hj', ha, hf⟩ := mem_support_trySizes ho
    exact ⟨j, a, hj, hj', hg j a ha, hf⟩

/-- With no fact about `gs`, what `f` accepts. -/
@[gen_rule]
theorem le_always_trySizes_accept {m k : Nat} {post : Option β → Prop} :
    (∀ o, (∀ b, o = some b → ∃ a, f a = some b) → post o)
      ≤ alwaysObs.spec (trySizes gs f m k) post :=
  fun h o ho => h o fun b hb => by
    subst hb
    obtain ⟨j, a, -, -, -, hf⟩ := mem_support_trySizes ho
    exact ⟨a, hf⟩

/-- What `suchThatFrom` returns is what `f` gives of a value drawn at a size from `n` on. -/
@[gen_rule]
theorem le_always_suchThatFrom {n : Nat} {R : Nat → α → Prop} {post : β → Prop}
    (hg : ∀ j, alwaysObs.spec (gs j) (R j)) :
    (∀ b, (∃ j a, n ≤ j ∧ R j a ∧ f a = some b) → post b)
      ≤ alwaysObs.spec (suchThatFrom gs f n) post :=
  fun h b hb =>
    have ⟨j, a, hj, ha, hf⟩ := mem_support_suchThatFrom hb
    h b ⟨j, a, hj, hg j a ha, hf⟩

/-- With no fact about `gs`, what `f` accepts. -/
@[gen_rule]
theorem le_always_suchThatFrom_accept {n : Nat} {post : β → Prop} :
    (∀ b, (∃ a, f a = some b) → post b) ≤ alwaysObs.spec (suchThatFrom gs f n) post :=
  fun h b hb =>
    have ⟨_, a, _, _, hf⟩ := mem_support_suchThatFrom hb
    h b ⟨a, hf⟩

end quickCheck

end SPMF
