/-
Copyright (c) 2026 Harrison Goldstein & Ernest Ng. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Ernest Ng
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Multiset.Basic

/-!
# Spaces, finite multisets, and indexing (Claessen–Duregård–Pałka, Section 2)

This file is a Lean translation of Section 2 of *Generating constrained random data with uniform
distribution* (Claessen, Duregård and Pałka, JFP 25, 2015). We keep the paper's names wherever
Lean allows it.

## Main definitions

- `Space` — the paper's `Space a` GADT (Section 2.2), with the paper's constructor spellings
  available as notation: `:+:`, `:*:`, `:$:`, `Pay`, `Pure`, `Empty`.
- `FinSet` — the paper's `Set a` type of finite *multisets* (Section 2.3). Renamed to avoid the
  clash with Lean's `Set`; this is also the name used in the accompanying Haskell code.
- `FinSet.card` — the paper's `|·|`.
- `FinSet.indexSet` — the paper's `indexSet` (Section 2.3).
- `Space.sized` — the paper's `sized` (Section 2.3), extracting the finite multiset of values of a
  given size out of a space.

## Main results

- `FinSet.card_eq_length_toList` — `|s|` is the length of the occurrence list of `s`.
- `FinSet.indexSet_eq_getElem?` — `indexSet s` *is* indexing into the occurrence list of `s`. This
  is the bijectivity of `indexSet` that Section 4 takes as a preliminary: the paper asks us to show
  `indexSet` is a bijection from `{0 … |s| - 1}` onto the occurrences of `s`, and identifying it
  with list indexing gives exactly that (`FinSet.indexSet_bijOn`).
- `Space.card_sized_prod` — the paper's cardinality equation for products,
  `|(T ⊗ U)ₖ| = ∑_{k₁+k₂=k} |T_{k₁}| |U_{k₂}|`.

## Representing recursive spaces

In Haskell, `spNat = Pay (Pure Zr :+: (Sc :$: spNat))` is a cyclic value. Lean's inductive types are
well-founded, so a recursive space is instead represented by its family of *finite unfoldings*
`Nat → Space α` (see `BasaltExperiments.UniformConstrained.Examples`). This loses nothing: the
paper's rule that "all recursion is guarded by at least one `Pay`" means `sized s k` inspects at
most `k` nested `Pay`s, so the `k`-sized values of a space are already determined by its `k`-th
unfolding. `Examples.sized_spNat_of_le` and friends make that precise.
-/

universe u v w

namespace UniformConstrained

/-! ## Spaces -/

/-- The paper's `Space a` (Section 2.2): a representation of an algebraic data type that supports
efficient cardinality computation and indexing.

Note the `Space (α × β)` index on `prod`: like the Haskell GADT, a product of spaces is a space of
pairs, so `Space` is a genuine inductive *family*. -/
inductive Space : Type → Type 1 where
  /-- The paper's `Empty`: the space with no values. -/
  | empty : Space α
  /-- The paper's `Pure`: the space with a single value, of size 0. -/
  | pure : α → Space α
  /-- The paper's `(:+:)`: disjoint union of two spaces. -/
  | union : Space α → Space α → Space α
  /-- The paper's `(:*:)`: the product of two spaces. -/
  | prod : Space α → Space β → Space (α × β)
  /-- The paper's `Pay`: charges one unit of size to every value in the space. -/
  | pay : Space α → Space α
  /-- The paper's `(:$:)`: applies a function to every value in the space. -/
  | fmap : (α → β) → Space α → Space β

namespace Space

@[inherit_doc] scoped infixr:65 " :+: " => Space.union
@[inherit_doc] scoped infixr:70 " :*: " => Space.prod
@[inherit_doc] scoped infixr:75 " :$: " => Space.fmap

/-- The paper's lifted application operator (Section 2.2):
`s₁ <*> s₂ = (λ(f, a) → f a) :$: (s₁ :*: s₂)`.

Written `⊛` here, since `<*>` is taken by `Seq`. -/
def ap (s₁ : Space (α → β)) (s₂ : Space α) : Space β :=
  Space.fmap (fun (fa : (α → β) × α) => fa.1 fa.2) (Space.prod s₁ s₂)

@[inherit_doc] scoped infixl:60 " ⊛ " => Space.ap

end Space

/-! ## Finite multisets -/

/-- The paper's `Set a` (Section 2.3): a type of finite *multisets*, built from the empty multiset,
singletons, disjoint union, Cartesian product, a `fmap`, and `replicateSet`.

Renamed from `Set` to `FinSet` because `Set` is taken in Lean. Because these are multisets,
"uniform over `s`" always means uniform over the *occurrences* in `s`, exactly as in the paper.

Universe-polymorphic because `sizedP` (Section 3) builds a `FinSet (Either a (Space a))`, and
`Space a` lives one universe up from `a`. -/
inductive FinSet : Type u → Type (u + 1) where
  /-- The paper's `{}`. -/
  | empty : FinSet α
  /-- The paper's `{a}`. -/
  | single : α → FinSet α
  /-- The paper's `⊎`. -/
  | union : FinSet α → FinSet α → FinSet α
  /-- The paper's `×`. -/
  | prod : FinSet α → FinSet β → FinSet (α × β)
  /-- The paper's `fmap`. -/
  | fmap : (α → β) → FinSet α → FinSet β
  /-- The paper's `replicateSet :: Integer → a → Set a` (Section 3): `n` occurrences of one value.
  This is what makes `|sizedP p s k| = |sized s k|` achievable (see `Predicate`). -/
  | replicateSet : Nat → α → FinSet α

namespace FinSet

/-- The paper's cardinality function `|·|` on finite multisets (Section 2.3). -/
def card : FinSet α → Nat
  | .empty => 0
  | .single _ => 1
  | .union a b => a.card + b.card
  | .prod a b => a.card * b.card
  | .fmap _ a => a.card
  | .replicateSet n _ => n

@[simp] theorem card_empty : (FinSet.empty : FinSet α).card = 0 := rfl
@[simp] theorem card_single (a : α) : (FinSet.single a).card = 1 := rfl
@[simp] theorem card_union (a b : FinSet α) : (a.union b).card = a.card + b.card := rfl
@[simp] theorem card_prod (a : FinSet α) (b : FinSet β) : (a.prod b).card = a.card * b.card := rfl
@[simp] theorem card_fmap (f : α → β) (a : FinSet α) : (a.fmap f).card = a.card := rfl
@[simp] theorem card_replicateSet (n : Nat) (a : α) :
    (FinSet.replicateSet n a).card = n := rfl

/-- The list of *occurrences* of a `FinSet`, in indexing order. This is the denotation of a
`FinSet`: `card` is its length (`card_eq_length_toList`) and `indexSet` is indexing into it
(`indexSet_eq_getElem?`). -/
def toList : FinSet α → List α
  | .empty => []
  | .single a => [a]
  | .union a b => a.toList ++ b.toList
  | .prod a b => a.toList.flatMap fun x => b.toList.map fun y => (x, y)
  | .fmap f a => a.toList.map f
  | .replicateSet n a => List.replicate n a

/-- The multiset denoted by a `FinSet`, forgetting the indexing order.

Section 4 of the paper says the proofs "rely on the `Set` type being an accurate representation of
multisets, so properties like commutativity and distributivity of union on `Set` follow from the
corresponding theorems for multisets". `toMultiset` is that representation, and the `toMultiset_*`
lemmas below are how those properties are transferred. -/
def toMultiset (s : FinSet α) : Multiset α := (s.toList : Multiset α)

@[simp] theorem toMultiset_empty : (FinSet.empty : FinSet α).toMultiset = 0 := rfl
@[simp] theorem toMultiset_single (a : α) : (FinSet.single a).toMultiset = {a} := rfl

@[simp] theorem toMultiset_union (a b : FinSet α) :
    (a.union b).toMultiset = a.toMultiset + b.toMultiset := rfl

@[simp] theorem toMultiset_fmap (f : α → β) (a : FinSet α) :
    (a.fmap f).toMultiset = a.toMultiset.map f := rfl

@[simp] theorem toMultiset_replicateSet (n : Nat) (a : α) :
    (FinSet.replicateSet n a).toMultiset = Multiset.replicate n a := rfl

/-- The paper's `×` on multisets is `Multiset.product`. -/
@[simp] theorem toMultiset_prod (a : FinSet α) (b : FinSet β) :
    (a.prod b).toMultiset = a.toMultiset ×ˢ b.toMultiset := by
  show ((a.toList.flatMap fun x => b.toList.map fun y => (x, y) : List (α × β)) : Multiset (α × β))
    = _
  unfold SProd.sprod Multiset.instSProd Multiset.product
  rw [← Multiset.coe_bind]
  rfl


@[simp] theorem toList_empty : (FinSet.empty : FinSet α).toList = [] := rfl
@[simp] theorem toList_single (a : α) : (FinSet.single a).toList = [a] := rfl
@[simp] theorem toList_union (a b : FinSet α) :
    (a.union b).toList = a.toList ++ b.toList := rfl
@[simp] theorem toList_prod (a : FinSet α) (b : FinSet β) :
    (a.prod b).toList = a.toList.flatMap fun x => b.toList.map fun y => (x, y) := rfl
@[simp] theorem toList_fmap (f : α → β) (a : FinSet α) :
    (a.fmap f).toList = a.toList.map f := rfl
@[simp] theorem toList_replicateSet (n : Nat) (a : α) :
    (FinSet.replicateSet n a).toList = List.replicate n a := rfl

private theorem length_listProd (xs : List α) (ys : List β) :
    (xs.flatMap fun x => ys.map fun y => (x, y)).length = xs.length * ys.length := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih, Nat.succ_mul, Nat.add_comm]

/-- `|s|` counts the occurrences of `s`. -/
@[simp]
theorem card_eq_length_toList (s : FinSet α) : s.card = s.toList.length := by
  induction s with
  | empty => rfl
  | single => rfl
  | union a b iha ihb => simp [iha, ihb]
  | prod a b iha ihb => simp [iha, ihb]
  | fmap f a iha => simp [iha]
  | replicateSet n a => simp

theorem card_toMultiset (s : FinSet α) : s.toMultiset.card = s.card := by
  rw [toMultiset, Multiset.coe_card, s.card_eq_length_toList]

/-- The paper's `indexSet` (Section 2.3), mapping an index in `{0 … |s| - 1}` to an occurrence of
`s`. Out-of-range indices give `none`, which is how the paper's partial equations are read. -/
def indexSet : FinSet α → Nat → Option α
  | .empty, _ => none
  | .single a, 0 => some a
  | .single _, _ + 1 => none
  | .union a b, i => if i < a.card then indexSet a i else indexSet b (i - a.card)
  -- The paper's `do { fst ← indexSet a (i / |b|); snd ← indexSet b (i % |b|); return (fst, snd) }`
  | .prod a b, i =>
    (indexSet a (i / b.card)).bind fun x =>
      (indexSet b (i % b.card)).map fun y => (x, y)
  | .fmap f a, i => (indexSet a i).map f
  | .replicateSet n a, i => if i < n then some a else none

@[simp] theorem indexSet_empty (i : Nat) : indexSet (FinSet.empty : FinSet α) i = none := rfl

theorem indexSet_union (a b : FinSet α) (i : Nat) :
    indexSet (a.union b) i =
      if i < a.card then indexSet a i else indexSet b (i - a.card) := rfl

theorem indexSet_fmap (f : α → β) (a : FinSet α) (i : Nat) :
    indexSet (a.fmap f) i = (indexSet a i).map f := rfl

theorem indexSet_prod (a : FinSet α) (b : FinSet β) (i : Nat) :
    indexSet (a.prod b) i =
      (indexSet a (i / b.card)).bind fun x =>
        (indexSet b (i % b.card)).map fun y => (x, y) := rfl

/-- Indexing a Cartesian product of occurrence lists splits the index by `divMod`, which is the
`prod` case of `indexSet_eq_getElem?`. -/
private theorem getElem?_listProd (xs : List α) (ys : List β) (i : Nat) :
    (xs.flatMap fun x => ys.map fun y => (x, y))[i]? =
      (xs[i / ys.length]?).bind fun x => (ys[i % ys.length]?).map fun y => (x, y) := by
  rcases Nat.eq_zero_or_pos ys.length with hy | hy
  · rw [List.length_eq_zero_iff.mp hy]
    simp
  · induction xs generalizing i with
    | nil => simp
    | cons x xs ih =>
      rcases Nat.lt_or_ge i ys.length with hi | hi
      · rw [List.flatMap_cons, List.getElem?_append_left (by simpa using hi)]
        rw [Nat.div_eq_of_lt hi, Nat.mod_eq_of_lt hi]
        rw [List.getElem?_map, List.getElem?_cons_zero]
        rfl
      · have hlen : (ys.map fun y => (x, y)).length = ys.length := by simp
        rw [List.flatMap_cons, List.getElem?_append_right (by omega)]
        rw [hlen, ih (i - ys.length)]
        have hdiv : i / ys.length = (i - ys.length) / ys.length + 1 :=
          Nat.div_eq_sub_div hy hi
        have hmod : i % ys.length = (i - ys.length) % ys.length :=
          Nat.mod_eq_sub_mod hi
        rw [hdiv, hmod, List.getElem?_cons_succ]

/-- **`indexSet` is list indexing.** The paper's Section 4 preliminaries ask for `indexSet` to be a
bijection onto the occurrences of `s`; this identifies it with `getElem?` on the occurrence list,
from which bijectivity is immediate (`indexSet_bijOn`). -/
theorem indexSet_eq_getElem? (s : FinSet α) (i : Nat) : indexSet s i = s.toList[i]? := by
  induction s generalizing i with
  | empty => rfl
  | single a => cases i <;> simp [indexSet]
  | union a b iha ihb =>
    rw [indexSet_union, toList_union]
    rcases Nat.lt_or_ge i a.card with h | h
    · rw [if_pos h, iha, List.getElem?_append_left (by simpa using h)]
    · rw [if_neg (by omega), ihb, List.getElem?_append_right (by simpa using h)]
      simp
  | prod a b iha ihb =>
    rw [indexSet_prod, toList_prod, getElem?_listProd, ← iha, ← ihb,
      ← card_eq_length_toList b]
  | fmap f a iha => rw [indexSet_fmap, iha, toList_fmap, List.getElem?_map]
  | replicateSet n a =>
    simp only [indexSet, toList_replicateSet]
    rcases Nat.lt_or_ge i n with h | h
    · simp [h]
    · simp [Nat.not_lt.mpr h]

/-- In-range indices always hit an occurrence. -/
theorem indexSet_isSome (s : FinSet α) {i : Nat} (h : i < s.card) :
    (indexSet s i).isSome := by
  rw [indexSet_eq_getElem?, List.getElem?_eq_getElem (by simpa using h)]
  rfl

/-- Out-of-range indices miss. -/
theorem indexSet_eq_none (s : FinSet α) {i : Nat} (h : s.card ≤ i) :
    indexSet s i = none := by
  rw [indexSet_eq_getElem?, List.getElem?_eq_none_iff]
  simpa using h

/-- The total form of `indexSet` on in-range indices: the paper's
`indexSet : {0 … |s| - 1} → s` with the range restriction made a proof obligation rather than a
partiality. `uniformSet` uses this so no `Option` leaks into the sampler's result type. -/
def index (s : FinSet α) (i : Nat) (h : i < s.card) : α :=
  s.toList[i]'(by simpa using h)

theorem indexSet_index (s : FinSet α) (i : Nat) (h : i < s.card) :
    indexSet s i = some (s.index i h) := by
  rw [indexSet_eq_getElem?]
  exact List.getElem?_eq_getElem _

/-- **`indexSet` realizes multiplicities: it is a bijection onto the occurrences of `s`.**

This is the Section 4 preliminary "`indexSet` is bijective". Because a `FinSet` is a *multiset*, the
bijection is onto occurrences rather than onto values — the paper is explicit that "uniform over
`s`" means uniform over the occurrences in `s`. The usable form of that statement is this one: of
the `|s|` valid indices, exactly `count a s` of them name `a`. With the index drawn uniformly from
`{0 … |s| - 1}`, this says `uniformSet s` returns `a` with probability `count a s / |s|`, i.e. it is
uniform over occurrences. -/
theorem countP_indexSet_eq_count [DecidableEq α] (s : FinSet α) (a : α) :
    ((List.range s.card).countP (fun i => indexSet s i == some a)) = s.toMultiset.count a := by
  have key : ∀ l : List α,
      ((List.range l.length).countP (fun i => l[i]? == some a)) = l.count a := by
    intro l
    induction l with
    | nil => simp
    | cons x xs ih =>
      rw [List.length_cons, List.range_succ_eq_map, List.countP_cons, List.countP_map,
        List.count_cons]
      simp only [List.getElem?_cons_zero, Function.comp_def, List.getElem?_cons_succ]
      rw [ih]
      by_cases h : x = a <;> simp [h]
  simp only [indexSet_eq_getElem?, card_eq_length_toList, toMultiset, Multiset.coe_count]
  exact key s.toList

end FinSet

/-! ## Extracting the values of a given size -/

namespace Space

open scoped Space

/-- The union over all ways of splitting a size between the two components of a product, i.e. the
paper's `sizedHelper` from the `(:*:)` case of `sized` (Section 2.3).

`sizedProd fa fb k₁ n` is `⨄_{i<n} fa (k₁ + i) × fb (n - 1 - i)`; instantiated at `k₁ = 0`,
`n = k + 1` it is `⨄_{k₁+k₂=k} fa k₁ × fb k₂`, right-nested and terminated by `{}`, exactly as in
the paper. -/
def sizedProd (fa : Nat → FinSet α) (fb : Nat → FinSet β) (k₁ : Nat) : Nat → FinSet (α × β)
  | 0 => .empty
  | n + 1 => .union (.prod (fa k₁) (fb n)) (sizedProd fa fb (k₁ + 1) n)

/-- The paper's `sized :: Space a → Int → Set a` (Section 2.3): the finite multiset of values of a
given size in a space. -/
def sized : Space α → Nat → FinSet α
  | .empty, _ => .empty
  | .pure a, 0 => .single a
  | .pure _, _ + 1 => .empty
  | .pay _, 0 => .empty
  | .pay a, k + 1 => sized a k
  | .union a b, k => .union (sized a k) (sized b k)
  | .fmap f a, k => .fmap f (sized a k)
  | .prod a b, k => sizedProd (sized a) (sized b) 0 (k + 1)

@[simp] theorem sized_empty (k : Nat) : sized (Space.empty : Space α) k = .empty := rfl
@[simp] theorem sized_pure_zero (a : α) : sized (Space.pure a) 0 = .single a := rfl
@[simp] theorem sized_pure_succ (a : α) (k : Nat) :
    sized (Space.pure a) (k + 1) = .empty := rfl
@[simp] theorem sized_pay_zero (a : Space α) : sized (a.pay) 0 = .empty := rfl
@[simp] theorem sized_pay_succ (a : Space α) (k : Nat) : sized (a.pay) (k + 1) = sized a k := rfl
@[simp] theorem sized_union (a b : Space α) (k : Nat) :
    sized (a :+: b) k = .union (sized a k) (sized b k) := rfl
@[simp] theorem sized_fmap (f : α → β) (a : Space α) (k : Nat) :
    sized (f :$: a) k = .fmap f (sized a k) := rfl
theorem sized_prod (a : Space α) (b : Space β) (k : Nat) :
    sized (a :*: b) k = sizedProd (sized a) (sized b) 0 (k + 1) := rfl

/-- `|·|` of `sizedProd`: a sum of products of cardinalities. -/
theorem card_sizedProd (fa : Nat → FinSet α) (fb : Nat → FinSet β) (k₁ n : Nat) :
    (sizedProd fa fb k₁ n).card = ∑ i ∈ Finset.range n, (fa (k₁ + i)).card * (fb (n - 1 - i)).card := by
  induction n generalizing k₁ with
  | zero => simp [sizedProd]
  | succ n ih =>
    rw [sizedProd, FinSet.card_union, FinSet.card_prod, ih, Finset.sum_range_succ']
    simp only [Nat.add_zero, Nat.add_sub_cancel]
    rw [Nat.add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    have h : n - 1 - i = n - (i + 1) := by omega
    have h' : k₁ + 1 + i = k₁ + (i + 1) := by omega
    rw [h, h']

/-- The paper's cardinality equation for products (Section 2.1):
`|(T ⊗ U)ₖ| = ∑_{k₁+k₂=k} |T_{k₁}| |U_{k₂}|`. -/
theorem card_sized_prod (a : Space α) (b : Space β) (k : Nat) :
    (sized (a :*: b) k).card =
      ∑ k₁ ∈ Finset.range (k + 1), (sized a k₁).card * (sized b (k - k₁)).card := by
  rw [sized_prod, card_sizedProd]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Nat.zero_add, Nat.add_sub_cancel]

/-- `sized (a :*: b) k` as a multiset: the paper's `⨄_{k₁+k₂=k} sized a k₁ × sized b k₂`. -/
theorem toMultiset_sized_prod (a : Space α) (b : Space β) (k : Nat) :
    (sized (a :*: b) k).toMultiset =
      ∑ k₁ ∈ Finset.range (k + 1),
        (sized a k₁).toMultiset ×ˢ (sized b (k - k₁)).toMultiset := by
  rw [sized_prod]
  -- Peel `sizedProd` one split at a time, matching it against `Finset.sum_range_succ'`.
  suffices h : ∀ n k₁ : Nat, (sizedProd (sized a) (sized b) k₁ n).toMultiset =
      ∑ i ∈ Finset.range n, (sized a (k₁ + i)).toMultiset ×ˢ (sized b (n - 1 - i)).toMultiset by
    rw [h]
    exact Finset.sum_congr rfl fun i _ => by simp only [Nat.zero_add, Nat.add_sub_cancel]
  intro n
  induction n with
  | zero => simp [sizedProd]
  | succ n ih =>
    intro k₁
    rw [sizedProd, FinSet.toMultiset_union, FinSet.toMultiset_prod, ih,
      Finset.sum_range_succ']
    simp only [Nat.add_zero, Nat.add_sub_cancel]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    have h : n - 1 - i = n - (i + 1) := by omega
    have h' : k₁ + 1 + i = k₁ + (i + 1) := by omega
    rw [h, h']

/-! ## The `***` operator (Section 3.1)

The paper eliminates top-level products from a space using the algebraic laws

```
a ⊗ (b ⊕ c) ≡ (a ⊗ b) ⊕ (a ⊗ c)   [distributivity]
a ⊗ (b ⊗ c) ≡ (a ⊗ b) ⊗ c          [associativity]
a ⊗ 1       ≡ a                    [identity]
a ⊗ 0       ≡ 0                    [annihilation]
```

repackaged as a Haskell operator `(***)` that "pushes top level products inwards without loss of
information", plus the two lifting laws for `Pay` and `:$:`. Since Lean's spaces are typed exactly
like the Haskell GADT, the coercions the paper inserts by hand (`λ(∼(x, y), z) → (x, (y, z))` etc.)
appear here too. -/

/-- The paper's `(***)` operator (Section 3.1). Defined by cases on the *right* operand, pushing the
product inwards:

```haskell
a *** (b :+: c) = (a :*: b) :+: (a :*: c)                                    [distributivity]
a *** (b :*: c) = (λ(∼(x, y), z) → (x, (y, z))) :$: ((a :*: b) :*: c)        [associativity]
a *** (Pure x)  = (λy → (y, x)) :$: a                                        [identity]
a *** Empty     = Empty                                                      [annihilation]
a *** (Pay b)   = Pay (a :*: b)                                              [lift-pay]
a *** (f :$: b) = (λ(x, y) → (x, f y)) :$: (a :*: b)                        [lift-fmap]
```

Note that `***` produces a space *without a top-level product* except where it re-nests one under a
`Pay`, `:+:` or `:$:` — that is what "pushing products inwards" means. -/
def prodR : {α β : Type} → Space α → Space β → Space (α × β)
  | _, _, a, .union b c => (a :*: b) :+: (a :*: c)
  | _, _, a, .prod b c =>
    (fun (p : (_ × _) × _) => (p.1.1, (p.1.2, p.2))) :$: ((a :*: b) :*: c)
  | _, _, a, .pure x => (fun y => (y, x)) :$: a
  | _, _, _, .empty => .empty
  | _, _, a, .pay b => .pay (a :*: b)
  | _, _, a, .fmap f b => (fun p => (p.1, f p.2)) :$: (a :*: b)

@[inherit_doc] scoped infixr:70 " *** " => Space.prodR

@[simp] theorem prodR_union (a : Space α) (b c : Space β) :
    a *** (b :+: c) = (a :*: b) :+: (a :*: c) := rfl
@[simp] theorem prodR_prod (a : Space α) (b : Space β) (c : Space γ) :
    a *** (b :*: c)
      = (fun (p : (α × β) × γ) => (p.1.1, (p.1.2, p.2))) :$: ((a :*: b) :*: c) := rfl
@[simp] theorem prodR_pure (a : Space α) (x : β) :
    a *** (Space.pure x) = (fun y => (y, x)) :$: a := rfl
@[simp] theorem prodR_empty (a : Space α) :
    a *** (Space.empty : Space β) = Space.empty := rfl
@[simp] theorem prodR_pay (a : Space α) (b : Space β) : a *** b.pay = (a :*: b).pay := rfl
@[simp] theorem prodR_fmap (a : Space α) (f : β → γ) (b : Space β) :
    a *** (f :$: b) = (fun p => (p.1, f p.2)) :$: (a :*: b) := rfl

/-! ### Lemma 1: `***` preserves the multiset of values of each size -/

/-- `Multiset.map` distributes over a `Finset.sum` of multisets. -/
private theorem map_finsetSum {ι : Type*} (t : Finset ι) (g : ι → Multiset α) (f : α → β) :
    (∑ i ∈ t, g i).map f = ∑ i ∈ t, (g i).map f :=
  map_sum (Multiset.mapAddMonoidHom f) _ _

/-- `×ˢ` distributes over a `Finset.sum` in its right argument. -/
private theorem product_finsetSum {ι : Type*} (s : Multiset α) (t : Finset ι)
    (g : ι → Multiset β) : s ×ˢ (∑ i ∈ t, g i) = ∑ i ∈ t, s ×ˢ (g i) := by
  classical
  induction t using Finset.induction with
  | empty => simp
  | insert a t ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Multiset.product_add, ih]

/-- `×ˢ` distributes over a `Finset.sum` in its left argument. -/
private theorem finsetSum_product {ι : Type*} (t : Finset ι) (g : ι → Multiset α)
    (s : Multiset β) : (∑ i ∈ t, g i) ×ˢ s = ∑ i ∈ t, (g i) ×ˢ s := by
  classical
  induction t using Finset.induction with
  | empty => simp
  | insert a t ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Multiset.add_product, ih]

/-- Multiset identity behind the `identity` law: `s ×ˢ {x} = s.map (·, x)`. -/
private theorem product_singleton (s : Multiset α) (x : β) :
    s ×ˢ ({x} : Multiset β) = s.map (fun y => (y, x)) := by
  refine Multiset.induction_on s (by simp) fun a s ih => ?_
  rw [Multiset.cons_product, ih, Multiset.map_cons]
  simp

/-- The `Prod.mk`-shifted case of `product_assoc`. -/
private theorem product_assoc_mk (a : α) (t : Multiset β) (u : Multiset γ) :
    ((t.map (Prod.mk a)) ×ˢ u).map (fun p : (α × β) × γ => (p.1.1, (p.1.2, p.2)))
      = (t ×ˢ u).map (Prod.mk a) := by
  refine Multiset.induction_on t (by simp) fun b t iht => ?_
  rw [Multiset.map_cons, Multiset.cons_product, Multiset.map_add, iht, Multiset.cons_product,
    Multiset.map_add]
  congr 1
  simp [Multiset.map_map]

/-- Multiset identity behind the `associativity` law. -/
private theorem product_assoc (s : Multiset α) (t : Multiset β) (u : Multiset γ) :
    ((s ×ˢ t) ×ˢ u).map (fun p : (α × β) × γ => (p.1.1, (p.1.2, p.2))) = s ×ˢ (t ×ˢ u) := by
  refine Multiset.induction_on s (by simp) fun a s ih => ?_
  rw [Multiset.cons_product, Multiset.add_product, Multiset.map_add, ih, Multiset.cons_product,
    product_assoc_mk]

/-- Multiset identity behind commutativity of products: `(s ×ˢ t).map swap = t ×ˢ s`. -/
private theorem product_swap (s : Multiset α) (t : Multiset β) :
    (s ×ˢ t).map Prod.swap = t ×ˢ s := by
  refine Multiset.induction_on s (by simp) fun a s ih => ?_
  rw [Multiset.cons_product, Multiset.map_add, ih,
    show t ×ˢ (a ::ₘ s) = t.map (fun y => (y, a)) + t ×ˢ s from ?_]
  · congr 1
    simp [Multiset.map_map]
  · refine Multiset.induction_on t (by simp) fun b t iht => ?_
    rw [Multiset.cons_product, Multiset.cons_product, iht, Multiset.map_cons]
    simp only [Multiset.map_cons, Multiset.cons_add]
    rw [add_left_comm]

/-- Multiset identity behind the `lift-fmap` law. -/
private theorem product_map_right (s : Multiset α) (f : β → γ) (t : Multiset β) :
    (s ×ˢ t).map (fun p : α × β => (p.1, f p.2)) = s ×ˢ t.map f := by
  refine Multiset.induction_on s (by simp) fun a s ih => ?_
  rw [Multiset.cons_product, Multiset.map_add, ih, Multiset.cons_product]
  congr 1
  simp [Multiset.map_map]

/-- **Lemma 1 (Claessen–Duregård–Pałka).**

> Let `a :: Space a` and `b :: Space b` be two spaces, and `k :: Int` a non-negative integer. Then
> the following equivalence holds between multisets: `sized (a :*: b) k = sized (a *** b) k`.

The paper's proof is "a straightforward proof by structural induction on `b`", with "each of the
cases proven using the corresponding laws for multisets and `Pay`". Note that the equality really is
only up to `toMultiset`: `***` reorders the occurrences (that reordering is the whole point of
Section 3.1 — it is chosen to match the predicate's evaluation order), so the two spaces are *not*
equal as `FinSet`s and do not agree under `indexSet`. -/
theorem Lemma1 : ∀ {α β : Type} (a : Space α) (b : Space β) (k : Nat),
    (sized (a :*: b) k).toMultiset = (sized (a *** b) k).toMultiset := by
  intro α β a b
  induction b with
  | empty => intro k; simp [toMultiset_sized_prod]
  | pure x =>
    -- `identity`: only the split `k₁ = k` contributes, and `sized (Pure x) 0 = {x}`.
    intro k
    rw [toMultiset_sized_prod, prodR_pure, sized_fmap, FinSet.toMultiset_fmap]
    rw [Finset.sum_eq_single k]
    · simp [product_singleton]
    · intro i hi hik
      -- Every other split leaves `Pure x` a nonzero size, and `sized (Pure x) (n+1) = {}`.
      simp only [Finset.mem_range] at hi
      have : k - i = (k - i - 1) + 1 := by omega
      rw [this]
      simp
    · simp
  | union b c ihb ihc =>
    -- `distributivity`.
    intro k
    rw [prodR_union, sized_union, FinSet.toMultiset_union,
      toMultiset_sized_prod, toMultiset_sized_prod, toMultiset_sized_prod,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k₁ _ => by
      simp only [sized_union, FinSet.toMultiset_union, Multiset.product_add]
  | prod b c ihb ihc =>
    -- `associativity`. Reassociating the size split is `Finset.sum_sigma`-style bookkeeping, so we
    -- prove it directly by double induction on the two split bounds.
    intro k
    rw [prodR_prod, sized_fmap, FinSet.toMultiset_fmap, toMultiset_sized_prod,
      toMultiset_sized_prod, map_finsetSum]
    -- LHS: `∑_{k₁ ≤ k} A k₁ ×ˢ (B ⊗ C)_{k-k₁}`; RHS: `∑_{j ≤ k} ((A ⊗ B)_j ×ˢ C_{k-j})` mapped.
    have hL : ∀ k₁, (sized (b :*: c) (k - k₁)).toMultiset
        = ∑ k₂ ∈ Finset.range (k - k₁ + 1),
            (sized b k₂).toMultiset ×ˢ (sized c (k - k₁ - k₂)).toMultiset :=
      fun k₁ => toMultiset_sized_prod b c (k - k₁)
    have hR : ∀ j, (sized (a :*: b) j).toMultiset
        = ∑ k₁ ∈ Finset.range (j + 1),
            (sized a k₁).toMultiset ×ˢ (sized b (j - k₁)).toMultiset :=
      fun j => toMultiset_sized_prod a b j
    simp only [hL, hR, product_finsetSum, finsetSum_product, map_finsetSum]
    -- Both sides are now double sums over `{(k₁, k₂) | k₁ + k₂ ≤ k}`; reindex.
    rw [Finset.sum_sigma' (Finset.range (k + 1)) (fun k₁ => Finset.range (k - k₁ + 1)) _,
      Finset.sum_sigma' (Finset.range (k + 1)) (fun j => Finset.range (j + 1)) _]
    -- `⟨k₁, k₂⟩ ↦ ⟨k₁ + k₂, k₁⟩` reassociates the split; its inverse is `⟨j, i⟩ ↦ ⟨i, j - i⟩`.
    refine Finset.sum_nbij' (i := fun p => ⟨p.1 + p.2, p.1⟩)
      (j := fun q => ⟨q.2, q.1 - q.2⟩) ?_ ?_ ?_ ?_ ?_
    · rintro ⟨k₁, k₂⟩ hp
      simp only [Finset.mem_sigma, Finset.mem_range] at hp ⊢
      omega
    · rintro ⟨j, i⟩ hq
      simp only [Finset.mem_sigma, Finset.mem_range] at hq ⊢
      omega
    · rintro ⟨k₁, k₂⟩ hp
      simp only [Finset.mem_sigma, Finset.mem_range] at hp
      simp only [Nat.add_sub_cancel_left]
    · rintro ⟨j, i⟩ hq
      simp only [Finset.mem_sigma, Finset.mem_range] at hq
      simp only [Sigma.mk.injEq, heq_eq_eq, and_true]
      omega
    · rintro ⟨k₁, k₂⟩ hp
      simp only [Finset.mem_sigma, Finset.mem_range] at hp
      have h1 : k₁ + k₂ - k₁ = k₂ := by omega
      have h2 : k - (k₁ + k₂) = k - k₁ - k₂ := by omega
      simp only [h1, h2, ← product_assoc]
  | pay b ihb =>
    -- `lift-pay`: `sized (a :*: Pay b) k` and `sized (Pay (a :*: b)) k` both drop the `k₁ = k` term
    -- and shift the size by one.
    intro k
    rw [prodR_pay]
    cases k with
    | zero => simp [toMultiset_sized_prod]
    | succ k =>
      rw [sized_pay_succ, toMultiset_sized_prod, toMultiset_sized_prod]
      rw [Finset.sum_range_succ]
      simp only [sized_pay_zero, Nat.sub_self, FinSet.toMultiset_empty, Multiset.product_zero,
        add_zero]
      refine Finset.sum_congr rfl fun k₁ hk₁ => ?_
      simp only [Finset.mem_range] at hk₁
      have : k + 1 - k₁ = (k - k₁) + 1 := by omega
      rw [this, sized_pay_succ]
  | fmap f b ihb =>
    -- `lift-fmap`.
    intro k
    rw [prodR_fmap, sized_fmap, FinSet.toMultiset_fmap, toMultiset_sized_prod,
      toMultiset_sized_prod, map_finsetSum]
    exact Finset.sum_congr rfl fun k₁ _ => by
      simp only [sized_fmap, FinSet.toMultiset_fmap, product_map_right]

/-- Lemma 1 in the form the paper uses it: `***` preserves cardinalities, so the uniformity
argument's `n = |a|` is unchanged by the transformation. -/
theorem card_sized_prodR (a : Space α) (b : Space β) (k : Nat) :
    (sized (a *** b) k).card = (sized (a :*: b) k).card := by
  rw [← FinSet.card_toMultiset, ← FinSet.card_toMultiset, ← Lemma1]

/-- **Commutativity of space products**, the other law Section 3.1 needs: `sizedP`'s `inspectsFst`
branch swaps the operands of a product before transforming it, and this says the swap is harmless.
Stated up to `Prod.swap`, since `a :*: b` and `b :*: a` have different types. -/
theorem toMultiset_sized_prod_comm (a : Space α) (b : Space β) (k : Nat) :
    (sized (b :*: a) k).toMultiset.map Prod.swap = (sized (a :*: b) k).toMultiset := by
  rw [toMultiset_sized_prod, toMultiset_sized_prod, map_finsetSum]
  -- Reindex `k₁ ↦ k - k₁` and use `(s ×ˢ t).map swap = t ×ˢ s`.
  refine Finset.sum_nbij' (i := fun k₁ => k - k₁) (j := fun k₂ => k - k₂)
    (fun i hi => by simp only [Finset.mem_range] at hi ⊢; omega)
    (fun i hi => by simp only [Finset.mem_range] at hi ⊢; omega)
    (fun i hi => by simp only [Finset.mem_range] at hi ⊢; omega)
    (fun i hi => by simp only [Finset.mem_range] at hi ⊢; omega)
    (fun i hi => ?_)
  simp only [Finset.mem_range] at hi
  have h : k - (k - i) = i := by omega
  rw [h, product_swap]

/-- Commutativity in the form `card_sizedP` needs. -/
theorem card_sized_prod_comm (a : Space α) (b : Space β) (k : Nat) :
    (sized (b :*: a) k).card = (sized (a :*: b) k).card := by
  rw [← FinSet.card_toMultiset, ← FinSet.card_toMultiset, ← toMultiset_sized_prod_comm,
    Multiset.card_map]

/-- **The exact rearrangement `sizedP`'s `inspectsFst` branch performs**, in one lemma: swap the
operands, push the product inwards with `***`, then swap the pairs back. Lemma 1 handles the `***`
and `toMultiset_sized_prod_comm` the swap, so the multiset of values of each size is unchanged.

This is the step the paper labels "`{-From Lemma 1 -}`" followed by
"`{-Commutativity of space products -}`" in its Lemma 2 proof. -/
theorem toMultiset_sized_swap_prodR (a : Space α) (b : Space β) (k : Nat) :
    (sized (Prod.swap :$: (b *** a)) k).toMultiset = (sized (a :*: b) k).toMultiset := by
  rw [sized_fmap, FinSet.toMultiset_fmap, ← Lemma1, toMultiset_sized_prod_comm]

end Space

end UniformConstrained
