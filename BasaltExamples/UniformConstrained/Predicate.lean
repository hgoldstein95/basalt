/-
Copyright (c) 2026 Harrison Goldstein & Ernest Ng. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Ernest Ng
-/
module

public import BasaltExamples.UniformConstrained.Uniform

/-!
# Predicate-guided refinement: `sizedP` and Lemmas 2–3 (Figure 2, Sections 3.1 and 4)

`sizedP` splits the values of a size into those satisfying the predicate and residual spaces that
exclude failing ones, guided by an abstract `LazyOracle`. Its result has one entry per value
(`card_sizedP`); its values are exactly the satisfying ones (`Lemma2`), and each residual keeps them
all while being strictly smaller (`Lemma3`, `Lemma3_lt`).
-/

@[expose] public section

universe u v w z

namespace UniformConstrained

open scoped Space

/-! ## The lazy oracles -/

/-- The paper's `universal` and `inspectsFst`, which observe the Haskell runtime:

- `universal :: (a → Bool) → Maybe Bool` — "`Nothing` if the predicate need to inspects its argument
  to yield a result, and `Just True` if the predicate is universally true and `Just False` if is
  universally false"; implementing it "involves applying the predicate to `⊥` and catching the
  resulting exception".
- `inspectsFst :: ((a, b) → Bool) → Bool` — "`True` iff `p` evaluates the first component of the
  pair before the second".

Lean has no `⊥`-catching and no evaluation-order reflection, so these are parameters. Only the
soundness of `universal` is assumed — a `some b` answer is correct — and it is all that
`card_sizedP`, Lemmas 2–3 and Theorem 2 use. A `universal` that always answers `none` qualifies; it
makes `sizedP` never prune. Nothing is assumed of `inspectsFst`: it only chooses an order, and every
order gives the same multisets. -/
structure LazyOracle where
  /-- The paper's `universal :: (a → Bool) → Maybe Bool`. -/
  universal : {α : Type} → (α → Bool) → Option Bool
  /-- The paper's `inspectsFst :: ((a, b) → Bool) → Bool`. -/
  inspectsFst : {α β : Type} → (α × β → Bool) → Bool
  /-- `universal p = some b` means `p` really is constantly `b`. -/
  universal_sound : ∀ {α : Type} (p : α → Bool) (b : Bool),
    universal p = some b → ∀ x, p x = b

namespace LazyOracle

variable (O : LazyOracle)

/-- The paper's stated law for `inspectsFst` (Section 4, Lemma 2 discussion): "`inspectsFst` is
required to interact in a standard way with functions like `swap`, for example satisfying the law
`inspectsFst p ⇒ not (inspectsFst (p ∘ swap))`".

It is not a field of `LazyOracle`. The paper needs it only for termination, which `fuel` replaces
here and which it does not ensure anyway (`cycleOracle_swapLaw`). And since Lean functions are
extensional, it forces `inspectsFst p = false` whenever `p ∘ swap = p`, which excludes Section 4.1's
racy oracle (`racyRound_race_TF`). -/
def SwapLaw : Prop :=
  ∀ {α β : Type} (p : α × β → Bool), O.inspectsFst p = true → O.inspectsFst (p ∘ Prod.swap) = false

theorem universal_true {α : Type} {p : α → Bool} (h : O.universal p = some true) (x : α) :
    p x = true := O.universal_sound p true h x

theorem universal_false {α : Type} {p : α → Bool} (h : O.universal p = some false) (x : α) :
    p x = false := O.universal_sound p false h x

end LazyOracle

/-! ## `sizedP` (Figure 2) -/

/-- The paper's `apply` helper from the `(:$:)` case of Figure 2:

```haskell
apply f x = case x of Left  x → Left  (f x)
                      Right a → Right (f :$: a)
```

It pushes an `fmap` through the `Either`: a value gets `f` applied, a residual space gets `f :$: ·`.
-/
def applyE {α β : Type} (f : α → β) : α ⊕ Space α → β ⊕ Space β
  | .inl x => .inl (f x)
  | .inr a => .inr (f :$: a)

/-- The paper's `rebuild` helper from the `(:+:)` case of Figure 2:

```haskell
rebuild :: (Space a → Space a) → Set (Either a (Space a)) → Set (Either a (Space a))
rebuild f = fmap (fmap f)
```

It applies `f` to every residual space in the multiset, leaving values alone. -/
def rebuild {α : Type} (f : Space α → Space α) :
    FinSet (α ⊕ Space α) → FinSet (α ⊕ Space α) :=
  FinSet.fmap (Sum.map id f)

/-- The paper's `sizedP :: (a → Bool) → Space a → Int → Set (Either a (Space a))` (Figure 2),
with an explicit `fuel` bound in place of the paper's `(k, r, q)` convergence measure:

```haskell
sizedP p (f :$: a) k = case universal p' of
    Just False → replicateSet |sized a k| (Right Empty)
    _          → fmap (apply f) (sizedP p' a k)
  where p' = p ∘ f
sizedP p (a :*: b) k = if inspectsFst p then sizedP p (swap :$: (b *** a)) k
                                        else sizedP p (a *** b) k
  where swap (a, b) = (b, a)
sizedP p (a :+: b) k = rebuild (:+: b) (sizedP p a k) ⊎ rebuild (a :+:) (sizedP p b k)
sizedP p (Pay a) k | k > 0 = fmap (fmap Pay) $ sizedP p a (k - 1)
sizedP p (Pure a) 0 | p a       = {Left a}
                    | otherwise = {Right Empty}
sizedP _ _ _ = {}
```

Returns `none` exactly when the fuel runs out. The `(:*:)` case recurses through `***`, which is not
structural, and the paper's measure for it is "a little intricate to construct"; with fuel, every
result below is conditional on `sizedP` returning `some`, as the paper's Lemmas 2 and 3 are about
invocations that terminate. -/
def sizedP (O : LazyOracle) :
    Nat → {α : Type} → (α → Bool) → Space α → Nat → Option (FinSet (α ⊕ Space α))
  | 0, _, _, _, _ => none
  | fuel + 1, _, p, s, k =>
    match s, k with
    | .fmap f a, k =>
      -- `p' = p ∘ f`. When `p'` is universally false, every value of size `k` fails, so the whole
      -- space of that size is discarded — but `replicateSet` keeps the *cardinality* the same.
      if O.universal (p ∘ f) = some false then
        some (.replicateSet (Space.sized a k).card (.inr .empty))
      else
        (sizedP O fuel (p ∘ f) a k).map (FinSet.fmap (applyE f))
    | .prod a b, k =>
      -- Section 3.1: which component to refine is decided by the predicate's evaluation order. In
      -- the `inspectsFst` branch the operands are swapped before applying `***`, and `swap :$: ·`
      -- puts the pair back the right way round, so the predicate is unchanged.
      if O.inspectsFst p then
        sizedP O fuel p (Prod.swap :$: (b *** a)) k
      else
        sizedP O fuel p (a *** b) k
    | .union a b, k =>
      match sizedP O fuel p a k, sizedP O fuel p b k with
      | some sa, some sb =>
        some ((rebuild (· :+: b) sa).union (rebuild (a :+: ·) sb))
      | _, _ => none
    | .pay a, 0 => some .empty
    | .pay a, k + 1 => (sizedP O fuel p a k).map (rebuild Space.pay)
    | .pure a, 0 => some (if p a then .single (.inl a) else .single (.inr .empty))
    | .pure _, _ + 1 => some .empty
    | .empty, _ => some .empty

/-- **More fuel never changes a `some` answer.** `sizedP` only fails by running out of fuel, so a run
that succeeds with `fuel` succeeds identically with any larger fuel. -/
theorem sizedP_succ_of_eq_some (O : LazyOracle) : ∀ (fuel : Nat) {α : Type} (p : α → Bool)
    (s : Space α) (k : Nat) (r : FinSet (α ⊕ Space α)), sizedP O fuel p s k = some r →
    sizedP O (fuel + 1) p s k = some r := by
  intro fuel
  induction fuel with
  | zero => intro _ p s k r h; simp [sizedP] at h
  | succ fuel ih =>
    intro α p s k r h
    match s, k, h with
    | .empty, _, h | .pure _, 0, h | .pure _, _ + 1, h | .pay _, 0, h => simpa [sizedP] using h
    | .pay a, k + 1, h =>
      simp only [sizedP, Option.map_eq_some_iff] at h
      rw [sizedP, Option.map_eq_some_iff]
      obtain ⟨r', hr', rfl⟩ := h
      exact ⟨r', ih p a k r' hr', rfl⟩
    | .union a b, k, h =>
      simp only [sizedP] at h
      rw [sizedP]
      split at h
      · rename_i sa sb hsa hsb
        rw [ih p a k sa hsa, ih p b k sb hsb]
        exact h
      · simp at h
    | .fmap f a, k, h =>
      simp only [sizedP] at h
      rw [sizedP]
      split at h
      · rename_i hu; rw [ite_eq_left hu]; exact h
      · rename_i hu
        rw [ite_eq_right hu]
        obtain ⟨r', hr', rfl⟩ := Option.map_eq_some_iff.mp h
        rw [ih _ a k r' hr']
        rfl
    | .prod a b, k, h =>
      simp only [sizedP] at h
      rw [sizedP]
      split at h
      · rename_i hi; rw [ite_eq_left hi]; exact ih _ _ k r h
      · rename_i hi; rw [ite_eq_right hi]; exact ih _ _ k r h

theorem sizedP_mono (O : LazyOracle) {fuel fuel' : Nat} (hle : fuel ≤ fuel') {α : Type}
    {p : α → Bool} {s : Space α} {k : Nat} {r : FinSet (α ⊕ Space α)}
    (h : sizedP O fuel p s k = some r) : sizedP O fuel' p s k = some r := by
  induction hle with
  | refl => exact h
  | step _ ih => exact sizedP_succ_of_eq_some O _ p s k r ih

/-! ### `|sizedP p s k| = |sized s k|`

"A key point of `sizedP` is that the cardinality of the resulting set does not depend on the
predicate. In fact, it is always the case that `|sizedP p s k| = |sized s k|`, in other words the
result of `sizedP` contains one element for every value of size `k` regardless of how many of them
satisfy `p`." This is what makes the residual index arithmetic in `uniform` uniform, and hence it is
the load-bearing invariant for Theorem 2. -/

/-- **The paper's key invariant: `|sizedP p s k| = |sized s k|`.** -/
theorem card_sizedP (O : LazyOracle) : ∀ (fuel : Nat) {α : Type} (p : α → Bool)
    (s : Space α) (k : Nat) (r : FinSet (α ⊕ Space α)), sizedP O fuel p s k = some r →
    r.card = (Space.sized s k).card := by
  intro fuel
  induction fuel with
  | zero => intro _ p s k r h; simp [sizedP] at h
  | succ fuel ih =>
    intro α p s k r h
    match s, k, h with
    | .empty, k, h => simp only [sizedP] at h; cases h; simp
    | .pure a, 0, h =>
      simp only [sizedP] at h
      cases h
      by_cases hp : p a <;> simp [hp]
    | .pure a, k + 1, h => simp only [sizedP] at h; cases h; simp
    | .pay a, 0, h => simp only [sizedP] at h; cases h; simp
    | .pay a, k + 1, h =>
      simp only [sizedP, Option.map_eq_some_iff] at h
      obtain ⟨r', hr', rfl⟩ := h
      rw [Space.sized_pay_succ, rebuild, FinSet.card_fmap]
      exact ih p a k r' hr'
    | .union a b, k, h =>
      simp only [sizedP] at h
      split at h
      · rename_i sa sb hsa hsb
        cases h
        rw [Space.sized_union, rebuild, rebuild, FinSet.card_union, FinSet.card_union,
          FinSet.card_fmap, FinSet.card_fmap, ih p a k sa hsa, ih p b k sb hsb]
      · simp at h
    | .fmap f a, k, h =>
      simp only [sizedP] at h
      split at h
      · cases h; simp
      · rw [Option.map_eq_some_iff] at h
        obtain ⟨r', hr', rfl⟩ := h
        rw [Space.sized_fmap, FinSet.card_fmap, FinSet.card_fmap]
        exact ih (p ∘ f) a k r' hr'
    | .prod a b, k, h =>
      simp only [sizedP] at h
      split at h
      · -- The `inspectsFst` branch: `swap :$: (b *** a)` has the same cardinality, by Lemma 1 and
        -- commutativity of space products.
        rw [ih _ _ k r h, Space.sized_fmap, FinSet.card_fmap, Space.card_sized_prodR,
          Space.card_sized_prod_comm]
      · rw [ih _ _ k r h, Space.card_sized_prodR]

/-! ## Splitting a `sizedP` result into values and residual spaces

The paper writes the two halves of a `sizedP` result as `{x | Left x ∈ sizedP p s k}` and
`{s' | Right s' ∈ sizedP p s k}`. As multisets those are `filterMap`s along `Sum.getLeft?` and
`Sum.getRight?`. -/

/-- The paper's `{x | Left x ∈ r}`: the values `sizedP` has committed to, as a multiset. -/
def lefts {α : Type} (r : FinSet (α ⊕ Space α)) : Multiset α :=
  r.toMultiset.filterMap Sum.getLeft?

/-- The paper's `{s' | Right s' ∈ r}`: the residual spaces, as a multiset. -/
def rights {α : Type} (r : FinSet (α ⊕ Space α)) : Multiset (Space α) :=
  r.toMultiset.filterMap Sum.getRight?

section SumHelpers

variable {α : Type u} {β : Type v} {γ : Type w} {δ : Type z}

/-- `Sum.map` commutes with taking the `Left`s. -/
private theorem filterMap_getLeft?_map_sumMap (M : Multiset (α ⊕ β)) (f : α → γ) (g : β → δ) :
    ((M.map (Sum.map f g)).filterMap Sum.getLeft?) = (M.filterMap Sum.getLeft?).map f := by
  rw [Multiset.filterMap_map, Multiset.map_filterMap]
  exact congrArg (fun h => Multiset.filterMap h M) (funext fun x => by cases x <;> rfl)

/-- `Sum.map` commutes with taking the `Right`s. -/
private theorem filterMap_getRight?_map_sumMap (M : Multiset (α ⊕ β)) (f : α → γ) (g : β → δ) :
    ((M.map (Sum.map f g)).filterMap Sum.getRight?) = (M.filterMap Sum.getRight?).map g := by
  rw [Multiset.filterMap_map, Multiset.map_filterMap]
  exact congrArg (fun h => Multiset.filterMap h M) (funext fun x => by cases x <;> rfl)

/-- A multiset of `Right`s contributes no `Left`s. -/
private theorem filterMap_getLeft?_replicate (n : Nat) (b : β) :
    ((Multiset.replicate n (Sum.inr b : α ⊕ β)).filterMap Sum.getLeft?) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Multiset.replicate_succ, Multiset.filterMap_cons_none (f := Sum.getLeft?) _ _ rfl, ih]

/-- …and contributes each of them as a `Right`. -/
private theorem filterMap_getRight?_replicate (n : Nat) (b : β) :
    ((Multiset.replicate n (Sum.inr b : α ⊕ β)).filterMap Sum.getRight?)
      = Multiset.replicate n b := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Multiset.replicate_succ, Multiset.filterMap_cons_some Sum.getRight? _ _ (b := b) rfl, ih,
      Multiset.replicate_succ]

/-- The `Left`s and the `Right`s together account for every occurrence. Used in Theorem 2 to turn
`|sizedP p s k| = n` and `|lefts| = m` into `|rights| = n - m`. -/
theorem card_filterMap_getLeft?_add_getRight? (M : Multiset (α ⊕ β)) :
    (M.filterMap Sum.getLeft?).card + (M.filterMap Sum.getRight?).card = M.card := by
  refine Multiset.induction_on M (by simp) fun a s ih => ?_
  cases a with
  | inl y =>
    rw [Multiset.filterMap_cons_some Sum.getLeft? _ _ (b := y) rfl,
      Multiset.filterMap_cons_none (f := Sum.getRight?) _ _ rfl]
    simp only [Multiset.card_cons]; omega
  | inr y =>
    rw [Multiset.filterMap_cons_none (f := Sum.getLeft?) _ _ rfl,
      Multiset.filterMap_cons_some Sum.getRight? _ _ (b := y) rfl]
    simp only [Multiset.card_cons]; omega

end SumHelpers

/-- `applyE` is exactly `Sum.map` of `f` and `f :$: ·`. -/
theorem applyE_eq_sumMap {α β : Type} (f : α → β) :
    applyE f = Sum.map f (Space.fmap f) := by
  funext x; cases x <;> rfl

@[simp] theorem lefts_empty {α : Type} : lefts (FinSet.empty : FinSet (α ⊕ Space α)) = 0 := rfl
@[simp] theorem rights_empty {α : Type} : rights (FinSet.empty : FinSet (α ⊕ Space α)) = 0 := rfl

@[simp] theorem lefts_single_inl {α : Type} (a : α) :
    lefts (FinSet.single (Sum.inl a : α ⊕ Space α)) = {a} := rfl
@[simp] theorem rights_single_inl {α : Type} (a : α) :
    rights (FinSet.single (Sum.inl a : α ⊕ Space α)) = 0 := rfl
@[simp] theorem lefts_single_inr {α : Type} (t : Space α) :
    lefts (FinSet.single (Sum.inr t : α ⊕ Space α)) = 0 := rfl
@[simp] theorem rights_single_inr {α : Type} (t : Space α) :
    rights (FinSet.single (Sum.inr t : α ⊕ Space α)) = {t} := rfl

@[simp] theorem lefts_union {α : Type} (r₁ r₂ : FinSet (α ⊕ Space α)) :
    lefts (r₁.union r₂) = lefts r₁ + lefts r₂ := by
  simp only [lefts, FinSet.toMultiset_union, Multiset.filterMap_add]

@[simp] theorem rights_union {α : Type} (r₁ r₂ : FinSet (α ⊕ Space α)) :
    rights (r₁.union r₂) = rights r₁ + rights r₂ := by
  simp only [rights, FinSet.toMultiset_union, Multiset.filterMap_add]

@[simp] theorem lefts_replicateSet_inr {α : Type} (n : Nat) (t : Space α) :
    lefts (FinSet.replicateSet n (Sum.inr t : α ⊕ Space α)) = 0 :=
  filterMap_getLeft?_replicate n t

@[simp] theorem rights_replicateSet_inr {α : Type} (n : Nat) (t : Space α) :
    rights (FinSet.replicateSet n (Sum.inr t : α ⊕ Space α)) = Multiset.replicate n t :=
  filterMap_getRight?_replicate n t

/-- `rebuild` only touches residual spaces, so it does not change the values. This is what makes the
`(:+:)` and `Pay` cases of Lemma 2 immediate. -/
@[simp] theorem lefts_rebuild {α : Type} (f : Space α → Space α) (r : FinSet (α ⊕ Space α)) :
    lefts (rebuild f r) = lefts r := by
  simp only [lefts, rebuild, FinSet.toMultiset_fmap,
    filterMap_getLeft?_map_sumMap _ (id : α → α) f, Multiset.map_id]

/-- Dually, `rebuild f` applies `f` to every residual space. -/
@[simp] theorem rights_rebuild {α : Type} (f : Space α → Space α) (r : FinSet (α ⊕ Space α)) :
    rights (rebuild f r) = (rights r).map f := by
  simp only [rights, rebuild, FinSet.toMultiset_fmap,
    filterMap_getRight?_map_sumMap _ (id : α → α) f]

/-- `fmap (applyE f)` maps `f` over the values. -/
@[simp] theorem lefts_fmap_applyE {α β : Type} (f : α → β) (r : FinSet (α ⊕ Space α)) :
    lefts (r.fmap (applyE f)) = (lefts r).map f := by
  simp only [lefts, FinSet.toMultiset_fmap, applyE_eq_sumMap,
    filterMap_getLeft?_map_sumMap _ f (Space.fmap f)]

/-- …and `f :$: ·` over the residual spaces. -/
@[simp] theorem rights_fmap_applyE {α β : Type} (f : α → β) (r : FinSet (α ⊕ Space α)) :
    rights (r.fmap (applyE f)) = (rights r).map (Space.fmap f) := by
  simp only [rights, FinSet.toMultiset_fmap, applyE_eq_sumMap,
    filterMap_getRight?_map_sumMap _ f (Space.fmap f)]

/-- The cardinality split, for `sizedP` results: `|lefts r| + |rights r| = |r|`. -/
theorem card_lefts_add_card_rights {α : Type} (r : FinSet (α ⊕ Space α)) :
    (lefts r).card + (rights r).card = r.card := by
  rw [lefts, rights, card_filterMap_getLeft?_add_getRight?, FinSet.card_toMultiset]

/-! ## Lemma 2: `sizedP` finds exactly the satisfying values

`satisfying p s k` (from `Uniform`) is the paper's `{x | x ∈ sized s k, p x}`. -/

/-- `satisfying` only looks at the multiset of values of size `k`. -/
theorem satisfying_congr {α : Type} {p : α → Bool} {s t : Space α} {k : Nat}
    (h : (Space.sized s k).toMultiset = (Space.sized t k).toMultiset) :
    satisfying p s k = satisfying p t k := by
  simp only [satisfying, allOfSize, h]

@[simp] theorem satisfying_empty {α : Type} (p : α → Bool) (k : Nat) :
    satisfying p (Space.empty : Space α) k = 0 := rfl

@[simp] theorem satisfying_pure_succ {α : Type} (p : α → Bool) (a : α) (k : Nat) :
    satisfying p (Space.pure a) (k + 1) = 0 := rfl

@[simp] theorem satisfying_pay_zero {α : Type} (p : α → Bool) (s : Space α) :
    satisfying p s.pay 0 = 0 := rfl

/-- `Pay` shifts the size index: the values of size `k + 1` in `Pay s` satisfying `p` are exactly the
values of size `k` in `s` satisfying `p`. This is `Space.sized_pay_succ` (which is `rfl`) transported
through `satisfying`. -/
@[simp] theorem satisfying_pay_succ {α : Type} (p : α → Bool) (s : Space α) (k : Nat) :
    satisfying p s.pay (k + 1) = satisfying p s k := rfl

theorem satisfying_pure_zero {α : Type} (p : α → Bool) (a : α) :
    satisfying p (Space.pure a) 0 = if p a then {a} else 0 := by
  classical
  simp only [satisfying, allOfSize, Space.sized_pure_zero, FinSet.toMultiset_single,
    Multiset.filter_singleton]
  by_cases h : p a <;> simp [h]

theorem satisfying_union {α : Type} (p : α → Bool) (a b : Space α) (k : Nat) :
    satisfying p (a :+: b) k = satisfying p a k + satisfying p b k := by
  classical
  simp only [satisfying, allOfSize, Space.sized_union, FinSet.toMultiset_union,
    Multiset.filter_add]

theorem satisfying_fmap {α β : Type} (p : β → Bool) (f : α → β) (a : Space α) (k : Nat) :
    satisfying p (f :$: a) k = (satisfying (p ∘ f) a k).map f := by
  classical
  simp only [satisfying, allOfSize, Space.sized_fmap, FinSet.toMultiset_fmap, Multiset.filter_map]
  rfl

/-- A universally-false predicate has nothing satisfying it. This is the paper's remark that in the
`universal p' = Just False` subcase "both sides of the equation [are] equal to `{}`". -/
theorem satisfying_eq_zero_of_universal_false {α β : Type} (O : LazyOracle) {p : β → Bool}
    {f : α → β} (h : O.universal (p ∘ f) = some false) (a : Space α) (k : Nat) :
    satisfying (p ∘ f) a k = 0 := by
  classical
  exact Multiset.filter_eq_nil.mpr fun x _ => by simpa using O.universal_false h x

/-- **Lemma 2 (Claessen–Duregård–Pałka).**

> Let `s :: Space a` be a space, `p :: a → Bool` a boolean predicate, and `k :: Int` a non-negative
> integer. Then, the following equivalence holds between multisets:
> `{x | Left x ∈ sizedP p s k} = {x | x ∈ sized s k, p x}`

"The next lemma contains most of the complexity of the proof. It shows that values of the form
`Left x` in the multiset returned by `sizedP p s k` contains exactly the subset of values returned by
`sized s k` that satisfy `p`."

The paper's proof is "by induction and case analysis of `sizedP`", with `(:*:)` and `(:$:)` the
interesting cases. Here the induction is on `fuel`; the `(:*:)` case is where Lemma 1 and
commutativity of space products are used (packaged as `Space.toMultiset_sized_swap_prodR`), and the
`(:$:)` case is where `universal`'s soundness is used to justify discarding the whole space. -/
theorem Lemma2 (O : LazyOracle) : ∀ (fuel : Nat) {α : Type} (p : α → Bool) (s : Space α) (k : Nat)
    (r : FinSet (α ⊕ Space α)), sizedP O fuel p s k = some r → lefts r = satisfying p s k := by
  intro fuel
  induction fuel with
  | zero => intro _ p s k r h; simp [sizedP] at h
  | succ fuel ih =>
    intro α p s k r h
    match s, k, h with
    | .empty, k, h => simp only [sizedP] at h; cases h; simp
    | .pure a, 0, h =>
      simp only [sizedP] at h
      cases h
      rw [satisfying_pure_zero]
      by_cases hp : p a <;> simp [hp]
    | .pure a, k + 1, h => simp only [sizedP] at h; cases h; simp
    | .pay a, 0, h => simp only [sizedP] at h; cases h; simp
    | .pay a, k + 1, h =>
      simp only [sizedP, Option.map_eq_some_iff] at h
      obtain ⟨r', hr', rfl⟩ := h
      rw [lefts_rebuild, ih p a k r' hr', satisfying_pay_succ]
    | .union a b, k, h =>
      -- `distributivity of filter over ⊎`.
      simp only [sizedP] at h
      split at h
      · rename_i sa sb hsa hsb
        cases h
        rw [lefts_union, lefts_rebuild, lefts_rebuild, ih p a k sa hsa, ih p b k sb hsb,
          satisfying_union]
      · simp at h
    | .fmap f a, k, h =>
      simp only [sizedP] at h
      split at h
      · -- `universal (p ∘ f) = Just False`: "both sides of the equation being equal to `{}`".
        rename_i huniv
        cases h
        rw [show lefts (FinSet.replicateSet (Space.sized a k).card
            (Sum.inr Space.empty : α ⊕ Space α)) = 0 from
          filterMap_getLeft?_replicate _ _, satisfying_fmap,
          satisfying_eq_zero_of_universal_false O huniv a k, Multiset.map_zero]
      · -- The recursive case: `f` is mapped over both sides.
        rw [Option.map_eq_some_iff] at h
        obtain ⟨r', hr', rfl⟩ := h
        rw [lefts_fmap_applyE, ih (p ∘ f) a k r' hr', satisfying_fmap]
    | .prod a b, k, h =>
      -- The paper's chain of equational steps, with Lemma 1 and commutativity of space products
      -- bundled into `Space.toMultiset_sized_swap_prodR`.
      simp only [sizedP] at h
      split at h
      · rw [ih _ _ k r h]
        exact satisfying_congr (Space.toMultiset_sized_swap_prodR a b k)
      · rw [ih _ _ k r h]
        exact satisfying_congr (Space.Lemma1 a b k).symm

/-! ## Lemma 3: the residual spaces retain every satisfying value

"If indexing in the result of `sizedP` hits an element that does not satisfy the predicate, the
result is `Right s`, where `s` is the residual space, which is used by `uniform` to continue
sampling. We show that the spaces returned by `sizedP` retain all elements from the original space
that satisfy the predicate, and are strictly smaller than the original space." -/

/-- **Lemma 3, first half (Claessen–Duregård–Pałka).**

> Let `s` be a space, `p` a boolean predicate, `k` a non-negative integer, and
> `Right s' ∈ sizedP p s k`. Then the following equation between multisets holds:
> `{x | x ∈ sized s k, p x} = {x | x ∈ sized s' k, p x}`

So restarting the search in a residual space loses no candidate: this is what lets Theorem 2's
induction step appeal to the induction hypothesis at `s'`. -/
theorem Lemma3 (O : LazyOracle) : ∀ (fuel : Nat) {α : Type} (p : α → Bool) (s : Space α) (k : Nat)
    (r : FinSet (α ⊕ Space α)), sizedP O fuel p s k = some r → ∀ s' ∈ rights r,
    satisfying p s' k = satisfying p s k := by
  intro fuel
  induction fuel with
  | zero => intro _ p s k r h; simp [sizedP] at h
  | succ fuel ih =>
    intro α p s k r h
    match s, k, h with
    | .empty, k, h => simp only [sizedP] at h; cases h; simp
    | .pure a, 0, h =>
      simp only [sizedP] at h
      cases h
      intro s' hs'
      by_cases hp : p a
      · simp [hp] at hs'
      · -- The residual is `Empty`, and `Pure a` had no satisfying values either.
        simp only [hp, Bool.false_eq_true, ite_false, rights_single_inr,
          Multiset.mem_singleton] at hs'
        rw [hs', satisfying_pure_zero, ite_eq_right hp, satisfying_empty]
    | .pure a, k + 1, h => simp only [sizedP] at h; cases h; simp
    | .pay a, 0, h => simp only [sizedP] at h; cases h; simp
    | .pay a, k + 1, h =>
      simp only [sizedP, Option.map_eq_some_iff] at h
      obtain ⟨r', hr', rfl⟩ := h
      intro s' hs'
      -- Residuals of `Pay a` are `Pay` of residuals of `a`, and `sized (Pay t) (k+1) = sized t k`.
      rw [rights_rebuild, Multiset.mem_map] at hs'
      obtain ⟨t, ht, rfl⟩ := hs'
      rw [satisfying_pay_succ, satisfying_pay_succ, ih p a k r' hr' t ht]
    | .union a b, k, h =>
      simp only [sizedP] at h
      split at h
      · rename_i sa sb hsa hsb
        cases h
        intro s' hs'
        -- A residual is either `s'a :+: b` or `a :+: s'b`; either way `filter` distributes.
        rw [rights_union, rights_rebuild, rights_rebuild, Multiset.mem_add] at hs'
        rcases hs' with hs' | hs'
        · obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.mp hs'
          rw [satisfying_union, satisfying_union, ih p a k sa hsa t ht]
        · obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.mp hs'
          rw [satisfying_union, satisfying_union, ih p b k sb hsb t ht]
      · simp at h
    | .fmap f a, k, h =>
      simp only [sizedP] at h
      split at h
      · -- Nothing of size `k` satisfies `p`, so both sides are `{}`.
        rename_i huniv
        cases h
        intro s' hs'
        rw [rights_replicateSet_inr] at hs'
        rw [Multiset.eq_of_mem_replicate hs', satisfying_empty, satisfying_fmap,
          satisfying_eq_zero_of_universal_false O huniv a k, Multiset.map_zero]
      · rw [Option.map_eq_some_iff] at h
        obtain ⟨r', hr', rfl⟩ := h
        intro s' hs'
        -- Residuals of `f :$: a` are `f :$:` residuals of `a`; `filter` commutes with `map f`.
        rw [rights_fmap_applyE, Multiset.mem_map] at hs'
        obtain ⟨t, ht, rfl⟩ := hs'
        rw [satisfying_fmap, satisfying_fmap, ih (p ∘ f) a k r' hr' t ht]
    | .prod a b, k, h =>
      simp only [sizedP] at h
      split at h
      · intro s' hs'
        rw [ih _ _ k r h s' hs']
        exact satisfying_congr (Space.toMultiset_sized_swap_prodR a b k)
      · intro s' hs'
        rw [ih _ _ k r h s' hs']
        exact satisfying_congr (Space.Lemma1 a b k).symm

/-- **Lemma 3, second half**: "Furthermore, `sized s' k` is a proper subset of `sized s k`."

This is the well-foundedness of `uniform`'s outer loop in the paper's argument: every retry strictly
shrinks the space, so `n = |sized s k|` decreases and Theorem 2's induction on `n` is legitimate. -/
theorem Lemma3_lt (O : LazyOracle) : ∀ (fuel : Nat) {α : Type} (p : α → Bool) (s : Space α)
    (k : Nat) (r : FinSet (α ⊕ Space α)), sizedP O fuel p s k = some r → ∀ s' ∈ rights r,
    (Space.sized s' k).toMultiset < (Space.sized s k).toMultiset := by
  intro fuel
  induction fuel with
  | zero => intro _ p s k r h; simp [sizedP] at h
  | succ fuel ih =>
    intro α p s k r h
    match s, k, h with
    | .empty, k, h => simp only [sizedP] at h; cases h; simp
    | .pure a, 0, h =>
      simp only [sizedP] at h
      cases h
      intro s' hs'
      by_cases hp : p a
      · simp [hp] at hs'
      · simp only [hp, Bool.false_eq_true, ite_false, rights_single_inr,
          Multiset.mem_singleton] at hs'
        rw [hs']
        simp
    | .pure a, k + 1, h => simp only [sizedP] at h; cases h; simp
    | .pay a, 0, h => simp only [sizedP] at h; cases h; simp
    | .pay a, k + 1, h =>
      simp only [sizedP, Option.map_eq_some_iff] at h
      obtain ⟨r', hr', rfl⟩ := h
      intro s' hs'
      rw [rights_rebuild, Multiset.mem_map] at hs'
      obtain ⟨t, ht, rfl⟩ := hs'
      rw [Space.sized_pay_succ, Space.sized_pay_succ]
      exact ih p a k r' hr' t ht
    | .union a b, k, h =>
      simp only [sizedP] at h
      split at h
      · rename_i sa sb hsa hsb
        cases h
        intro s' hs'
        rw [rights_union, rights_rebuild, rights_rebuild, Multiset.mem_add] at hs'
        rcases hs' with hs' | hs'
        · obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.mp hs'
          simp only [Space.sized_union, FinSet.toMultiset_union]
          exact add_lt_add_of_lt_of_le (ih p a k sa hsa t ht) le_rfl
        · obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.mp hs'
          simp only [Space.sized_union, FinSet.toMultiset_union]
          exact add_lt_add_of_le_of_lt le_rfl (ih p b k sb hsb t ht)
      · simp at h
    | .fmap f a, k, h =>
      simp only [sizedP] at h
      split at h
      · -- The whole space is discarded, and it was non-empty: otherwise there is no residual to
        -- speak of, since `replicateSet 0 _` has no occurrences.
        cases h
        intro s' hs'
        rw [rights_replicateSet_inr] at hs'
        have hpos : 0 < (Space.sized a k).card :=
          Nat.pos_of_ne_zero (Multiset.mem_replicate.mp hs').1
        rw [Multiset.eq_of_mem_replicate hs']
        simp only [Space.sized_empty, Space.sized_fmap, FinSet.toMultiset_empty,
          FinSet.toMultiset_fmap]
        refine lt_of_le_of_ne (Multiset.zero_le _) (Ne.symm ?_)
        rw [Ne, ← Multiset.card_eq_zero, Multiset.card_map, FinSet.card_toMultiset]
        omega
      · rw [Option.map_eq_some_iff] at h
        obtain ⟨r', hr', rfl⟩ := h
        intro s' hs'
        rw [rights_fmap_applyE, Multiset.mem_map] at hs'
        obtain ⟨t, ht, rfl⟩ := hs'
        simp only [Space.sized_fmap, FinSet.toMultiset_fmap]
        exact Multiset.map_lt_map (ih (p ∘ f) a k r' hr' t ht)
    | .prod a b, k, h =>
      simp only [sizedP] at h
      split at h
      · intro s' hs'
        rw [← Space.toMultiset_sized_swap_prodR a b k]
        exact ih _ _ k r h s' hs'
      · intro s' hs'
        rw [Space.Lemma1 a b k]
        exact ih _ _ k r h s' hs'

end UniformConstrained
