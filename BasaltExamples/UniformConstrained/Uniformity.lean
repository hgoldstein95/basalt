/-
Copyright (c) 2026 Harrison Goldstein & Ernest Ng. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Ernest Ng
-/
module

public import BasaltExamples.UniformConstrained.Predicate

/-!
# The predicate-guided sampler `uniform`, Theorem 2, and Section 4.1

`uniform` is the paper's sampler over `sizedP` (Section 3). Its fuel can run out on a residual
space, so Theorem 2 is proved conditional on producing a value, for every oracle and fuel
(`Theorem2`). Section 4.1's racy oracle shows determinism is needed.
-/

@[expose] public section

open Lean.Order RandomChoice ENNReal

namespace UniformConstrained

open scoped Space

universe u v

variable {α : Type}

/-! ## Sums over a `sizedP` result -/

/-- Summing a function of an `Either` splits into the `Left`s and the `Right`s. -/
theorem sum_map_sumElim {α : Type u} {β : Type v} (M : Multiset (α ⊕ β)) (f : α → ℝ≥0∞) (g : β → ℝ≥0∞) :
    (M.map (Sum.elim f g)).sum
      = ((M.filterMap Sum.getLeft?).map f).sum + ((M.filterMap Sum.getRight?).map g).sum := by
  refine Multiset.induction_on M (by simp) fun a s ih => ?_
  cases a with
  | inl y =>
    rw [Multiset.filterMap_cons_some Sum.getLeft? _ _ (b := y) rfl,
      Multiset.filterMap_cons_none (f := Sum.getRight?) _ _ rfl]
    simp only [Multiset.map_cons, Multiset.sum_cons, Sum.elim_inl, ih]
    rw [add_assoc]
  | inr y =>
    rw [Multiset.filterMap_cons_none (f := Sum.getLeft?) _ _ rfl,
      Multiset.filterMap_cons_some Sum.getRight? _ _ (b := y) rfl]
    simp only [Multiset.map_cons, Multiset.sum_cons, Sum.elim_inr, ih]
    rw [add_left_comm]

/-! ## `uniform` -/

section UniformDef

variable {G : Type → Type} [Gen G]

/-- The paper's `uniform :: (a → Bool) → Space a → Int → Random a` (Section 3):

```haskell
uniform p s k = do
  x ← uniformSet (sizedP p s k)
  case x of Left a → return a
            Right s' → uniform p s' k
```

`uniformSet` is inlined as the paper defines it, a uniform index followed by `indexSet`: an element
of the multiset `sizedP` returns has type `α ⊕ Space α : Type 1`, which `G : Type → Type` cannot
return. The
result is `Option α`: `none` when `sizedP` runs out of fuel, and at an empty multiset, where the
paper's `uniformSet` raises `error "empty set"`. -/
def uniform (O : LazyOracle) (fuel : Nat) (p : α → Bool) (s : Space α) (k : Nat) :
    G (Option α) :=
  match sizedP O fuel p s k with
  | none => pure none
  | some r => do
    let i ← chooseNat 0 (r.card - 1)
    match r.indexSet i with
    | some (.inl a) => pure (some a)
    | some (.inr s') => uniform O fuel p s' k
    | none => pure none
partial_fixpoint

theorem uniform_eq (O : LazyOracle) (fuel : Nat) (p : α → Bool) (s : Space α) (k : Nat) :
    (uniform O fuel p s k : G (Option α))
      = (match sizedP O fuel p s k with
        | none => pure none
        | some r => do
          let i ← chooseNat 0 (r.card - 1)
          match r.indexSet i with
          | some (.inl a) => pure (some a)
          | some (.inr s') => uniform O fuel p s' k
          | none => pure none) := by
  conv_lhs => rw [uniform]

end UniformDef

/-! ## One step of `uniform` -/

/-- **One iteration of `uniform`, as a probability.** When `sizedP` succeeds with result `r`, the
probability of `x` is a draw from the `|sized s k|` occurrences of `r`: the `Left x` occurrences
contribute `1` each — there are `count x (sized s k)` of them if `p x`, by Lemma 2, and none
otherwise — and each residual `Right s'` contributes a fresh run of `uniform` at `s'`. -/
theorem uniform_apply_some [DecidableEq α] (O : LazyOracle) (fuel : Nat) (p : α → Bool)
    (s : Space α) (k : Nat) {r : FinSet (α ⊕ Space α)} (hr : sizedP O fuel p s k = some r)
    (x : α) :
    (uniform O fuel p s k : SPMF (Option α)) (some x)
      = ((if p x then ((allOfSize s k).count x : ℝ≥0∞) else 0)
          + ((rights r).map fun s' => (uniform O fuel p s' k : SPMF (Option α)) (some x)).sum)
        / ((Space.sized s k).card : ℝ≥0∞) := by
  classical
  -- The continuation after the index draw, and what it contributes at each occurrence.
  set g : α ⊕ Space α → ℝ≥0∞ := Sum.elim (fun a => if x = a then 1 else 0)
    (fun s' => (uniform O fuel p s' k : SPMF (Option α)) (some x)) with hg
  have hcont : ∀ i, (match r.indexSet i with
        | some (.inl a) => (pure (some a) : SPMF (Option α))
        | some (.inr s') => uniform O fuel p s' k
        | none => pure none) (some x) = ((r.indexSet i).map g).getD 0 := by
    intro i
    rcases r.indexSet i with _ | (a | s') <;>
      simp [hg, SPMF.pure_apply, eq_comm]
  have hsum : (r.toMultiset.map g).sum
      = (if p x then ((allOfSize s k).count x : ℝ≥0∞) else 0)
        + ((rights r).map fun s' => (uniform O fuel p s' k : SPMF (Option α)) (some x)).sum := by
    rw [hg, sum_map_sumElim, sum_map_indicator]
    show ((lefts r).count x : ℝ≥0∞) + _ = _
    rw [Lemma2 O fuel p s k r hr, satisfying, Multiset.count_filter, Nat.cast_ite, Nat.cast_zero]
    rfl
  rw [uniform_eq, hr]
  dsimp only
  rcases Nat.eq_zero_or_pos r.card with h0 | hpos
  · -- An empty result: every index misses, and there is nothing on the right-hand side either.
    have hnil : r.toMultiset = 0 := by
      rw [← Multiset.card_eq_zero, FinSet.card_toMultiset, h0]
    rw [← hsum, hnil, Multiset.map_zero, Multiset.sum_zero, ENNReal.zero_div, SPMF.bind_apply,
      ENNReal.tsum_eq_zero]
    intro i
    rw [hcont, FinSet.indexSet_eq_none r (by omega), Option.map_none, Option.getD_none, mul_zero]
  · rw [chooseNat_bind_apply hpos, Finset.sum_congr rfl (fun i _ => hcont i),
      sum_range_indexSet_map, hsum, card_sizedP O fuel p s k r hr]


/-! ## Theorem 2 -/

/-- A residual space retains the satisfying occurrences, so it retains their counts. -/
theorem count_allOfSize_of_mem_rights [DecidableEq α] {O : LazyOracle} {fuel : Nat}
    {p : α → Bool} {s : Space α} {k : Nat} {r : FinSet (α ⊕ Space α)}
    (hr : sizedP O fuel p s k = some r) {s' : Space α} (hs' : s' ∈ rights r) {x : α}
    (hx : p x = true) : (allOfSize s' k).count x = (allOfSize s k).count x := by
  have h := congrArg (Multiset.count x) (Lemma3 O fuel p s k r hr s' hs')
  simpa [satisfying, Multiset.count_filter, hx] using h

theorem card_sized_lt_of_mem_rights {O : LazyOracle} {fuel : Nat} {p : α → Bool} {s : Space α}
    {k : Nat} {r : FinSet (α ⊕ Space α)} (hr : sizedP O fuel p s k = some r) {s' : Space α}
    (hs' : s' ∈ rights r) : (Space.sized s' k).card < (Space.sized s k).card := by
  rw [← FinSet.card_toMultiset, ← FinSet.card_toMultiset]
  exact Multiset.card_lt_card (Lemma3_lt O fuel p s k r hr s' hs')

/-- **Theorem 2, for every fuel: running out of fuel never favours one satisfying value.**

Whatever `fuel` is, the probability of each `x` satisfying `p` is its multiplicity in `sized s k`
times a constant `κ` that does not depend on `x`; values failing `p` have probability `0`. Running out of fuel discards a
whole residual space at once, and a residual space keeps every satisfying occurrence (Lemma 3), so
the loss is spread over the satisfying values in proportion to their multiplicities. -/
theorem Theorem2_prop [DecidableEq α] (O : LazyOracle) (fuel : Nat) (p : α → Bool)
    (s : Space α) (k : Nat) :
    ∃ κ : ℝ≥0∞, ∀ x, (uniform O fuel p s k : SPMF (Option α)) (some x)
      = if p x then ((allOfSize s k).count x : ℝ≥0∞) * κ else 0 := by
  induction hn : (Space.sized s k).card using Nat.strong_induction_on generalizing s with
  | _ n ih =>
  cases hr : sizedP O fuel p s k with
  | none =>
    refine ⟨0, fun x => ?_⟩
    rw [uniform_eq, hr]
    simp [SPMF.pure_apply]
  | some r =>
    -- One `κ` for each residual space, by the induction hypothesis.
    have ih' : ∀ s' ∈ rights r, ∃ κ : ℝ≥0∞, ∀ x,
        (uniform O fuel p s' k : SPMF (Option α)) (some x)
          = if p x then ((allOfSize s' k).count x : ℝ≥0∞) * κ else 0 := fun s' hs' =>
      ih _ (hn ▸ card_sized_lt_of_mem_rights hr hs') s' rfl
    choose! K hK using ih'
    refine ⟨(1 + ((rights r).map K).sum) / (n : ℝ≥0∞), fun x => ?_⟩
    rw [uniform_apply_some O fuel p s k hr, hn]
    by_cases hx : p x = true
    · have hterm : ∀ s' ∈ rights r, (uniform O fuel p s' k : SPMF (Option α)) (some x)
          = ((allOfSize s k).count x : ℝ≥0∞) * K s' := fun s' hs' => by
        rw [hK s' hs', ite_eq_left hx, count_allOfSize_of_mem_rights hr hs' hx]
      rw [Multiset.map_congr rfl hterm, Multiset.sum_map_mul_left, ite_eq_left hx, ite_eq_left hx,
        ← mul_one_add, mul_div_assoc]
    · have hterm : ∀ s' ∈ rights r, (uniform O fuel p s' k : SPMF (Option α)) (some x) = 0 :=
        fun s' hs' => by rw [hK s' hs', ite_eq_right (by simpa using hx)]
      rw [Multiset.map_congr rfl hterm, Multiset.map_const', Multiset.sum_replicate, smul_zero,
        ite_eq_right (by simpa using hx), ite_eq_right (by simpa using hx), zero_add,
        ENNReal.zero_div]

/-- **Theorem 2 (Claessen–Duregård–Pałka).**

> Consider space `s`, a non-negative size `k`, and a predicate `p`. Let the multiset `a = sized s k`
> and `b = {x | x ∈ a, p x}`. If `b` is non-empty, then `uniform p s k` is uniform over `b`.

Uniform over the occurrences of `b`, conditional on producing a value: the probability of `x` is its
share `count x a / m` of the satisfying occurrences, times the probability of producing anything at
all. This holds for every oracle and every fuel. The paper's proof also takes that probability to be
`1`, which needs `sizedP` to terminate, and its stated law does not ensure that
(`uniform_cycleOracle_spaceTriple`). -/
theorem Theorem2 [DecidableEq α] (O : LazyOracle) (fuel : Nat) (p : α → Bool) (s : Space α)
    (k : Nat) (hb : 0 < (satisfying p s k).card) (x : α) :
    (uniform O fuel p s k : SPMF (Option α)) (some x)
      = (if p x then ((allOfSize s k).count x : ℝ≥0∞) else 0) / ((satisfying p s k).card : ℝ≥0∞)
        * ∑' y, (uniform O fuel p s k : SPMF (Option α)) (some y) := by
  classical
  obtain ⟨κ, hκ⟩ := Theorem2_prop O fuel p s k
  have hm0 : ((satisfying p s k).card : ℝ≥0∞) ≠ 0 := by rw [Ne, Nat.cast_eq_zero]; omega
  have hmtop : ((satisfying p s k).card : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  -- The total is `m * κ`: the multiplicities of the satisfying values sum to `m`.
  have htot : ∑' y, (uniform O fuel p s k : SPMF (Option α)) (some y)
      = ((satisfying p s k).card : ℝ≥0∞) * κ := by
    rw [tsum_congr hκ, ← tsum_ite_count_eq_card_satisfying, ← ENNReal.tsum_mul_right]
    exact tsum_congr fun y => by rw [ite_mul, zero_mul]
  rw [htot, hκ, ← mul_assoc, ENNReal.div_mul_cancel hm0 hmtop, ite_mul, zero_mul]

/-! ## Section 4.1: a non-deterministic evaluation order breaks uniformity

"Even so, there is a more subtle problem with non-deterministic evaluation order – it may cause
biased distribution of the generated data." The paper's predicate `nonDetB` is constantly `True`,
but asks a racy `oracle :: IO Bool` which component to force first; the race makes the answer depend
on the drawn index. A `LazyOracle` is a fixed function, so the race is modelled by drawing the index
first and then choosing the oracle from it (`racyRound`). Since `nonDetB` accepts everything, one
round of `uniform` is the whole run.

The racy oracle cannot satisfy `LazyOracle.SwapLaw`: `nonDetB ∘ swap = nonDetB`, so the law forces
`inspectsFst nonDetB = false`. In Lean the example therefore lies outside the paper's law, which is
why the law is not a field of `LazyOracle`. -/

/-- The paper's `spaceBool = Pay (Pure False :+: Pure True)`. -/
def spaceBool : Space Bool := .pay (.pure false :+: .pure true)

/-- The paper's `spacePairB = Pay ((,) :$: spaceBool :*: spaceBool)`. Lean's `:*:` already builds
pairs, so the `(,) :$:` is not needed. -/
def spacePairB : Space (Bool × Bool) := .pay (spaceBool :*: spaceBool)

/-- The paper's `nonDetB`: its value is always `True`; only its evaluation order is
non-deterministic, and that lives in the oracle. -/
def nonDetB : Bool × Bool → Bool := fun _ => true

/-- An oracle that never prunes and always forces the first component first (`b = true`) or the
second first (`b = false`). -/
def orderOracle (b : Bool) : LazyOracle where
  universal _ := none
  inspectsFst _ := b
  universal_sound := by intro _ _ _ h; cases h

/-- The paper's race: "if the index is 1 then `oracle` returns `False`, otherwise it returns
`True`". -/
def race (i : Nat) : LazyOracle := orderOracle (i != 1)

section Racy

variable {G : Type → Type} [Gen G]

/-- One round of `uniform` in which the oracle may depend on the drawn index: draw `i`, run
`sizedP` with the oracle `O i`, and return the value at index `i`, if it is one. -/
def racyRound (O : Nat → LazyOracle) (fuel : Nat) (p : α → Bool) (s : Space α) (k : Nat) :
    G (Option α) := do
  let i ← chooseNat 0 ((Space.sized s k).card - 1)
  pure (((sizedP (O i) fuel p s k).bind (·.indexSet i)).bind Sum.getLeft?)

end Racy

/-- One round of `racyRound` at `spacePairB`, as the sum over the four indices. -/
theorem racyRound_spacePairB_apply (O : Nat → LazyOracle) (y : Option (Bool × Bool)) :
    (racyRound O 17 nonDetB spacePairB 3 : SPMF (Option (Bool × Bool))) y
      = (∑ i ∈ Finset.range 4, if y = ((sizedP (O i) 17 nonDetB spacePairB 3).bind
          (·.indexSet i)).bind Sum.getLeft? then 1 else 0) / 4 := by
  have hcard : (Space.sized spacePairB 3).card = 4 := by decide
  unfold racyRound
  rw [chooseNat_bind_apply (by omega : 0 < (Space.sized spacePairB 3).card), hcard]
  simp only [SPMF.pure_apply, Nat.cast_ofNat]
  exact congrArg (· / 4) (Finset.sum_congr rfl fun i _ => by congr)

/-- What the race returns at each index: the first-component-first order everywhere except at
index 1. -/
private theorem race_lookup :
    ((List.range 4).map fun i =>
        ((sizedP (race i) 17 nonDetB spacePairB 3).bind (·.indexSet i)).bind Sum.getLeft?)
      = [some (false, false), some (true, false), some (true, false), some (true, true)] := by
  decide

/-- **Section 4.1: the race makes `(True, False)` twice as likely as it should be…** It comes out
at indices 1 and 2. -/
theorem racyRound_race_TF :
    (racyRound race 17 nonDetB spacePairB 3 : SPMF (Option (Bool × Bool))) (some (true, false))
      = 1 / 2 := by
  rw [racyRound_spacePairB_apply]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  have h := race_lookup
  simp only [List.range_succ, List.range_zero, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append, List.cons.injEq] at h
  obtain ⟨h0, h1, h2, h3, -⟩ := h
  rw [h0, h1, h2, h3]
  norm_num
  rw [show (4 : ℝ≥0∞) = 2 * 2 by norm_num, ENNReal.div_eq_inv_mul, ENNReal.mul_inv (by simp) (by simp),
    mul_assoc, ENNReal.inv_mul_cancel (by simp) (by simp), mul_one]

/-- **…and `(False, True)` is never produced**, although it satisfies `nonDetB`. -/
theorem racyRound_race_FT :
    (racyRound race 17 nonDetB spacePairB 3 : SPMF (Option (Bool × Bool))) (some (false, true))
      = 0 := by
  rw [racyRound_spacePairB_apply]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  have h := race_lookup
  simp only [List.range_succ, List.range_zero, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append, List.cons.injEq] at h
  obtain ⟨h0, h1, h2, h3, -⟩ := h
  rw [h0, h1, h2, h3]
  norm_num

end UniformConstrained
