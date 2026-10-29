/-
Copyright (c) 2026 Harrison Goldstein & Ernest Ng. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Ernest Ng
-/
module

public import Basalt.Combinators
public import Basalt.Laws
import Basalt.Tactic.MassFixpoint
public import BasaltExamples.UniformConstrained.Space

/-!
# Uniform sampling by size, and rejection sampling (Sections 2.3, 3 and Theorem 1)

The paper's `Random` monad is Basalt's `Gen`, so its `uniformRange` is `chooseNat`. `uniformSet`
draws uniformly over the occurrences of a multiset, and the rejection sampler `uniformFilter` is
`suchThat` over it; Theorem 1 says the latter is uniform over the satisfying occurrences.
-/

@[expose] public section

open Lean.Order RandomChoice ENNReal

universe u

namespace UniformConstrained

open scoped Space

/-! ## Uniform sampling from a finite multiset -/

/-- The paper's `uniformSet :: Set a → Random a` (Section 2.3): draw an index uniformly from
`{0 … |s| - 1}` and return the occurrence it names.

The paper writes `uniformSet s | |s| == 0 = error "empty set"`; we take non-emptiness as a
hypothesis instead, which keeps the function total. `indexSet` is total here because the drawn index
is in range (`FinSet.indexSet_isSome`), so no `Option` leaks into the result. -/
def uniformSet [Gen G] (s : FinSet α) (hne : 0 < s.card) : G α := do
  let i ← chooseNat 0 (s.card - 1) (Nat.zero_le _)
  -- `indexSet s i` is always `some` here since `i` is in range, so the fallback is unreachable;
  -- it exists only to keep the result type `α` rather than `Option α`.
  pure ((s.indexSet i).getD (s.index 0 hne))

/-- The paper's `uniformSized :: Space a → Int → Random a` (Section 2.3):
`uniformSized s k = uniformSet (sized s k)`. -/
def uniformSized [Gen G] (s : Space α) (k : Nat) (hne : 0 < (Space.sized s k).card) : G α :=
  uniformSet (Space.sized s k) hne

/-! ### Sums over a uniform index -/

/-- **Binding after a uniform index averages over the indices.** -/
theorem chooseNat_bind_apply {β : Type} {n : Nat} (hn : 0 < n) (F : Nat → SPMF β) (y : β) :
    ((chooseNat 0 (n - 1) (Nat.zero_le _) : SPMF Nat) >>= F) y
      = (∑ i ∈ Finset.range n, F i y) / (n : ℝ≥0∞) :=
  SPMF.expect_chooseNat_zero hn fun i => F i y

theorem sum_range_getElem?_map {β : Type u} (l : List β) (g : β → ℝ≥0∞) :
    ∑ i ∈ Finset.range l.length, ((l[i]?).map g).getD 0 = ((l : Multiset β).map g).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    rw [List.length_cons, Finset.sum_range_succ']
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.map_some, Option.getD_some]
    rw [ih]
    show _ = ((x ::ₘ (xs : Multiset β)).map g).sum
    rw [Multiset.map_cons, Multiset.sum_cons, add_comm]

/-- Summing over the indices of a `FinSet` is summing over its occurrences: `indexSet` is a
bijection onto them. -/
theorem sum_range_indexSet_map {β : Type u} (s : FinSet β) (g : β → ℝ≥0∞) :
    ∑ i ∈ Finset.range s.card, ((s.indexSet i).map g).getD 0 = (s.toMultiset.map g).sum := by
  simp only [FinSet.indexSet_eq_getElem?, FinSet.card_eq_length_toList]
  exact sum_range_getElem?_map s.toList g

theorem sum_map_indicator [DecidableEq α] (M : Multiset α) (x : α) :
    (M.map (fun a => if x = a then (1 : ℝ≥0∞) else 0)).sum = (M.count x : ℝ≥0∞) := by
  refine Multiset.induction_on M (by simp) fun a s ih => ?_
  rw [Multiset.map_cons, Multiset.sum_cons, ih, Multiset.count_cons]
  by_cases h : x = a
  · simp [h, add_comm]
  · simp [h]

/-! ### `uniformSet` is uniform over occurrences -/

/-- **`uniformSet s` is uniform over the occurrences in `s`.** The probability of drawing `a` is its
multiplicity in `s` divided by `|s|`. This is the statement the paper opens Section 4 with ("it is
easy to prove that `uniformSet s` is uniform over the occurrences in `s`, by proving that `indexSet`
is bijective and that `uniformRange` is uniform"): `sum_range_indexSet_map` is the first half and
`chooseNat_bind_apply` the second. -/
theorem uniformSet_apply [DecidableEq α] (s : FinSet α) (hne : 0 < s.card) (a : α) :
    (uniformSet s hne : SPMF α) a = (s.toMultiset.count a : ℝ≥0∞) / (s.card : ℝ≥0∞) := by
  have hterm : ∀ i ∈ Finset.range s.card,
      (Pure.pure ((s.indexSet i).getD (s.index 0 hne)) : SPMF α) a
        = ((s.indexSet i).map fun z => if a = z then (1 : ℝ≥0∞) else 0).getD 0 := by
    intro i hi
    rw [s.indexSet_index i (Finset.mem_range.mp hi), Option.getD_some, Option.map_some,
      Option.getD_some, SPMF.pure_apply]
    congr
  unfold uniformSet
  rw [chooseNat_bind_apply hne, Finset.sum_congr rfl hterm, sum_range_indexSet_map,
    sum_map_indicator]

/-- `uniformSet` makes exactly one random choice, so it terminates. -/
theorem isAlmostSurelyTerminating_uniformSet (s : FinSet α) (hne : 0 < s.card) :
    IsAlmostSurelyTerminating (uniformSet s hne : SPMF α) := by
  unfold uniformSet
  rw [IsAlmostSurelyTerminating, SPMF.mass_bind_tsum]
  simp only [SPMF.mass_pure, mul_one]
  exact SPMF.mass_chooseNat 0 (s.card - 1) (Nat.zero_le _)

/-! ## Rejection sampling (Section 3) -/

/-- The paper's `uniformFilter :: (a → Bool) → Space a → Int → Random a` (Section 3):

```haskell
uniformFilter p s k = do
  a ← uniformSized s k
  if p a then return a else uniformFilter p s k
```

That is Basalt's rejection sampler `suchThat`, over `uniformSized s k`. -/
def uniformFilter [Gen G] (p : α → Bool) (s : Space α) (k : Nat)
    (hne : 0 < (Space.sized s k).card) : G α :=
  suchThat (uniformSized s k hne) p

theorem uniformFilter_eq [Gen G] (p : α → Bool) (s : Space α) (k : Nat)
    (hne : 0 < (Space.sized s k).card) :
    (uniformFilter p s k hne : G α)
      = (do let a ← uniformSized s k hne
            if p a then pure a else uniformFilter p s k hne) := by
  unfold uniformFilter
  conv_lhs => rw [suchThat]

/-! ### Theorem 1: the rejection sampler is uniform

The paper's proof: let `a = sized s k`, `b = {x | x ∈ a, p x}`, `n = |a|`, `m = |b|`. Each iteration
draws `y` uniformly from `a`. It rejects with probability `(n - m)/n` and hits a given occurrence `x`
with probability `1/n`, so `x` comes out on iteration `i` with probability
`(1/n)((n-m)/n)^(i-1)`, and summing the geometric series gives `1/m`.

Here `uniformFilter` is a `partial_fixpoint`, so instead of summing the series by hand we derive the
one-step recurrence `P(x) = 1/n + ((n-m)/n) · P(x)` from `uniformFilter_eq` and solve it — the same
argument, with the limit handled by the fixpoint equation.
-/

/-- The multiset `a = sized s k` of all values of size `k`: the paper's `a` in Theorem 1. -/
abbrev allOfSize (s : Space α) (k : Nat) : Multiset α := (Space.sized s k).toMultiset

/-- The paper's `b = {x | x ∈ a, p x}`: the occurrences of size `k` that satisfy the predicate. -/
def satisfying (p : α → Bool) (s : Space α) (k : Nat) : Multiset α :=
  (allOfSize s k).filter (fun x => p x = true)

/-- Pulling a constant divisor out of a `tsum`. -/
theorem tsum_div_const (f : α → ℝ≥0∞) (c : ℝ≥0∞) :
    ∑' x, f x / c = (∑' x, f x) / c := by
  simp only [ENNReal.div_eq_inv_mul]
  exact ENNReal.tsum_mul_left

/-- The total mass of a multiset's multiplicity function is its cardinality. -/
theorem tsum_count [DecidableEq α] (M : Multiset α) :
    ∑' x, (M.count x : ℝ≥0∞) = (M.card : ℝ≥0∞) := by
  classical
  rw [tsum_eq_sum (s := M.toFinset)
    (by intro x hx
        simp [Multiset.count_eq_zero_of_notMem (by simpa using hx)])]
  rw [← Nat.cast_sum]
  exact congrArg Nat.cast (Multiset.toFinset_sum_count_eq M)

/-- The multiplicities of the satisfying values sum to `|b|`. -/
theorem tsum_ite_count_eq_card_satisfying [DecidableEq α] (p : α → Bool) (s : Space α) (k : Nat) :
    (∑' x, if p x then ((allOfSize s k).count x : ℝ≥0∞) else 0)
      = ((satisfying p s k).card : ℝ≥0∞) := by
  rw [← tsum_count (satisfying p s k)]
  exact tsum_congr fun x => by
    rw [satisfying, Multiset.count_filter]
    by_cases h : p x = true <;> simp [h]

/-- **The acceptance probability is `m / n`.** One draw of `uniformSized s k` satisfies `p` with
probability `|b| / |a|`, since `p`-satisfying occurrences are exactly `b`. -/
theorem massAccept [DecidableEq α] (p : α → Bool) (s : Space α) (k : Nat)
    (hne : 0 < (Space.sized s k).card) :
    (∑' x, if p x then (uniformSized s k hne : SPMF α) x else 0)
      = ((satisfying p s k).card : ℝ≥0∞) / ((allOfSize s k).card : ℝ≥0∞) := by
  classical
  have hterm : ∀ x, (if p x then (uniformSized s k hne : SPMF α) x else 0)
      = ((satisfying p s k).count x : ℝ≥0∞) / ((Space.sized s k).card : ℝ≥0∞) := by
    intro x
    rw [uniformSized, uniformSet_apply _ hne x, satisfying, Multiset.count_filter]
    by_cases h : p x = true <;> simp [h]
  rw [tsum_congr hterm, tsum_div_const, tsum_count, ← FinSet.card_toMultiset]

/-- The rejection probability is `(n - m) / n`, the paper's `y ∉ b` case. -/
theorem massReject [DecidableEq α] (p : α → Bool) (s : Space α) (k : Nat)
    (hne : 0 < (Space.sized s k).card) :
    (∑' x, if p x then 0 else (uniformSized s k hne : SPMF α) x)
      = 1 - ((satisfying p s k).card : ℝ≥0∞) / ((allOfSize s k).card : ℝ≥0∞) := by
  classical
  have hmass : (uniformSized s k hne : SPMF α).mass = 1 :=
    isAlmostSurelyTerminating_uniformSet _ hne
  have hsplit : (∑' x, if p x then (uniformSized s k hne : SPMF α) x else 0)
      + (∑' x, if p x then 0 else (uniformSized s k hne : SPMF α) x)
      = (uniformSized s k hne : SPMF α).mass := by
    rw [SPMF.mass, ← ENNReal.tsum_add]
    exact tsum_congr (fun x => by by_cases h : p x <;> simp [h])
  rw [hmass, massAccept] at hsplit
  rw [← hsplit, ENNReal.add_sub_cancel_left
    (ne_top_of_le_ne_top one_ne_top (le_of_add_le_left hsplit.le))]

/-- **The one-step recurrence of the rejection sampler.** Unfolding `uniformFilter` once: `x` comes
out either on this draw (probability `count x a / n` when `p x`, else 0) or after a rejection
(probability `(n - m)/n`) followed by a fresh, independent run of the same loop. This is the paper's
"probability of `x` being drawn during the `i`th iteration is `(1/n)((n-m)/n)^(i-1)`", packaged as a
fixpoint equation instead of an infinite series. -/
theorem uniformFilter_apply [DecidableEq α] (p : α → Bool) (s : Space α) (k : Nat)
    (hne : 0 < (Space.sized s k).card) (x : α) :
    (uniformFilter p s k hne : SPMF α) x
      = (if p x then ((allOfSize s k).count x : ℝ≥0∞) else 0) / ((allOfSize s k).card : ℝ≥0∞)
        + (1 - ((satisfying p s k).card : ℝ≥0∞) / ((allOfSize s k).card : ℝ≥0∞))
          * (uniformFilter p s k hne : SPMF α) x := by
  classical
  conv_lhs => rw [uniformFilter_eq]
  rw [SPMF.bind_apply]
  -- Split each summand into its accepting and rejecting parts.
  have hterm : ∀ y, (uniformSized s k hne : SPMF α) y *
      (if p y then (Pure.pure y : SPMF α) else (uniformFilter p s k hne : SPMF α)) x
      = (if p y then (uniformSized s k hne : SPMF α) y * (Pure.pure y : SPMF α) x else 0)
        + (if p y then 0 else (uniformSized s k hne : SPMF α) y)
          * (uniformFilter p s k hne : SPMF α) x := by
    intro y
    by_cases h : p y <;> simp [h]
  rw [tsum_congr hterm, ENNReal.tsum_add, ENNReal.tsum_mul_right, massReject]
  congr 1
  -- The accepting part contributes only at `y = x`.
  by_cases hx : p x
  · rw [ite_eq_left hx, tsum_eq_single x, ite_eq_left hx, SPMF.pure_apply, ite_eq_left rfl, mul_one,
      uniformSized, uniformSet_apply _ hne x, ← FinSet.card_toMultiset]
    intro y hy
    by_cases hy' : p y
    · rw [ite_eq_left hy', SPMF.pure_apply, ite_eq_right (fun h => hy h.symm), mul_zero]
    · rw [ite_eq_right hy']
  · rw [ite_eq_right hx, ENNReal.zero_div, ENNReal.tsum_eq_zero]
    intro y
    by_cases hy' : p y
    · rw [ite_eq_left hy', SPMF.pure_apply, ite_eq_right (fun h : x = y => hx (by rw [h]; exact hy')),
        mul_zero]
    · rw [ite_eq_right hy']

/-- **Theorem 1 (Claessen–Duregård–Pałka).**

> Consider space `s`, a non-negative size `k`, and a predicate `p`. Let the multiset `a = sized s k`
> and `b = {x | x ∈ a, p x}`. If `b` is non-empty, then `uniformFilter p s k` is uniform over `b`.

"Uniform over `b`" is, as everywhere in the paper, uniform over the *occurrences* of `b`: each
occurrence gets probability `1/m`, so a value `x` with multiplicity `count x a` in `a` (equivalently,
in `b`, since `p x`) is produced with probability `count x a / m`. That is the statement proved here.
Since `uniformFilter` is `suchThat`, this is exact conditioning of `suchThat` at a uniform draw.
That it never produces a value failing `p`, and that it terminates almost surely, follow from
`suchThat`'s own lemmas (`Theorem1_sound`, `Theorem1_terminates`). -/
theorem Theorem1 [DecidableEq α] (p : α → Bool) (s : Space α) (k : Nat)
    (hne : 0 < (Space.sized s k).card) (hb : 0 < (satisfying p s k).card) (x : α) :
    (uniformFilter p s k hne : SPMF α) x
      = (if p x then ((allOfSize s k).count x : ℝ≥0∞) else 0)
        / ((satisfying p s k).card : ℝ≥0∞) := by
  classical
  -- Solve `R = c + (1 - m/n) * R` for `R`, where `m/n ≠ 0` (this is where `b ≠ ∅` is used).
  set R := (uniformFilter p s k hne : SPMF α) x with hR
  set n := ((allOfSize s k).card : ℝ≥0∞) with hn
  set m := ((satisfying p s k).card : ℝ≥0∞) with hm
  set w := (if p x then ((allOfSize s k).count x : ℝ≥0∞) else 0) with hw
  have hn0 : n ≠ 0 := by
    rw [hn, Ne, Nat.cast_eq_zero]
    have : (satisfying p s k).card ≤ (allOfSize s k).card :=
      Multiset.card_le_card (Multiset.filter_le _ _)
    omega
  have hntop : n ≠ ⊤ := ENNReal.natCast_ne_top _
  have hm0 : m ≠ 0 := by rw [hm, Ne, Nat.cast_eq_zero]; omega
  have hmtop : m ≠ ⊤ := ENNReal.natCast_ne_top _
  have hmn : m / n ≤ 1 := by
    rw [ENNReal.div_le_iff_le_mul (Or.inl hn0) (Or.inl hntop), one_mul, hm, hn, Nat.cast_le]
    exact Multiset.card_le_card (Multiset.filter_le _ _)
  have hrec : R = w / n + (1 - m / n) * R := uniformFilter_apply p s k hne x
  -- Rearrange to `R * (m/n) = w/n`, then cancel `n` to get `R * m = w`, i.e. `R = w/m`.
  have hRtop : R ≠ ⊤ := SPMF.apply_ne_top _ x
  have hkey : R * (m / n) = w / n := by
    have h1 : R * (1 - m / n) + R * (m / n) = R * (1 - m / n) + w / n := by
      rw [← mul_add, tsub_add_cancel_of_le hmn, mul_one]
      conv_lhs => rw [hrec]
      rw [mul_comm, add_comm]
    exact (ENNReal.add_right_inj (ENNReal.mul_ne_top hRtop (by finiteness))).mp h1
  have hRm : R * m = w := by
    rw [← mul_div_assoc] at hkey
    have := congrArg (fun x => x * n) hkey
    simpa [ENNReal.div_mul_cancel hn0 hntop] using this
  rw [ENNReal.eq_div_iff hm0 hmtop, mul_comm]
  exact hRm

/-- **`uniformFilter` is sound**: it never produces a value that fails the predicate, whether or not
`b` is empty. -/
theorem Theorem1_sound {p : α → Bool} {s : Space α} {k : Nat} {hne : 0 < (Space.sized s k).card}
    {x : α} (hx : x ∈ SPMF.support (uniformFilter p s k hne : SPMF α)) : p x :=
  (SPMF.mem_support_suchThat_iff.mp hx).2

/-- **`uniformFilter` terminates almost surely** when `b` is non-empty: a draw is rejected with
probability `1 - m/n < 1`. -/
theorem Theorem1_terminates [DecidableEq α] (p : α → Bool) (s : Space α) (k : Nat)
    (hne : 0 < (Space.sized s k).card) (hb : 0 < (satisfying p s k).card) :
    IsAlmostSurelyTerminating (uniformFilter p s k hne : SPMF α) := by
  have hm0 : ((satisfying p s k).card : ℝ≥0∞) ≠ 0 := by rw [Ne, Nat.cast_eq_zero]; omega
  refine SPMF.isAlmostSurelyTerminating_suchThat (r := 1 - ((satisfying p s k).card : ℝ≥0∞)
    / ((allOfSize s k).card : ℝ≥0∞)) (isAlmostSurelyTerminating_uniformSet _ hne) ?_
    (ENNReal.sub_lt_self one_ne_top one_ne_zero
      (ENNReal.div_pos_iff.mpr ⟨hm0, ENNReal.natCast_ne_top _⟩).ne')
  show SPMF.expect _ _ ≤ _
  rw [SPMF.expect, ← massReject p s k hne]
  exact le_of_eq (tsum_congr fun x => by by_cases h : p x <;> simp [h])

end UniformConstrained
