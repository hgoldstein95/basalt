/-
Copyright (c) 2026 Harrison Goldstein & Ernest Ng. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Ernest Ng
-/
import Basalt
import BasaltExperiments.UniformConstrained.Space

/-!
# Uniform sampling by size, and rejection sampling (Sections 2.3 and 3)

This file translates the paper's sampling procedures. The paper's `Random` monad — "a monad with the
only side-effect of generating random values" — is Basalt's `Gen`, so `uniformRange` is `chooseNat`
and the paper's `Random a` is `G α`.

## Main definitions

- `uniformSet` — the paper's `uniformSet :: Set a → Random a` (Section 2.3), uniform over the
  occurrences of a non-empty finite multiset. The paper's `error "empty set"` becomes a hypothesis
  `0 < s.card`, so the Lean version is total.
- `uniformSized` — the paper's `uniformSized s k = uniformSet (sized s k)`.
- `uniformFilter` — the paper's rejection sampler (Section 3). Since it may diverge, it is defined
  by `partial_fixpoint`, which is exactly what Basalt's `Gen` is set up for.

## Main results

- `uniformSet_apply` — `uniformSet s` assigns `a` the probability `count a s / |s|`: it is uniform
  over the *occurrences* in `s`, as the paper requires.
- `IsPMF_uniformSet` — `uniformSet` terminates (it makes exactly one choice).
- `uniformFilter_apply` — the recurrence the paper's Theorem 1 proof reasons about.
- `Theorem1` — **the paper's Theorem 1**: if `b = {x | x ∈ a, p x}` is non-empty, where
  `a = sized s k`, then `uniformFilter p s k` is uniform over `b`. Concretely, every `x` satisfying
  `p` is produced with probability `count x a / |b|`, so two values satisfying `p` with the same
  multiplicity in `a` are equally likely, and the total mass is 1.
-/

open Lean.Order RandomChoice ENNReal

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

/-! ### `uniformSet` is uniform over occurrences -/

namespace SPMF

/-- Every index `chooseNat 0 (n-1)` can draw is equiprobable, with probability `1/n`. -/
theorem chooseNat_apply_of_mem {n : Nat} (hn : 0 < n) {i : Nat} (hi : i < n) :
    (chooseNat 0 (n - 1) (Nat.zero_le _) : SPMF Nat) i = 1 / (n : ℝ≥0∞) := by
  unfold chooseNat
  rw [map_eq_pure_bind, SPMF.bind_apply]
  rw [tsum_eq_single (⟨⟨i, ⟨Nat.zero_le i, by omega⟩⟩⟩ :
    ULift {x : Nat // 0 ≤ x ∧ x ≤ n - 1})]
  · rw [SPMF.choose_apply, SPMF.pure_apply, if_pos rfl, mul_one]
    congr 2
    omega
  · intro m hm
    have hne : ¬ (i = m.down.val) := fun h => hm (by
      cases m with
      | up v => cases v with | mk v hv => cases h; rfl)
    rw [SPMF.pure_apply, if_neg hne, mul_zero]

end SPMF

/-- **`uniformSet s` is uniform over the occurrences in `s`.** The probability of drawing `a` is its
multiplicity in `s` divided by `|s|`. This is the statement the paper opens Section 4 with ("it is
easy to prove that `uniformSet s` is uniform over the occurrences in `s`, by proving that `indexSet`
is bijective and that `uniformRange` is uniform"): `FinSet.countP_indexSet_eq_count` supplies the
first half and `SPMF.chooseNat_apply_of_mem` the second. -/
theorem uniformSet_apply [DecidableEq α] (s : FinSet α) (hne : 0 < s.card) (a : α) :
    (uniformSet s hne : SPMF α) a = (s.toMultiset.count a : ℝ≥0∞) / (s.card : ℝ≥0∞) := by
  classical
  unfold uniformSet
  rw [SPMF.bind_apply]
  -- Only the indices naming `a` contribute, and each contributes `1 / |s|`.
  have hterm : ∀ i : Nat,
      (chooseNat 0 (s.card - 1) (Nat.zero_le _) : SPMF Nat) i *
        (Pure.pure ((s.indexSet i).getD (s.index 0 hne)) : SPMF α) a
      = if i ∈ (List.range s.card).filter (fun i => s.indexSet i == some a)
        then 1 / (s.card : ℝ≥0∞) else 0 := by
    intro i
    by_cases hi : i < s.card
    · rw [SPMF.chooseNat_apply_of_mem hne hi, s.indexSet_index i hi]
      by_cases hxa : a = s.index i hi
      · rw [Option.getD_some, SPMF.pure_apply, if_pos hxa, mul_one, if_pos
          (by simp only [List.mem_filter, List.mem_range, beq_iff_eq]
              exact ⟨hi, by rw [s.indexSet_index i hi, hxa]⟩)]
      · rw [Option.getD_some, SPMF.pure_apply, if_neg hxa, mul_zero, if_neg]
        simp only [List.mem_filter, List.mem_range, beq_iff_eq, not_and]
        intro _ h
        exact hxa (Option.some_injective _ ((s.indexSet_index i hi).symm.trans h)).symm
    · have hzero : (chooseNat 0 (s.card - 1) (Nat.zero_le _) : SPMF Nat) i = 0 := by
        rw [SPMF.apply_eq_zero_iff, SPMF.mem_support_chooseNat_iff]
        omega
      rw [hzero, zero_mul, if_neg]
      simp only [List.mem_filter, List.mem_range, not_and]
      omega
  rw [tsum_congr hterm]
  -- Only the indices naming `a` contribute; each contributes `1 / |s|`.
  rw [tsum_eq_sum (s := ((List.range s.card).filter (fun i => s.indexSet i == some a)).toFinset)
    (by intro i hi; rw [if_neg]; simpa using hi)]
  rw [Finset.sum_congr rfl (fun i hi => if_pos (by simpa using hi))]
  rw [Finset.sum_const, nsmul_eq_mul, one_div, mul_comm, ← ENNReal.div_eq_inv_mul]
  -- The number of contributing indices is the multiplicity of `a`.
  congr 1
  rw [List.toFinset_card_of_nodup (List.Nodup.filter _ (List.nodup_range)),
    ← List.countP_eq_length_filter]
  exact congrArg Nat.cast (s.countP_indexSet_eq_count a)

/-- `uniformSet` makes exactly one random choice, so it terminates. -/
theorem IsPMF_uniformSet [Inhabited α] (s : FinSet α) (hne : 0 < s.card) :
    SPMF.IsPMF (uniformSet s hne : SPMF α) := by
  unfold uniformSet
  rw [SPMF.IsPMF]
  rw [SPMF.mass_bind_tsum]
  simp only [SPMF.mass_pure, mul_one]
  exact SPMF.mass_chooseNat 0 (s.card - 1) (Nat.zero_le _)

/-! ## Rejection sampling (Section 3) -/

/-- The paper's `uniformFilter :: (a → Bool) → Space a → Int → Random a` (Section 3):

```haskell
uniformFilter p s k = do
  a ← uniformSized s k
  if p a then return a else uniformFilter p s k
```

This may diverge (the paper: "if there are no values that satisfy the predicate it will never
terminate"), so it is a `partial_fixpoint` — the reason Basalt's generators live in a CCPO. -/
def uniformFilter [Gen G] (p : α → Bool) (s : Space α) (k : Nat)
    (hne : 0 < (Space.sized s k).card) : G α := do
  let a ← uniformSized s k hne
  if p a then pure a else uniformFilter p s k hne
partial_fixpoint

theorem uniformFilter_eq [Gen G] (p : α → Bool) (s : Space α) (k : Nat)
    (hne : 0 < (Space.sized s k).card) :
    (uniformFilter p s k hne : G α)
      = (do let a ← uniformSized s k hne
            if p a then pure a else uniformFilter p s k hne) := by
  conv_lhs => rw [uniformFilter]

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
private theorem tsum_div_const (f : α → ℝ≥0∞) (c : ℝ≥0∞) :
    ∑' x, f x / c = (∑' x, f x) / c := by
  simp only [ENNReal.div_eq_inv_mul]
  exact ENNReal.tsum_mul_left

/-- The total mass of a multiset's multiplicity function is its cardinality. -/
private theorem tsum_count [DecidableEq α] (M : Multiset α) :
    ∑' x, (M.count x : ℝ≥0∞) = (M.card : ℝ≥0∞) := by
  classical
  rw [tsum_eq_sum (s := M.toFinset)
    (by intro x hx
        simp [Multiset.count_eq_zero_of_notMem (by simpa using hx)])]
  rw [← Nat.cast_sum]
  exact congrArg Nat.cast (Multiset.toFinset_sum_count_eq M)

/-- **The acceptance probability is `m / n`.** One draw of `uniformSized s k` satisfies `p` with
probability `|b| / |a|`, since `p`-satisfying occurrences are exactly `b`. -/
theorem massAccept [DecidableEq α] (p : α → Bool) (s : Space α) (k : Nat)
    (hne : 0 < (Space.sized s k).card) :
    (∑' x, if p x then (uniformSized s k hne : SPMF α) x else 0)
      = ((satisfying p s k).card : ℝ≥0∞) / ((allOfSize s k).card : ℝ≥0∞) := by
  classical
  have hcard : (Space.sized s k).card = (allOfSize s k).card := by
    rw [FinSet.card_eq_length_toList]; rfl
  have hterm : ∀ x, (if p x then (uniformSized s k hne : SPMF α) x else 0)
      = ((satisfying p s k).count x : ℝ≥0∞) / ((Space.sized s k).card : ℝ≥0∞) := by
    intro x
    rw [uniformSized, uniformSet_apply _ hne x, satisfying, Multiset.count_filter]
    by_cases h : p x = true <;> simp [h]
  rw [tsum_congr hterm, tsum_div_const, tsum_count, hcard]

/-- The rejection probability is `(n - m) / n`, the paper's `y ∉ b` case. -/
theorem massReject [DecidableEq α] (p : α → Bool) (s : Space α) (k : Nat)
    (hne : 0 < (Space.sized s k).card) :
    (∑' x, if p x then 0 else (uniformSized s k hne : SPMF α) x)
      = 1 - ((satisfying p s k).card : ℝ≥0∞) / ((allOfSize s k).card : ℝ≥0∞) := by
  classical
  have hmass : (uniformSized s k hne : SPMF α).mass = 1 := by
    have : Inhabited α := ⟨(Space.sized s k).index 0 hne⟩
    exact IsPMF_uniformSet _ hne
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
  have hcard : (Space.sized s k).card = (allOfSize s k).card := by
    rw [FinSet.card_eq_length_toList]; rfl
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
  · rw [if_pos hx, tsum_eq_single x, if_pos hx, SPMF.pure_apply, if_pos rfl, mul_one,
      uniformSized, uniformSet_apply _ hne x, hcard]
    intro y hy
    by_cases hy' : p y
    · rw [if_pos hy', SPMF.pure_apply, if_neg (fun h => hy h.symm), mul_zero]
    · rw [if_neg hy']
  · rw [if_neg hx, ENNReal.zero_div, ENNReal.tsum_eq_zero]
    intro y
    by_cases hy' : p y
    · rw [if_pos hy', SPMF.pure_apply, if_neg (fun h : x = y => hx (by rw [h]; exact hy')),
        mul_zero]
    · rw [if_neg hy']

/-- **Theorem 1 (Claessen–Duregård–Pałka).**

> Consider space `s`, a non-negative size `k`, and a predicate `p`. Let the multiset `a = sized s k`
> and `b = {x | x ∈ a, p x}`. If `b` is non-empty, then `uniformFilter p s k` is uniform over `b`.

"Uniform over `b`" is, as everywhere in the paper, uniform over the *occurrences* of `b`: each
occurrence gets probability `1/m`, so a value `x` with multiplicity `count x a` in `a` (equivalently,
in `b`, since `p x`) is produced with probability `count x a / m`. That is the statement proved here.
Two immediate consequences are recorded below: `uniformFilter` never produces a value failing `p`
(`Theorem1_sound`), and it terminates almost surely (`Theorem1_IsPMF`). -/
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

/-- **`uniformFilter` is sound**: it never produces a value that fails the predicate. Immediate from
`Theorem1` — the numerator is `0` when `¬ p x`. -/
theorem Theorem1_sound [DecidableEq α] (p : α → Bool) (s : Space α) (k : Nat)
    (hne : 0 < (Space.sized s k).card) (hb : 0 < (satisfying p s k).card) {x : α}
    (hx : x ∈ SPMF.support (uniformFilter p s k hne : SPMF α)) : p x := by
  by_contra h
  rw [SPMF.mem_support_iff, Theorem1 p s k hne hb x, if_neg h, ENNReal.zero_div] at hx
  exact hx rfl

/-- **`uniformFilter` terminates almost surely** when `b` is non-empty: the total mass is `1`, so no
mass is lost to the rejection loop running forever. This is the other half of what "uniform over `b`"
asserts — `Theorem1` gives the relative probabilities, this gives that they sum to one. -/
theorem Theorem1_IsPMF [DecidableEq α] (p : α → Bool) (s : Space α) (k : Nat)
    (hne : 0 < (Space.sized s k).card) (hb : 0 < (satisfying p s k).card) :
    SPMF.IsPMF (uniformFilter p s k hne : SPMF α) := by
  classical
  have hm0 : ((satisfying p s k).card : ℝ≥0∞) ≠ 0 := by
    rw [Ne, Nat.cast_eq_zero]; omega
  rw [SPMF.IsPMF, SPMF.mass, tsum_congr (Theorem1 p s k hne hb), tsum_div_const]
  -- The numerators are the multiplicities of `b`, which sum to `m`.
  rw [show (∑' x, if p x then ((allOfSize s k).count x : ℝ≥0∞) else 0)
      = ((satisfying p s k).card : ℝ≥0∞) from by
    rw [← tsum_count (satisfying p s k)]
    exact tsum_congr (fun x => by
      rw [satisfying, Multiset.count_filter]
      by_cases h : p x = true <;> simp [h])]
  exact ENNReal.div_self hm0 (ENNReal.natCast_ne_top _)

end UniformConstrained
