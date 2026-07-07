/-
Copyright (c) 2026 Harrison Goldstein & Ernest Ng. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein & Ernest Ng
-/

import Basalt.Gen
import Basalt.IO
import Basalt.RandomChoice

open Lean.Order

/-!
# Generator Combinators

This file defines various generator combinators:
- `elements`: generates an element from a non-empty list at random
- `oneOf`: picks from a list of generators uniformly at random selection
- `frequency`: like `oneOf`, but performs weighted random selection
- `frequencySelect`: helper function that traverses the list of weights
   to select a generator for a given random index
-/

open List

namespace Helpers

/-- Helper function for the `frequency` combinator:
    `frequencySelect xs n` chooses a weight & a generator `(k, gen)` from the list `xs` such that `n < k`.
     This function expects a proof `h : n < sum(xs)`, which makes the empty-list case in
     the pattern-match irrefutable, since `n < 0` is `False` (this is discharged
     immediately by `contradiction`). -/
def frequencySelect [Gen G] (xs : List (Nat × (Unit → G α))) (n : Nat)
    (h : n < List.sum (List.map Prod.fst xs)) : G α :=
  match xs with
  | [] => by contradiction
  | (k, x) :: xs =>
    if hlt : n < k then
      x ()
    else
      frequencySelect xs (n - k) (by dsimp at h; omega)

/-- Implementation of the `oneOf` combinator, parameterized by an upper bound `n`
    for the random index. The caller is required to supply a proof that `n`
    is strictly less than the list's length.
    (`oneOf` instantiates `n` with `gs.length - 1`).
    Making the upper bound a parameter allows us to use the `oneOfAux_congr` lemma below
    to propogate equalities about the bound via `subst`, which
    is used in the monotonicity proof for `oneOf` (`oneOf_le`). -/
def oneOfAux [Gen G] (l : List (Unit → G α)) (n : Nat)
    (hlt : ∀ i, i ≤ n → i < l.length) : G α := do
  let ⟨i, _, hle_i⟩ ← ULift.down <$> RandomChoice.choose 0 n (Nat.zero_le n)
  (l[i]'(hlt i hle_i)) ()

/-- Implementation of the `frequency` combinator, parameterized by the total
    weight `total`, which serves as the (exclusive) upper bound for the random
    index. The caller supplies a proof `htotal` that `total` really is the sum of
    the weights in `gs`. (`frequency` instantiates `total` with
    `List.sum (List.map Prod.fst gs)`.)

    This helper plays the same role for `frequency` that `oneOfAux` plays for
    `oneOf`: it is the `do`-block wrapping the random `RandomChoice.choose`, and
    it delegates the actual generator selection to `frequencySelect` (just as
    `oneOfAux` delegates to the list indexing `l[i]`).

    Making the bound `total` a parameter lets us use the `frequencyAux_congr`
    lemma to propagate equalities about the total via `subst`, which is used in
    the monotonicity proof for `frequency` (`frequency_le`). -/
def frequencyAux [Gen G] (gs : List (Nat × (Unit → G α))) (total : Nat)
    (htotal : total = List.sum (List.map Prod.fst gs)) : G α := do
  let n ← ULift.down <$> RandomChoice.choose 0 (total - 1) (Nat.zero_le _)
  if hn : n < total then
    frequencySelect gs n (by omega)
  else
    default

end Helpers

/-- Generates an element of the list `xs` at random.
    This combinator takes as input a proof that `xs` is non-empty. -/
def elements [Gen G] (xs : List α) (hne : xs ≠ []) : G α := do
  let ⟨i, ⟨ hge, hle ⟩⟩ ← ULift.down <$> RandomChoice.choose 0 (xs.length - 1) (by omega)
  -- Obtain a proof that the list indexing is in-bounds
  have hlen : 0 < xs.length := by
    apply length_pos_iff.mpr
    assumption
  have hlt : i < xs.length := by omega
  return xs[i]'hlt

/-- Picks one of the generators in `gs` at random.
    This combinator takes as input a proof that `gs` is non-empty. -/
def oneOf [Gen G] (gs : List (Unit → G α)) (hne : gs ≠ []) : G α :=
  Helpers.oneOfAux gs (gs.length - 1) (by
    intro i hi
    have hlen : 0 < gs.length := length_pos_iff.mpr hne
    omega)

/-- `frequency` picks a generator from the list `gs` according to the weights in `gs`.
    This combinators also takes an additional hypothesis that the sum of the weights
    in the list is non-zero (this is discharged via `omega` by default). -/
def frequency [Gen G] (gs : List (Nat × (Unit → G α)))
  (_h : 0 < List.sum (List.map Prod.fst gs) := by omega) : G α :=
  Helpers.frequencyAux gs (List.sum (List.map Prod.fst gs)) rfl

/-- Define a partial order over `List α` that says `l1 ⊑ l2` when:
    - `l1.length = l2.length`
    - `l1[i] ⊑ l2[i]` for all list elements (here we are comparing them using the `PartialOrder` on `α`) -/
instance List.instPartialOrder {α : Type u} [PartialOrder α] :
    PartialOrder (List α) where
  rel l1 l2 :=
    l1.length = l2.length ∧
    ∀ (i : Nat) (h1 : i < l1.length) (h2 : i < l2.length), l1[i] ⊑ l2[i]
  -- Reflexivity
  rel_refl := by
    intro xs
    constructor
    . rfl
    . intro i _ _
      apply PartialOrder.rel_refl
  -- Transitivity
  rel_trans := by
    intro xs ys zs h12 h23
    obtain ⟨heq1, hle1⟩ := h12
    obtain ⟨heq2, hle2⟩ := h23
    constructor
    . apply Eq.trans <;> assumption
    . intro i h1 h2
      apply PartialOrder.rel_trans
      . apply hle1
        omega
      . apply hle2
  -- Antisymmetry
  rel_antisymm := by
    intro x y hxy hyx
    obtain ⟨hlen, helem_xy⟩ := hxy
    obtain ⟨_, helem_yx⟩ := hyx
    apply List.ext_getElem hlen
    intro i hx hy
    apply PartialOrder.rel_antisymm
    . apply helem_xy
    . apply helem_yx

/-- Partial order on `Nat × α` pairs:
      `(w₁, g₁) ⊑ (w₂, g₂) ≝ w₁ = w₂ ∧ g₁ ⊑ g₂`.
    The `nat` weight uses the *discrete* order (`=`) and the second element uses `α`'s order.
    Note that if we instead had w1 ≤ w2, `frequency` would no longer be monotone,
    since increasing the weight of one sub-generator passed to `frequency`
    would cause the weights of other sub-generators to decrease (as the two lists
    `l1, l2` are constrianed to have the same length). -/
instance {α : Type u} [PartialOrder α] : PartialOrder (Nat × α) where
  rel p q := p.1 = q.1 ∧ p.2 ⊑ q.2
  -- Reflexivity
  rel_refl := by
    intro p
    constructor
    . rfl
    . apply PartialOrder.rel_refl
  -- Transitivity
  rel_trans := by
    intro p q r hpq hqr
    obtain ⟨hw1, hg1⟩ := hpq
    obtain ⟨hw2, hg2⟩ := hqr
    constructor
    . apply hw1.trans; assumption
    . apply PartialOrder.rel_trans <;> assumption
  -- Antisymmetry
  rel_antisymm := by
    intro p q hpq hqp
    obtain ⟨hw, hg⟩ := hpq
    obtain ⟨_, hg'⟩ := hqp
    apply Prod.ext
    . assumption
    . apply PartialOrder.rel_antisymm <;> assumption

/- This lemma lets the `monotonicity` tactic (invoked by `partial_fixpoint` under the hood)
   decompose a list literal `[e₁, e₂, …]` into `e₁ :: (e₂ :: …)`
   when all the `eᵢ` are functions. -/
@[partial_fixpoint_monotone]
theorem List.monotone_cons
    {α : Type u} {γ : Sort w} [PartialOrder α] [PartialOrder γ]
    (f : γ → α) (fs : γ → List α) (hf : monotone f) (hfs : monotone fs) :
    monotone (fun x => f x :: fs x) := by
  intro x y hxy
  have hle : fs x ⊑ fs y := hfs x y hxy
  have heq : (fs x).length = (fs y).length := hle.1
  dsimp
  constructor
  . -- (f x :: fs x).length = (f y :: fs y).length
    simpa using heq
  . -- (f x :: fs x)[i] ⊑ (f y :: fs y)[i]
    intro i h1 h2
    cases i with
    | zero =>
      apply hf
      assumption
    | succ i' =>
      dsimp
      have all_elts_le := (hfs x y hxy).2
      apply all_elts_le

/-- If two terms `a, b` are propositionally equal (i.e. `a = b`),
    then `a ⊑ b`, i.e. `⊑` is reflexive up to propositional equality. -/
private theorem le_of_eq {β : Sort u} [PartialOrder β] {a b : β} (h : a = b) : a ⊑ b := by
  subst h
  exact PartialOrder.rel_refl

/-- `oneOfAux` is congruent in the upper bound `n` for the random index,
    i.e. if `n1 = n2`, then `oneOfAux l n1 = oneOfAux l n2`.
    Since `n` is a parameter to `oneOfAux`, we can `subst` the equality `n1 = n2`
    in the return type of `RandomChoice.choose`. -/
private theorem oneOfAux_congr [Gen G] (l : List (Unit → G α)) (n₁ n₂ : Nat)
    (hn : n₁ = n₂)
    (hlt₁ : ∀ i, i ≤ n₁ → i < l.length) (hlt₂ : ∀ i, i ≤ n₂ → i < l.length) :
    Helpers.oneOfAux l n₁ hlt₁ = Helpers.oneOfAux l n₂ hlt₂ := by
  subst hn
  rfl

/-- Like `oneOfAux` above, but for `frequencyAux` -/
private theorem frequencyAux_congr [Gen G] (l : List (Nat × (Unit → G α))) (n1 n2 : Nat)
    (hn : n1 = n2)
    (heq1 : n1 = List.sum (List.map Prod.fst l)) (heq2 : n2 = List.sum (List.map Prod.fst l)) :
    Helpers.frequencyAux l n1 heq1 = Helpers.frequencyAux l n2 heq2 := by
  subst hn
  rfl



/-- Monotonicity of `frequencySelect` traversal: if `l1 ⊑ l2` and the same random index `n` is
    in less than each list's sum of weights (`h1, h2`),
    then `frequencySelect l1 n h1 ⊑ frequencySelect l2 n h2 -/
private theorem frequencySelect_le [Gen G] {l1 l2 : List (Nat × (Unit → G α))} {n : Nat}
    (hle : l1 ⊑ l2)
    (h1 : n < List.sum (List.map Prod.fst l1))
    (h2 : n < List.sum (List.map Prod.fst l2)) :
    Helpers.frequencySelect l1 n h1 ⊑ Helpers.frequencySelect l2 n h2 := by
  induction l1 generalizing n l2 with
  | nil => contradiction
  | cons hd xs IH =>
    obtain ⟨k, g⟩ := hd
    obtain ⟨hlen_eq, hrel⟩ := hle
    cases l2 with
    | nil => contradiction
    | cons hd' ys =>
      obtain ⟨k', g'⟩ := hd'
      -- Instantiate `hrel` with 0 to reason about the head of the two lists
      have hzero := hrel 0 (by simp) (by simp)
      obtain ⟨hweight, helt⟩ := hzero
      -- This simplifies `hweight` and `helt` to `k = k'`, `g ⊑ g'`
      simp [List.getElem_cons_zero] at hweight helt
      subst hweight
      -- Case analysis on how the `if`-expression in `frequencySelect` evaluate
      unfold Helpers.frequencySelect
      split
      . -- n < k
        apply helt
      . -- ¬ (n < k)
        have htail : xs ⊑ ys := by
          constructor
          . injection hlen_eq
          . intro i hi1 hi2
            -- Note that `((k, g) :: xs)[i + 1] = xs[i]`, so
            -- we can just instantiate `hrel` (the ⊑ relation on lists)
            -- with `i + 1` and directly apply `hrel`
            specialize hrel (i + 1)
            dsimp at hrel
            apply hrel <;> omega
        apply IH
        assumption

/-- If two lists `l1, l2 : List (Nat × α)` satisfy `l1 ⊑ l2`, then the sum of their weights
    must be equal -/
private theorem sumOfWeights_le {α : Type u} [PartialOrder α] {l1 l2 : List (Nat × α)}
      (hle : l1 ⊑ l2) :
      List.sum (List.map Prod.fst l1) = List.sum (List.map Prod.fst l2) := by
  obtain ⟨hlen, hrel⟩ := hle
  congr 1
  -- Need to show `map Prod.fst l1 = map Prod.fst l2`
  apply List.ext_getElem
  . repeat rw [List.length_map]
    assumption
  . intro i h1 h2
    rw [List.length_map] at h1 h2
    specialize hrel i h1 h2
    obtain ⟨hlen, hle⟩ := hrel
    simp only [getElem_map]
    assumption

/-- Monotonicity of `oneOf`: if lists `l1, l2` are both non-empty (`h1, h2`) and `l1 ⊑ l2`,
    then `oneOf l1 h1 ⊑ oneOf l2 h2` -/
theorem oneOf_le [Gen G] {l1 l2 : List (Unit → G α)} (h : l1 ⊑ l2) (h1 : l1 ≠ []) (h2 : l2 ≠ []) :
    oneOf l1 h1 ⊑ oneOf l2 h2 := by
  obtain ⟨hlen_eq, hle⟩ := h
  have h1len : 0 < l1.length := List.length_pos_iff.mpr h1
  have h2len : 0 < l2.length := List.length_pos_iff.mpr h2
  -- Use transitivity of ⊑
  apply PartialOrder.rel_trans
    (y := Helpers.oneOfAux l2 (l1.length - 1) (by omega))
  . -- oneOf l1 h1 ⊑ oneOfAux l2 (l1.length - 1)
    simp only [oneOf, Helpers.oneOfAux]
    -- Both sides of the ⊑ bind the result of `RandomChoice.choose`, so we
    -- only need to reason about the rest of the `do` block
    apply MonoBind.bind_mono_right
    intro ⟨i, hge, hle_i⟩
    apply hle
  . -- oneOfAux l2 (l1.length - 1) ⊑ oneOf l2 h2
    simp only [oneOf]
    -- Turn ⊑ in the goal into an ordinary equality =,
    -- then use the fact that oneOfAux is congruent in the choice of
    -- upper bound for the random index
    apply le_of_eq
    apply oneOfAux_congr <;> omega

/-- Single general `@[partial_fixpoint_monotone]` lemma.
    The `monotonicity` tactic (invoked by `partial_fixpoint` under the hood)
    sees `fun x => oneOf (gens x)` and uses this lemma,
    having already established `monotone gens` via `List.monotone_cons`. -/
@[partial_fixpoint_monotone]
theorem monotone_oneOf [Gen G] {γ : Sort w} [PartialOrder γ]
    (gs : γ → List (Unit → G α)) (hne : ∀ x, gs x ≠ []) (hmono : monotone gs) :
    monotone (fun x => oneOf (gs x) (hne x)) := by
  intro x y hxy
  unfold monotone at hmono
  apply oneOf_le
  apply hmono
  assumption

/-- Lets the `monotonicity` tactic build a monotone weighted entry `(w, g x)`
    for a `frequency` list: the weight `w` is a constant and the generator `g`
    is monotone. Mirrors `List.monotone_cons`, but for the pair that sits at
    each position of a `frequency` list literal `[(w₁, g₁), …]`. -/
@[partial_fixpoint_monotone]
theorem monotone_pair_snd {α : Type u} {γ : Sort w} [PartialOrder α] [PartialOrder γ]
    (w : Nat) (g : γ → α) (hg : monotone g) :
    monotone (fun x => (w, g x)) := by
  intro x y hxy
  exact ⟨rfl, hg x y hxy⟩

/-- Monotonicity of `frequency`: if `l1 ⊑ l2` (equal weights, pointwise-related
      generators) and both have positive total weight (`h1, h2`), then
      `frequency l1 h1 ⊑ frequency l2 h2`. -/
theorem frequency_le [Gen G] {l1 l2 : List (Nat × (Unit → G α))} (h : l1 ⊑ l2)
    (h1 : 0 < List.sum (List.map Prod.fst l1))
    (h2 : 0 < List.sum (List.map Prod.fst l2)) :
    frequency l1 h1 ⊑ frequency l2 h2 := by
  apply PartialOrder.rel_trans
    (y := Helpers.frequencyAux l2 (List.sum (List.map Prod.fst l1)) (sumOfWeights_le h))
  . -- frequency l1 h1 ⊑ frequencyAux (List.sum (Prod.fst <$> l1)) ...
    simp only [frequency, Helpers.frequencyAux]
    apply MonoBind.bind_mono_right
    intro ⟨i, hge, hle_i⟩
    dsimp at *
    -- In the goal, we have a dependent `if ... then ... else` on both sides of the ⊑,
    -- so we case on whether it evaluates to true or false
    by_cases hi : i < (map Prod.fst l1).sum
    . -- i < (map Prod.fst l1).sum
      simp only [dif_pos hi]
      apply frequencySelect_le
      assumption
    . -- ¬ i < (map Prod.fst l1).sum
      simp only [dif_neg hi]
      apply PartialOrder.rel_refl
  . -- frequencyAux (List.sum (Prod.fst <$> l1)) ... ⊑ frequency l2 h2
    simp only [frequency]
    apply le_of_eq
    apply frequencyAux_congr
    apply sumOfWeights_le
    assumption

/-- Lemma allowing us to use `frequency` in functions marked as `partial_fixpoint`
    (the `monotonicity` tactic is used under the hood by `partial_fixpoint`) -/
@[partial_fixpoint_monotone]
theorem monotone_frequency [Gen G] {γ : Sort w} [PartialOrder γ]
    (gs : γ → List (Nat × (Unit → G α))) (hne : ∀ x, 0 < List.sum (List.map Prod.fst (gs x))) (hmono : monotone gs) :
    monotone (fun x => frequency (gs x) (hne x)) := by
  unfold monotone at *
  intro x y hxy
  apply frequency_le
  apply hmono
  assumption
