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

Derived combinators (`chooseNat`, `elements`, `oneOf`, `frequency`, `listOf`, …), all built on
`RandomChoice.choose`.
-/

open List

namespace Helpers

/-- Helper function for the `frequency` combinator: `frequencySelect xs n` chooses a weight & a
generator `(k, gen)` from the list `xs` such that `n < k`.  This function expects a proof `h : n <
sum(xs)`, which makes the empty-list case in the pattern-match irrefutable, since `n < 0` is `False`
(this is discharged immediately by `contradiction`). -/
def frequencySelect [Gen G] (xs : List (Nat × (Unit → G α))) (n : Nat)
    (h : n < List.sum (List.map Prod.fst xs)) : G α :=
  match xs with
  | [] => by contradiction
  | (k, x) :: xs =>
    if hlt : n < k then
      x ()
    else
      frequencySelect xs (n - k) (by simp only [List.map_cons, List.sum_cons] at h; omega)

/-- Implementation of the `oneOf` combinator, parameterized by an upper bound `n` for the random
index. The caller is required to supply a proof that `n` is strictly less than the list's length.
(`oneOf` instantiates `n` with `gs.length - 1`).  Making the upper bound a parameter allows us to
use the `oneOfAux_congr` lemma below to propogate equalities about the bound via `subst`, which is
used in the monotonicity proof for `oneOf` (`oneOf_le`). -/
def oneOfAux [Gen G] (l : List (Unit → G α)) (n : Nat)
    (hlt : ∀ i, i ≤ n → i < l.length) : G α := do
  let ⟨i, _, hle_i⟩ ← ULift.down <$> RandomChoice.choose 0 n (Nat.zero_le n)
  (l[i]'(hlt i hle_i)) ()

/-- Implementation of the `frequency` combinator, parameterized by the total weight `total`, which
serves as the (exclusive) upper bound for the random weight `n` sampled via `RandomChoice.choose`.
The caller supplies a proof `htotal` that `total` is the sum of the weights in `gs`. (`frequency`
instantiates `total` with `List.sum (List.map Prod.fst gs)`.)

Making `total` a parameter lets us use the `frequencyAux_congr` lemma to propagate equalities about
the total via `subst`, which is used in the monotonicity proof for `frequency` (`frequency_le`). -/
def frequencyAux [Gen G] (gs : List (Nat × (Unit → G α))) (total : Nat)
    (htotal : total = List.sum (List.map Prod.fst gs)) : G α := do
  let n ← ULift.down <$> RandomChoice.choose 0 (total - 1) (Nat.zero_le _)
  if hn : n < total then
    frequencySelect gs n (by omega)
  else
    default

end Helpers

section side_condition_tactic

/-- This tactic discharges common side conditions for `chooseNat`, `elements`, and `frequency`. -/
syntax "gen_side_condition" : tactic

macro_rules
  | `(tactic| gen_side_condition) =>
    `(tactic| first
        | (simp; done)
        | (simp_all only [decide_eq_true_eq]; done)
        | (simp_all; done))

end side_condition_tactic

/-- Choose a plain `Nat` uniformly from `[lo, hi]` (inclusive). Prefer this over raw `choose` in
generators: it hides `choose`'s `ULift` subtype from bodies and proofs. -/
def chooseNat [Gen G] (lo hi : Nat) (h : lo ≤ hi := by gen_side_condition) : G Nat :=
  (·.down.val) <$> RandomChoice.choose lo hi h

/-- Same as `chooseNat` but for signed `Int`s.  -/
def chooseInt [Gen G] (lo hi : Int) (_h : lo ≤ hi := by gen_side_condition) : G Int := do
  let k ← chooseNat 0 (hi - lo).toNat (Nat.zero_le _)
  return lo + (k : Int)

/-- Generates an element of the list `xs` at random.  This combinator takes as input a proof that
`xs` is non-empty, discharged by `gen_side_condition` when omitted. -/
def elements [Gen G] (xs : List α) (hne : xs ≠ [] := by gen_side_condition) : G α := do
  let ⟨i, ⟨ hge, hle ⟩⟩ ← ULift.down <$> RandomChoice.choose 0 (xs.length - 1) (by omega)
  have hlen : 0 < xs.length := by
    apply length_pos_iff.mpr
    assumption
  have hlt : i < xs.length := by omega
  return xs[i]'hlt

/-- Picks one of the generators in `gs` at random.  This combinator takes as input a proof that `gs`
is non-empty, discharged by `gen_side_condition` when omitted. -/
def oneOf [Gen G] (gs : List (Unit → G α)) (hne : gs ≠ [] := by gen_side_condition) : G α :=
  Helpers.oneOfAux gs (gs.length - 1) (by
    intro i hi
    have hlen : 0 < gs.length := length_pos_iff.mpr hne
    omega)

/-- `frequency` picks a generator from the list `gs` according to the weights in `gs`.  This
combinators also takes an additional hypothesis that the sum of the weights in the list is non-zero
(this is discharged by `gen_side_condition` when omitted). -/
def frequency [Gen G] (gs : List (Nat × (Unit → G α)))
  (_h : 0 < List.sum (List.map Prod.fst gs) := by gen_side_condition) : G α :=
  Helpers.frequencyAux gs (List.sum (List.map Prod.fst gs)) rfl

/-- A stop-or-continue choice with `n` further steps available, weighted so that the **number of
steps taken is uniform on `[0, n]`**.

The recursion `stopOrGo n stop go` with `go` recursing at `n - 1` stops with probability
`1 / (n + 1)` at every remaining budget `n`, and those telescope: `P(at least k steps)` is
`(n + 1 - k) / (n + 1)`, so every length in `[0, n]` is equally likely. The obvious alternative,
`pick stop go`, halves the mass at every step and puts `2⁻ᵏ` on `k` steps — which is complete for
the bound but samples anywhere near it essentially never. Completeness proofs cannot see the
difference (`SPMF.support_stopOrGo`), which is exactly why the choice is worth naming. -/
def stopOrGo [Gen G] (n : Nat) (stop go : Unit → G α) : G α :=
  frequency [(1, stop), (n + 1, go)]
    (by simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; omega)

/-- Generates a length-`n` list, where each element is generated by the generator `g` -/
def vectorOf [Gen G] (n : Nat) (g : G α) : G (List α) :=
  List.foldr (fun m acc => do
    let x ← m
    let xs ← acc
    pure (x :: xs)) (pure []) (List.replicate n g)

/-- Helper lemma that unfolds one layer of recursion in `vectorOf (n + 1) g`.  This is needed for
the lemmas `support_vectorOf`, `IsPMF_vectorOf`. -/
theorem vectorOf_succ [Gen G] {n : Nat} {g : G α} :
    vectorOf (n + 1) g = (do let x ← g; let xs ← vectorOf n g; pure (x :: xs)) :=
  rfl

/-- `listOfMaxLength n g` generates a list whose length is unformly distributed across `[0, n]`,
(i.e. the list may be empty and its maximum possible length is `n` inclusive). Each list element is
produced by the generator `g`. -/
def listOfMaxLength [Gen G] (n : Nat) (g : G α) : G (List α) := do
  let ⟨k, _⟩ ← ULift.down <$> RandomChoice.choose 0 n (Nat.zero_le n)
  vectorOf k g

/-- Generates a (possibly empty) list with unbounded length where each element is produced using
`g`.  Note: this produces the empty list 50% of the time, so for production generators, you should
consider using other combinators, e.g. `listOfMaxLength`. -/
def listOf [Gen G] (g : G α) : G (List α) := do
  RandomChoice.pick
    (fun () => pure [])
    (fun () => do
      let x ← g
      let xs ← listOf g
      return x :: xs)
partial_fixpoint

/-- Lifts a generator of `α`'s into a generator of `Option α`'s, which returns `some <$> g` with
probability `r`.

Note: we explicitly use `bind` instead of `<$>` in the body of this combinator, as there is no
monotonicity lemma for `<$>` in `Lean.Order`. -/
def biasedOptionGen [Gen G] (r : Rat) (g : G α) : G (Option α) := do
  if ← RandomChoice.coin r then do
    let x ← g
    pure (some x)
  else
    pure none

/-- Lifts a generator of `α`'s into a generator of `Option α`'s, which returns `none` with probability 1/2 -/
def optionGen [Gen G] (g : G α) : G (Option α) :=
  biasedOptionGen (1 / 2) g

/-- Generates a *non-empty* list with unbounded length, where each element is produced using `g`. -/
def nonEmptyListOf {G α} [Gen G] (g : G α) : G (List α) := do
  RandomChoice.pick
    (fun () => do let x ← g; pure [x])
    (fun () => do
      let x ← g
      let xs ← nonEmptyListOf g
      return x :: xs)
partial_fixpoint

/-- Define a partial order over `List α` that says `l1 ⊑ l2` when:
- `l1.length = l2.length`
- `l1[i] ⊑ l2[i]` for all list elements (here we are comparing them using the `PartialOrder` on `α`) -/
instance List.instPartialOrder {α : Type u} [PartialOrder α] :
    PartialOrder (List α) where
  rel l1 l2 :=
    l1.length = l2.length ∧
    ∀ (i : Nat) (h1 : i < l1.length) (h2 : i < l2.length), l1[i] ⊑ l2[i]
  rel_refl := by
    intro xs
    constructor
    . rfl
    . intro i _ _
      apply PartialOrder.rel_refl
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
  rel_antisymm := by
    intro x y hxy hyx
    obtain ⟨hlen, helem_xy⟩ := hxy
    obtain ⟨_, helem_yx⟩ := hyx
    apply List.ext_getElem hlen
    intro i hx hy
    apply PartialOrder.rel_antisymm
    . apply helem_xy
    . apply helem_yx

/-- The partial order on `Nat × α` behind `frequency`'s monotonicity: `(w1, g1) ⊑ (w2, g2)` iff
`w1 = w2 ∧ g1 ⊑ g2`. The weights must be *equal*, not `≤` — raising one branch's weight lowers every
other branch's probability, so under `w1 ≤ w2` the `frequency` combinator would not be monotone in
`⊑` on `SPMF`. -/
instance {α : Type u} [PartialOrder α] : PartialOrder (Nat × α) where
  rel p q := p.1 = q.1 ∧ p.2 ⊑ q.2
  rel_refl := by
    intro p
    constructor
    . rfl
    . apply PartialOrder.rel_refl
  rel_trans := by
    intro p q r hpq hqr
    obtain ⟨hw1, hg1⟩ := hpq
    obtain ⟨hw2, hg2⟩ := hqr
    constructor
    . apply hw1.trans; assumption
    . apply PartialOrder.rel_trans <;> assumption
  rel_antisymm := by
    intro p q hpq hqp
    obtain ⟨hw, hg⟩ := hpq
    obtain ⟨_, hg'⟩ := hqp
    apply Prod.ext
    . assumption
    . apply PartialOrder.rel_antisymm <;> assumption

/- This lemma lets the `monotonicity` tactic (invoked by `partial_fixpoint` under the hood)
decompose a list literal `[e₁, e₂, …]` into `e₁ :: (e₂ :: …)` when all the `eᵢ` are functions. -/
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
  . simpa using heq
  . intro i h1 h2
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


/-- Monotonicity of `frequencySelect`: if `l1 ⊑ l2` and the same random weight `n` is
    in less than each list's sum of weights (`h1`, `h2`),
    then `frequencySelect l1 n h1 ⊑ frequencySelect l2 n h2` -/
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
      have hzero := hrel 0 (by simp) (by simp)
      obtain ⟨hweight, helt⟩ := hzero
      simp [List.getElem_cons_zero] at hweight helt
      subst hweight
      unfold Helpers.frequencySelect
      split
      . apply helt
      . have htail : xs ⊑ ys := by
          constructor
          . injection hlen_eq
          . intro i hi1 hi2
            specialize hrel (i + 1)
            dsimp at hrel
            apply hrel <;> omega
        apply IH
        assumption

/-- If `n < sum (fst <$> gs)`, then `frequencySelect gs n h` picks a sub-generator from `gs` that
has non-zero weight `w`. -/
theorem frequencySelect_mem [Gen G]
    {gs : List (Nat × (Unit → G α))}
    {n : Nat}
    (h : n < (List.map Prod.fst gs).sum) :
    ∃ w g, ⟨ w, g ⟩ ∈ gs ∧ 0 < w ∧ Helpers.frequencySelect gs n h = g () := by
  induction gs generalizing n with
  | nil => simp at h
  | cons hd tl ih =>
    unfold Helpers.frequencySelect
    obtain ⟨ w, g ⟩ := hd
    split
    · exists w, g
      constructor
      . apply List.Mem.head
      . constructor
        . omega
        . rfl
    · have h_remaining_weight : n - w < List.sum (List.map Prod.fst tl) := by
        simp only [List.map_cons, List.sum_cons] at h
        omega
      obtain ⟨w', g', hwg_mem, hwg_pos, hwg_eq⟩ := ih h_remaining_weight
      exists w', g'
      constructor
      . apply List.mem_cons_of_mem
        assumption
      . constructor <;> assumption

/-- If two lists `l1, l2 : List (Nat × α)` satisfy `l1 ⊑ l2`, then the sum of their weights
    must be equal -/
private theorem sumOfWeights_le {α : Type u} [PartialOrder α] {l1 l2 : List (Nat × α)}
      (hle : l1 ⊑ l2) :
      List.sum (List.map Prod.fst l1) = List.sum (List.map Prod.fst l2) := by
  obtain ⟨hlen, hrel⟩ := hle
  congr 1
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
  apply PartialOrder.rel_trans
    (y := Helpers.oneOfAux l2 (l1.length - 1) (by omega))
  . simp only [oneOf, Helpers.oneOfAux]
    apply MonoBind.bind_mono_right
    intro ⟨i, hge, hle_i⟩
    apply hle
  . simp only [oneOf]
    apply le_of_eq
    apply oneOfAux_congr <;> omega

/-- Single general `@[partial_fixpoint_monotone]` lemma.  The `monotonicity` tactic (invoked by
`partial_fixpoint` under the hood) sees `fun x => oneOf (gens x)` and uses this lemma, having
already established `monotone gens` via `List.monotone_cons`. -/
@[partial_fixpoint_monotone]
theorem monotone_oneOf [Gen G] {γ : Sort w} [PartialOrder γ]
    (gs : γ → List (Unit → G α)) (hne : ∀ x, gs x ≠ []) (hmono : monotone gs) :
    monotone (fun x => oneOf (gs x) (hne x)) := by
  intro x y hxy
  unfold monotone at hmono
  apply oneOf_le
  apply hmono
  assumption

/-- This lemma allows the `monotonicity` tactic to reason about pairs of the form `(w, g x)` that
appear in the list supplied to the `frequency` combinator.  Here, the weight `w` is a constant `Nat`
and the generator `g` assumed to be monotone. -/
@[partial_fixpoint_monotone]
theorem monotone_pair_snd {α : Type u} {γ : Sort w} [PartialOrder α] [PartialOrder γ]
    (w : Nat) (g : γ → α) (hg : monotone g) :
    monotone (fun x => (w, g x)) := by
  intro x y hxy
  exact ⟨rfl, hg x y hxy⟩

/-- Monotonicity of `frequency`: if `l1 ⊑ l2` (equal weights, pointwise-related generators) and both
have positive total weight (`h1, h2`), then `frequency l1 h1 ⊑ frequency l2 h2`. -/
theorem frequency_le [Gen G] {l1 l2 : List (Nat × (Unit → G α))} (h : l1 ⊑ l2)
    (h1 : 0 < List.sum (List.map Prod.fst l1))
    (h2 : 0 < List.sum (List.map Prod.fst l2)) :
    frequency l1 h1 ⊑ frequency l2 h2 := by
  apply PartialOrder.rel_trans
    (y := Helpers.frequencyAux l2 (List.sum (List.map Prod.fst l1)) (sumOfWeights_le h))
  . simp only [frequency, Helpers.frequencyAux]
    apply MonoBind.bind_mono_right
    intro ⟨i, hge, hle_i⟩
    dsimp at *
    by_cases hi : i < (map Prod.fst l1).sum
    . simp only [dif_pos hi]
      apply frequencySelect_le
      assumption
    . simp only [dif_neg hi]
      apply PartialOrder.rel_refl
  . simp only [frequency]
    apply le_of_eq
    apply frequencyAux_congr
    apply sumOfWeights_le
    assumption

/-- Lemma allowing us to use `frequency` in functions marked as `partial_fixpoint` (the
`monotonicity` tactic is used under the hood by `partial_fixpoint`) -/
@[partial_fixpoint_monotone]
theorem monotone_frequency [Gen G] {γ : Sort w} [PartialOrder γ]
    (gs : γ → List (Nat × (Unit → G α)))
    (hne : ∀ x, 0 < List.sum (List.map Prod.fst (gs x)))
    (hmono : monotone gs) :
    monotone (fun x => frequency (gs x) (hne x)) := by
  unfold monotone at *
  intro x y hxy
  apply frequency_le
  apply hmono
  assumption

/-- Monotonicity of `stopOrGo`, so it can appear in a `partial_fixpoint` body: the `monotonicity`
tactic cannot see through the definition to the `frequency` underneath. -/
@[partial_fixpoint_monotone]
theorem monotone_stopOrGo [Gen G] {γ : Sort w} [PartialOrder γ]
    (n : Nat) (stop go : γ → Unit → G α) (hstop : monotone stop) (hgo : monotone go) :
    monotone (fun x => stopOrGo n (stop x) (go x)) := by
  unfold stopOrGo
  exact monotone_frequency _ _
    (List.monotone_cons _ _ (monotone_pair_snd 1 stop hstop)
      (List.monotone_cons _ _ (monotone_pair_snd (n + 1) go hgo) (monotone_const [])))

/-- Lemma allowing us to use `vectorOf` in functions marked as `partial_fixpoint` (the
`monotonicity` tactic is used under the hood by `partial_fixpoint`). -/
@[partial_fixpoint_monotone]
theorem monotone_vectorOf [Gen G] {γ : Sort w} [PartialOrder γ]
    (n : Nat) (g : γ → G α) (hg : monotone g) :
    monotone (fun x => vectorOf n (g x)) := by
  unfold monotone at *
  induction n with
  | zero =>
    intro x y hxy
    simp [vectorOf]
    apply PartialOrder.rel_refl
  | succ n' IH =>
    intro x y hxy
    simp [vectorOf_succ]
    apply monotone_bind <;> try assumption
    apply monotone_of_monotone_apply
    intro z
    apply monotone_bind <;> (unfold monotone; intro x' y' hxy')
    . apply IH
      assumption
    . dsimp
      apply PartialOrder.rel_refl

/-- Lemma allowing us to use `listOfMaxLength` in functions marked as `partial_fixpoint` (the
`monotonicity` tactic is used under the hood by `partial_fixpoint`). -/
@[partial_fixpoint_monotone]
theorem monotone_listOfMaxLength [Gen G] {γ : Sort w} [PartialOrder γ]
    (n : Nat) (g : γ → G α) (hg : monotone g) :
    monotone (fun x => listOfMaxLength n (g x)) := by
  unfold listOfMaxLength
  apply monotone_bind
  . apply monotone_const
  . dsimp
    apply monotone_of_monotone_apply
    intro ⟨x, hge, hle⟩
    dsimp
    apply monotone_vectorOf
    assumption

/-- Lemma allowing us to use `listOf` in functions marked as `partial_fixpoint` (the `monotonicity`
tactic is used under the hood by `partial_fixpoint`). -/
@[partial_fixpoint_monotone]
theorem monotone_listOf [Gen G] {γ : Sort w} [PartialOrder γ]
    (g : γ → G α) (hg : monotone g) :
    monotone (fun x => listOf (g x)) := by
  unfold monotone
  intro x y hxy
  show listOf (g x) ⊑ listOf (g y)
  generalize hw : listOf (g y) = w
  delta listOf
  apply Lean.Order.fix_induct (motive := fun z => z ⊑ w)
  · intro c hc hall
    apply Lean.Order.csup_le <;> assumption
  · intro z hz
    subst hw
    unfold listOf
    simp only [RandomChoice.pick]
    apply MonoBind.bind_mono_right
    intro n
    split
    · apply PartialOrder.rel_refl
    · apply PartialOrder.rel_trans (MonoBind.bind_mono_left (hg x y hxy))
      apply MonoBind.bind_mono_right
      intro a
      apply MonoBind.bind_mono_left
      assumption

/-- Lemma allowing us to use `biasedOptionGen` in functions marked as `partial_fixpoint`. -/
@[partial_fixpoint_monotone]
theorem monotone_biasedOptionGen [Gen G] [PartialOrder γ]
    (g : γ → G α) (hg : monotone g) :
    monotone (fun x => biasedOptionGen r (g x)) := by
  unfold biasedOptionGen
  apply monotone_bind
  . apply monotone_const
  . apply monotone_of_monotone_apply
    intro b
    cases b <;> simp
    . apply monotone_const
    . apply monotone_bind
      . assumption
      . apply monotone_const

/-- Lemma allowing us to use `optionGen` in functions marked as `partial_fixpoint` -/
@[partial_fixpoint_monotone]
theorem monotone_optionGen [Gen G] [PartialOrder γ]
    (g : γ → G α) (hg : monotone g) :
    monotone (fun x => optionGen (g x)) := by
  unfold optionGen
  apply monotone_biasedOptionGen
  assumption

/-- Lemma allowing us to use `nonEmptyListOf` in functions marked as `partial_fixpoint` (the
`monotonicity` tactic is used under the hood by `partial_fixpoint`). -/
@[partial_fixpoint_monotone]
theorem monotone_nonEmptyListOf [Gen G] {γ : Sort w} [PartialOrder γ]
    (g : γ → G α) (hg : monotone g) :
    monotone (fun x => nonEmptyListOf (g x)) := by
  unfold monotone
  intro x y hxy
  show nonEmptyListOf (g x) ⊑ nonEmptyListOf (g y)
  generalize hw : nonEmptyListOf (g y) = w
  delta nonEmptyListOf
  apply Lean.Order.fix_induct (motive := fun z => z ⊑ w)
  · intro c hc hall
    apply Lean.Order.csup_le <;> assumption
  · intro z hz
    subst hw
    unfold nonEmptyListOf
    simp only [RandomChoice.pick]
    apply MonoBind.bind_mono_right
    intro n
    split
    · unfold monotone at hg
      apply MonoBind.bind_mono_left
      apply hg
      assumption
    · apply PartialOrder.rel_trans (MonoBind.bind_mono_left (hg x y hxy))
      apply MonoBind.bind_mono_right
      intro a
      apply MonoBind.bind_mono_left
      assumption
