/-
Copyright (c) 2026 Harrison Goldstein & Ernest Ng. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Ernest Ng
-/
module

public import BasaltExamples.UniformConstrained.Uniformity
public import Mathlib.Data.Fintype.Prod

/-!
# When does `sizedP` terminate? (Section 4, the Lemma 2 discussion)

The paper's termination argument for `sizedP` needs `inspectsFst` to be deterministic, "for example
satisfying the law `inspectsFst p ⇒ not (inspectsFst (p ∘ swap))`" (`LazyOracle.SwapLaw`). This file
shows that law is not enough — `cycleOracle` satisfies it, and `sizedP` loops on a product of three
`Pay`-guarded spaces — and that the right-first oracle, the paper's unguided `sizedP p (a *** b)`,
terminates within `Space.measure s` fuel, which discharges `Theorem2`'s `FuelSuffices`.
-/

@[expose] public section

open ENNReal

namespace UniformConstrained

open scoped Space

variable {α : Type}

/-! ## The swap law does not ensure termination

For `(A :*: B) :*: C`, the `inspectsFst` branch of `sizedP` gives
`swap :$: (C *** (A :*: B)) = swap :$: (assoc :$: ((C :*: A) :*: B))`, so after two `:$:` steps the
state is `(C :*: A) :*: B`, with the predicate precomposed with `swap ∘ assoc`. Answering `true`
again gives `(B :*: C) :*: A`, then `(A :*: B) :*: C`: no size is paid, so `sizedP` never stops.

None of the predicates this queries is `q ∘ swap` for another queried `q` — they all live on
`(_ × _) × _` — so the swap law never applies. A real lazy predicate answers consistently with the
one leaf it forces first: if it forces `A`, it answers `true` at `(A, B), C` and `(C, A), B`, where
`A` is in the first component, but `false` at `(B, C), A`, which breaks the cycle. The paper's
measure `(k, r, q)` needs exactly that consistency ("`q` is the position … of the leaf that is
requested by the evaluation of the predicate"); its Section 4.1 notes the risk of non-termination
"when the order of evaluation of the predicate is not consistent between different invocations of
`inspectsFst`", but the law it states does not exclude it. -/

/-- An oracle that is never sure (`universal = none`) and answers `inspectsFst = true` exactly for
predicates on `(Bool × Bool) × Bool`. Lean cannot inspect a type, so the answer is chosen
classically. -/
noncomputable def cycleOracle : LazyOracle where
  universal _ := none
  inspectsFst {α β} _ := @decide (α = (Bool × Bool) ∧ β = Bool) (Classical.propDecidable _)
  universal_sound := by intro _ _ _ h; cases h

theorem bool_ne_bool_prod : Bool ≠ (Bool × Bool) := by
  intro h
  have := Fintype.card_congr (Equiv.cast h)
  simp at this

/-- `cycleOracle` satisfies the paper's law: `p ∘ swap` lives on `Bool × (Bool × Bool)`. -/
theorem cycleOracle_swapLaw : cycleOracle.SwapLaw := by
  intro α β p h
  simp only [cycleOracle, decide_eq_true_eq, decide_eq_false_iff_not] at h ⊢
  obtain ⟨rfl, rfl⟩ := h
  exact fun h => bool_ne_bool_prod h.1

/-- Three `Pay`-guarded leaves, nested to the left. -/
def spaceTriple : Space ((Bool × Bool) × Bool) := (spaceBool :*: spaceBool) :*: spaceBool

/-- The triple has values: eight of them at size 3, one per triple of booleans. -/
theorem card_sized_spaceTriple : (Space.sized spaceTriple 3).card = 8 := by decide

/-- **`sizedP` loops on `spaceTriple` under `cycleOracle`**: for every fuel and every predicate,
it runs out. Each lap of the cycle costs three fuel and returns to `spaceTriple`. -/
theorem sizedP_cycleOracle_spaceTriple : ∀ (fuel : Nat) (q : (Bool × Bool) × Bool → Bool)
    (k : Nat), sizedP cycleOracle fuel q spaceTriple k = none := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | _ fuel ih =>
  intro q k
  have hfst : ∀ q : (Bool × Bool) × Bool → Bool, cycleOracle.inspectsFst q = true := fun _ => by
    simp [cycleOracle]
  have hu : ∀ {β : Type} (q : β → Bool), cycleOracle.universal q = none := fun _ => rfl
  rcases fuel with _ | _ | _ | fuel
  · rfl
  · simp only [spaceTriple, sizedP, hfst, ite_true]
  · simp only [spaceTriple, sizedP, hfst, hu, ite_true, Space.prodR_prod, reduceCtorEq, ite_false,
      Option.map_none]
  · simp only [spaceTriple, sizedP, hfst, hu, ite_true, Space.prodR_prod, reduceCtorEq, ite_false]
    rw [show (spaceBool :*: spaceBool) :*: spaceBool = spaceTriple from rfl, ih fuel (by omega)]
    rfl

/-- So `uniform` never produces a value from `spaceTriple`, whatever the fuel: `FuelSuffices` fails
for every fuel, and the paper's Theorem 2 has no instance here although every value satisfies the
predicate. -/
theorem uniform_cycleOracle_spaceTriple (fuel : Nat) (k : Nat) (x : (Bool × Bool) × Bool) :
    (uniform cycleOracle fuel (fun _ => true) spaceTriple k : SPMF _) (some x) = 0 := by
  rw [uniform_eq, sizedP_cycleOracle_spaceTriple]
  simp [SPMF.pure_apply]

theorem not_fuelSuffices_cycleOracle_spaceTriple (fuel k : Nat) (q : (Bool × Bool) × Bool → Bool) :
    ¬ FuelSuffices cycleOracle fuel q spaceTriple k := fun h => by
  simpa [sizedP_cycleOracle_spaceTriple] using h spaceTriple (.refl _)

/-! ## The right-first oracle terminates

With `inspectsFst` constantly `false`, `sizedP` always expands the *right* operand of a product,
which is the plain `sizedP p (a :*: b) = sizedP p (a *** b)` the paper starts from (Section 3.1)
before making the order predicate-guided. Weighting the right operand of a product double makes
every step of `sizedP` decrease `Space.measure`, and residual spaces are never larger than the space
they came from, so `Space.measure s` fuel suffices for `uniform p s k` at every `k`. -/

/-- A size of a space in which `***` decreases: the right operand of a product counts double. -/
def Space.measure : {α : Type} → Space α → Nat
  | _, .empty => 1
  | _, .pure _ => 1
  | _, .union a b => 1 + max a.measure b.measure
  | _, .prod a b => 1 + a.measure + 2 * b.measure
  | _, .pay a => 1 + a.measure
  | _, .fmap _ a => 1 + a.measure

theorem Space.measure_pos {α : Type} (s : Space α) : 0 < s.measure := by
  cases s <;> simp only [Space.measure] <;> omega

/-- `***` is a step down in `Space.measure`. -/
theorem Space.measure_prodR_lt {α β : Type} (a : Space α) (b : Space β) :
    (a *** b).measure < (a :*: b).measure := by
  cases b with
  | union c d => simp only [Space.prodR_union, Space.measure]; omega
  | prod c d =>
    have := d.measure_pos
    simp only [Space.prodR_prod, Space.measure]; omega
  | pure x => simp only [Space.prodR_pure, Space.measure]; omega
  | empty => have := a.measure_pos; simp only [Space.prodR_empty, Space.measure]; omega
  | pay c => simp only [Space.prodR_pay, Space.measure]; omega
  | fmap f c => simp only [Space.prodR_fmap, Space.measure]; omega

/-- **With a right-first oracle, `sizedP` succeeds within `Space.measure s` fuel, and its residual
spaces are no larger than `s`.** -/
theorem sizedP_of_measure_le (O : LazyOracle) (hO : ∀ {α β : Type} (q : α × β → Bool),
    O.inspectsFst q = false) : ∀ (fuel : Nat) {α : Type} (p : α → Bool) (s : Space α) (k : Nat),
    s.measure ≤ fuel → ∃ r, sizedP O fuel p s k = some r ∧ ∀ s' ∈ rights r, s'.measure ≤ s.measure := by
  intro fuel
  induction fuel with
  | zero => intro _ _ s _ h; have := s.measure_pos; omega
  | succ fuel ih =>
    intro α p s k hle
    cases s with
    | empty => exact ⟨.empty, by simp [sizedP]⟩
    | pure a =>
      cases k with
      | zero =>
        refine ⟨_, by simp only [sizedP]; rfl, fun s' hs' => ?_⟩
        by_cases hp : p a <;> simp_all [Space.measure]
      | succ k => exact ⟨.empty, by simp [sizedP]⟩
    | pay a =>
      cases k with
      | zero => exact ⟨.empty, by simp [sizedP]⟩
      | succ k =>
        obtain ⟨r, hr, hres⟩ := ih p a k (by simp only [Space.measure] at hle; omega)
        refine ⟨_, by simp only [sizedP, hr, Option.map_some]; rfl, fun s' hs' => ?_⟩
        rw [rights_rebuild, Multiset.mem_map] at hs'
        obtain ⟨t, ht, rfl⟩ := hs'
        have := hres t ht
        simp only [Space.measure]; omega
    | union a b =>
      simp only [Space.measure] at hle
      obtain ⟨ra, hra, hresa⟩ := ih p a k (by omega)
      obtain ⟨rb, hrb, hresb⟩ := ih p b k (by omega)
      refine ⟨_, by simp only [sizedP, hra, hrb]; rfl, fun s' hs' => ?_⟩
      rw [rights_union, rights_rebuild, rights_rebuild, Multiset.mem_add] at hs'
      rcases hs' with hs' | hs' <;> obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.mp hs'
      · have := hresa t ht; simp only [Space.measure]; omega
      · have := hresb t ht; simp only [Space.measure]; omega
    | fmap f a =>
      simp only [Space.measure] at hle
      by_cases hu : O.universal (p ∘ f) = some false
      · refine ⟨_, by simp only [sizedP, hu, ite_true]; rfl, fun s' hs' => ?_⟩
        rw [rights_replicateSet_inr] at hs'
        rw [Multiset.eq_of_mem_replicate hs']
        simp only [Space.measure]; omega
      · obtain ⟨r, hr, hres⟩ := ih (p ∘ f) a k (by omega)
        refine ⟨_, by simp only [sizedP, hu, ite_false, hr, Option.map_some]; rfl, fun s' hs' => ?_⟩
        rw [rights_fmap_applyE, Multiset.mem_map] at hs'
        obtain ⟨t, ht, rfl⟩ := hs'
        have := hres t ht
        simp only [Space.measure]; omega
    | prod a b =>
      have hlt := Space.measure_prodR_lt a b
      obtain ⟨r, hr, hres⟩ := ih p (a *** b) k (by omega)
      refine ⟨r, by simp only [sizedP, hO, Bool.false_eq_true, ite_false, hr], fun s' hs' => ?_⟩
      have := hres s' hs'
      omega

/-- `Space.measure s` fuel suffices for `uniform p s k` under a right-first oracle. -/
theorem fuelSuffices_of_measure_le (O : LazyOracle) (hO : ∀ {α β : Type} (q : α × β → Bool),
    O.inspectsFst q = false) {α : Type} (p : α → Bool) (s : Space α) (k : Nat) {fuel : Nat}
    (hle : s.measure ≤ fuel) : FuelSuffices O fuel p s k := by
  intro t ht
  -- Every reachable space is at most as large as `s`.
  suffices h : ∀ s t, Reachable O fuel p k s t → s.measure ≤ fuel → t.measure ≤ fuel by
    obtain ⟨r, hr, _⟩ := sizedP_of_measure_le O hO fuel p t k (h s t ht hle)
    simp [hr]
  intro s t ht
  induction ht with
  | refl => exact id
  | step hr hs' _ ih =>
    intro hle
    obtain ⟨r', hr', hres⟩ := sizedP_of_measure_le O hO fuel p _ k hle
    rw [hr] at hr'
    cases hr'
    exact ih ((hres _ hs').trans hle)

/-- **The paper's Theorem 2 holds as stated for a right-first oracle**, with fuel
`Space.measure s`. -/
theorem Theorem2_rightFirst [DecidableEq α] (O : LazyOracle) (hO : ∀ {α β : Type}
    (q : α × β → Bool), O.inspectsFst q = false) (p : α → Bool) (s : Space α) (k : Nat)
    (hb : 0 < (satisfying p s k).card) (x : α) :
    (uniform O s.measure p s k : SPMF (Option α)) (some x)
      = (if p x then ((allOfSize s k).count x : ℝ≥0∞) else 0)
        / ((satisfying p s k).card : ℝ≥0∞) :=
  Theorem2 O _ p s k hb (fuelSuffices_of_measure_le O hO p s k le_rfl) x

end UniformConstrained
