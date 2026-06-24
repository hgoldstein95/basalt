import Init.Internal.Order

open Lean.Order

/-!
# MWE: monotonicity for `oneOf` in a universe-polymorphic generator monad

## Context

We are building a property-based testing library whose generator monad is
abstracted via a typeclass `Gen (g : Type u → Type v)`.

The `oneOf` combinator picks uniformly from a list of thunked generators by
drawing a `Nat` index with `RandomChoice.choose` and indexing with `getElem!`.

## Problem

A recursive generator using `oneOf` requires a `@[partial_fixpoint_monotone]`
lemma for `oneOf`.  Two natural approaches fail:

(A) A universally-quantified `∀ gs : List …` conclusion fails to elaborate
    because `monotone` requires the partial order's type argument to align, but
    `g : Type u → Type v` makes the list live at `Type v` while the recursion
    variable lives at a different level.

(B) Fixed-arity lemmas (`monotone_oneOf₂`, `monotone_oneOf₃`, …) require a
    lemma per list length; unmaintainable for user-facing combinators.

## Fix (following the Zulip suggestion)

Define a pointwise `PartialOrder` on `List α` and register two lemmas:
  · `List.monotone_cons` lets the tactic walk a list literal element-by-element.
  · `monotone_oneOf` is a single general lemma about functions producing lists.
-/

-- ============================================================
-- § 1  Typeclasses
-- ============================================================

/-- Uniform n-ary random choice. -/
class RandomChoice (m : Type u → Type v) where
  choose : (lo hi : Nat) → lo ≤ hi → m (ULift Nat)

/-- A generator monad: a universe-polymorphic monad with a CCPO structure
    (for `partial_fixpoint`) and random choice. -/
class Gen (g : Type u → Type v) where
  instInhabited : ∀ α, Inhabited (g α)
  instMonad     : Monad g
  instRC        : RandomChoice g
  instCCPO      : ∀ α, CCPO (g α)
  instMonoBind  : MonoBind g

instance [m : Gen g] : ∀ α, Inhabited (g α) := m.instInhabited
instance [m : Gen g] : Monad g               := m.instMonad
instance [m : Gen g] : RandomChoice g        := m.instRC
instance [m : Gen g] : ∀ α, CCPO (g α)      := m.instCCPO
instance [m : Gen g] : MonoBind g            := m.instMonoBind

-- ============================================================
-- § 2  The `oneOf` combinator
-- ============================================================

/-- Pick uniformly from a non-empty list of thunked generators.
    `getElem!` is used so the definition is non-dependent; it returns
    `default` for out-of-range indices (which never occur at runtime). -/
def oneOf [Gen G] (gs : List (Unit → G α)) : G α := do
  let i ← ULift.down <$> RandomChoice.choose 0 (gs.length - 1) (by omega)
  gs[i]! ()

-- ============================================================
-- § 3  The problem: `partial_fixpoint` fails
-- ============================================================

-- The following fails because the tactic cannot discharge the
-- monotonicity obligation for `oneOf`:
--
--   def myGen [Gen G] : Unit → G Nat := fun _ =>
--     oneOf [fun _ => pure 0, fun _ => do let n ← myGen (); pure (n + 1)]
--   partial_fixpoint
--
-- Error (roughly): failed to prove monotonicity of the body;
-- no `@[partial_fixpoint_monotone]` lemma for `oneOf` applies.

-- ============================================================
-- § 4  Fix: pointwise `PartialOrder` on `List` + two lemmas
-- ============================================================

-- `Init.Internal.Order` already provides `instOrderPi : PartialOrder (∀ x, β x)`,
-- so `Unit → G α` automatically gets a partial order once `PartialOrder (G α)`
-- is available (which follows from `CCPO (G α)`, provided by `Gen`).
-- We only need to add the list order.


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
  rel_antisymm h12 h21 := by
    obtain ⟨hlen, helem12⟩ := h12
    obtain ⟨_, helem21⟩ := h21
    apply List.ext_getElem hlen
    intro i hi1 hi2
    apply PartialOrder.rel_antisymm
    . apply helem12
    . apply helem21

-- Lets the tactic decompose a list literal `[e₁, e₂, …]` = `e₁ :: (e₂ :: …)`
-- into one element at a time; the empty-list base case is handled by the
-- tactic's existing constant-expression rule.
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

-- Key monotonicity fact: if two lists are related by the pointwise order,
-- then `oneOf` on them is related by the monad order.
-- Proof sketch:
--   · Equal lengths (from the list order) make the `choose` calls identical,
--     so only the continuations `fun i => lₖ[i]! ()` need be compared.
--   · In-bounds (i < l.length): `getElem!_pos` reduces to `getElem`, and the
--     element-wise list order provides the needed `l1[i] ⊑ l2[i]` as
--     `Unit → G α`; the Pi order then gives `l1[i] () ⊑ l2[i] ()`.
--   · Out-of-bounds: both sides reduce to `default` via `getElem!_neg`.
theorem oneOf_le [Gen G] {l1 l2 : List (Unit → G α)} (h : l1 ⊑ l2) :
    oneOf l1 ⊑ oneOf l2 := by
  obtain ⟨hlen_eq, hle⟩ := h
  -- `simp only [oneOf, hlen]` unfolds oneOf and rewrites l1.length → l2.length.
  -- We use simp rather than `unfold` + `rw` because the `choose` call contains a
  -- proof term `⋯ : 0 ≤ l1.length - 1` that depends on l1.length; `rw` would
  -- produce an ill-typed motive, whereas simp handles proof terms in Prop via
  -- proof irrelevance.
  simp only [oneOf, hlen_eq]
  -- After simp, both sides have `choose 0 (l2.length - 1) _` as the prefix;
  -- only the continuations differ.
  apply MonoBind.bind_mono_right
  intro i
  by_cases hi : i < l2.length
  · -- i < l2.length
    rw [getElem!_pos l1 i (by omega), getElem!_pos l2 i hi]
    apply hle
  · -- ¬ (i > l2.length)
    -- this is out-of-bounds, so both sides become `default ()`.
    rw [getElem!_neg l1 i (by omega), getElem!_neg l2 i hi]
    exact PartialOrder.rel_refl

-- Single general `@[partial_fixpoint_monotone]` lemma.
-- The tactic sees `fun x => oneOf (gens x)` and uses this lemma,
-- having already established `monotone gens` via `List.monotone_cons`.
@[partial_fixpoint_monotone]
theorem monotone_oneOf [Gen G] {γ : Sort w} [PartialOrder γ]
    (gs : γ → List (Unit → G α)) (hmono : monotone gs) :
    monotone (fun x => oneOf (gs x)) := by
  intro x y hxy
  unfold monotone at hmono
  apply oneOf_le
  apply hmono
  assumption

-- ============================================================
-- § 5  End-to-end: `partial_fixpoint` now succeeds
-- ============================================================

def myGen [Gen G] : Unit → G Nat := fun _ =>
  oneOf [fun _ => pure 0, fun _ => do let n ← myGen (); pure (n + 1)]
partial_fixpoint
