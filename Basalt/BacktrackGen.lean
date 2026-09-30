/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Segev Elazar Mittelman
-/
import Basalt.Gen

/-!
# Backtracking Generators

`BacktrackGen G α` is a generator that may fail, with the failure an observable value of `G` rather
than divergence, so a combinator can react to it and retry: `backtrack` samples weighted branches
without replacement until one succeeds. `BacktrackGen G` is itself a `Gen`.
-/

open Lean.Order

/-- The result of a producer that may fail. `refuted` claims the branch does not apply; `exhausted`
claims nothing, only that the budget ran out first — so a combinator that merges failures must not
report `refuted` when any branch was `exhausted`. -/
inductive Outcome (α : Type) where
  | ok : α → Outcome α
  | refuted : Outcome α
  | exhausted : Outcome α
  deriving Repr, DecidableEq, Inhabited

namespace Outcome

/-- Renaming, which cannot change a verdict. -/
def map (f : α → β) : Outcome α → Outcome β
  | .ok a => .ok (f a)
  | .refuted => .refuted
  | .exhausted => .exhausted

end Outcome

/-- Which kind of producer a `Producer` is: a phantom index, so a generator and an enumeration over
the same carrier are different types and a combinator for one cannot resolve at the other. -/
inductive ProducerKind where
  /-- One outcome per run; alternatives are sampled. -/
  | gen
  /-- Many outcomes; alternatives are unioned. -/
  | enum
  deriving Repr, DecidableEq, Inhabited

/-- A producer of `α` over the carrier `m`, whose failures are values inside `m`. -/
structure Producer (k : ProducerKind) (m : Type → Type) (α : Type) where
  run : m (Outcome α)

namespace Producer

/-- Bind short-circuits on either failure. Stated for any `Monad m` rather than for `Gen`, so it
applies at carriers that are not generators. -/
instance [Monad m] : Monad (Producer k m) where
  pure a := ⟨pure (.ok a)⟩
  bind x f := ⟨do
    match ← x.run with
    | .ok a => (f a).run
    | .refuted => pure .refuted
    | .exhausted => pure .exhausted⟩

/-- Lift a producer that cannot fail. -/
def lift [Monad m] (g : m α) : Producer k m α :=
  ⟨do let a ← g; pure (.ok a)⟩

/-- `bind (lift g) f` without the intermediate `Outcome`. -/
@[inline] def liftBind [Monad m] (g : m α) (f : α → Producer k m β) : Producer k m β :=
  ⟨do let a ← g; (f a).run⟩

/-- This branch definitively does not apply. -/
def refute [Monad m] : Producer k m α :=
  ⟨pure .refuted⟩

/-- Nothing was determined. -/
def exhaust [Monad m] : Producer k m α :=
  ⟨pure .exhausted⟩

/-- Downgrade a refutation to `exhausted`. For a disjunction that was offered only some of its
alternatives, whose collective failure is not a refutation of the whole. -/
def refutedToExhausted [Monad m] (g : Producer k m α) : Producer k m α :=
  ⟨do
    match ← g.run with
    | .ok a => pure (.ok a)
    | _ => pure .exhausted⟩

@[simp] theorem run_pure [Monad m] (a : α) : (pure a : Producer k m α).run = pure (.ok a) := rfl
@[simp] theorem run_refute [Monad m] : (refute : Producer k m α).run = pure .refuted := rfl
@[simp] theorem run_exhaust [Monad m] : (exhaust : Producer k m α).run = pure .exhausted := rfl
@[simp] theorem run_lift [Monad m] (g : m α) :
    (lift g : Producer k m α).run = (do let a ← g; pure (.ok a)) := rfl

/-- Collapse the `Outcome`, mapping either failure to `default`. -/
def collapse [Monad m] [Inhabited α] (g : Producer k m α) : m α := do
  match ← g.run with
  | .ok a => pure a
  | _ => pure default

end Producer

/-- A backtracking generator: a `Producer` of the `gen` kind. -/
abbrev BacktrackGen (G : Type → Type) (α : Type) := Producer .gen G α

namespace BacktrackGen

/-- `default` is `exhausted`, the outcome that claims nothing. -/
instance [Monad G] : Inhabited (Producer .gen G α) where
  default := ⟨pure .exhausted⟩

/-- Lift a generator that cannot fail. -/
abbrev liftGen [Monad G] (g : G α) : BacktrackGen G α := Producer.lift g

@[inline, inherit_doc Producer.liftBind]
abbrev liftBind [Monad G] (g : G α) (f : α → BacktrackGen G β) : BacktrackGen G β :=
  Producer.liftBind g f

@[inherit_doc Producer.refute] abbrev refute [Monad G] : BacktrackGen G α := Producer.refute
@[inherit_doc Producer.exhaust] abbrev exhaust [Monad G] : BacktrackGen G α := Producer.exhaust

@[inherit_doc Producer.refutedToExhausted]
abbrev refutedToExhausted [Monad G] (g : BacktrackGen G α) : BacktrackGen G α :=
  Producer.refutedToExhausted g

@[inherit_doc Producer.collapse]
abbrev toGen [Monad G] [Inhabited α] (g : BacktrackGen G α) : G α := Producer.collapse g

/-! ## Order structure, through `run` -/

variable {G : Type → Type} [Gen G] {α : Type}

instance instPartialOrder : PartialOrder (BacktrackGen G α) where
  rel x y := x.run ⊑ y.run
  rel_refl := PartialOrder.rel_refl
  rel_trans h₁ h₂ := PartialOrder.rel_trans h₁ h₂
  rel_antisymm h₁ h₂ := congrArg (Producer.mk (k := .gen)) (PartialOrder.rel_antisymm h₁ h₂)

theorem chain_run {c : BacktrackGen G α → Prop} (hc : chain c) :
    chain (fun r => ∃ x, c x ∧ x.run = r) := by
  rintro r₁ r₂ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
  exact hc x y hx hy

instance instCCPO : CCPO (BacktrackGen G α) where
  has_csup {c} hc := by
    obtain ⟨s, hs⟩ := CCPO.has_csup (chain_run hc)
    refine ⟨⟨s⟩, fun x => ⟨fun h y hy => (hs x.run).mp h y.run ⟨y, hy, rfl⟩, fun h => ?_⟩⟩
    refine (hs x.run).mpr ?_
    rintro r ⟨y, hy, rfl⟩
    exact h y hy

instance instMonoBind : MonoBind (BacktrackGen G) where
  bind_mono_left h := MonoBind.bind_mono_left (m := G) h
  bind_mono_right h := by
    refine MonoBind.bind_mono_right (m := G) ?_
    intro o
    cases o with
    | ok a => exact h a
    | refuted => exact PartialOrder.rel_refl
    | exhausted => exact PartialOrder.rel_refl

instance instRandomChoice : RandomChoice (BacktrackGen G) where
  choose lo hi h := liftGen (RandomChoice.choose lo hi h)

instance instGen : Gen (BacktrackGen G) where
  instInhabited := fun _ => inferInstance
  instMonad := inferInstance
  instRandomChoice := instRandomChoice
  instCCPO := fun _ => instCCPO
  instMonoBind := instMonoBind

/-! ## Weighted backtracking -/

/-- Sum of the weights. -/
def sumWeights (gs : List (Nat × β)) : Nat :=
  (gs.map Prod.fst).sum

/-- The entry whose weight interval contains `n`, its weight, and the list without it. -/
def pickDrop [Inhabited β] (gs : List (Nat × β)) (n : Nat) : Nat × β × List (Nat × β) :=
  match gs with
  | [] => (0, default, [])
  | (k, g) :: rest =>
    if n < k then (k, g, rest)
    else
      let (k', g', rest') := pickDrop rest (n - k)
      (k', g', (k, g) :: rest')

/-- Pick a branch by weight and run it; on failure drop it and pick again among the rest. Fails
with `refuted` only if every branch did, and with `exhausted` if any branch did. Recursion is on a
fuel of `gs.length`, so it is structural. -/
def backtrack (gs : List (Nat × (Unit → BacktrackGen G α))) : BacktrackGen G α :=
  ⟨go gs.length (sumWeights gs) gs false⟩
where
  go : Nat → Nat → List (Nat × (Unit → BacktrackGen G α)) → Bool → G (Outcome α)
  | _, _, [], anyExhausted => pure (if anyExhausted then .exhausted else .refuted)
  | 0, _, _, _ => pure .exhausted
  | fuel + 1, total, gs@(_ :: _), anyExhausted => do
    let n ← RandomChoice.choose 0 (total - 1) (by omega)
    let (k, g, gs') := pickDrop gs n.down.val
    match ← (g ()).run with
    | .ok a => pure (.ok a)
    | .refuted => go fuel (total - k) gs' anyExhausted
    | .exhausted => go fuel (total - k) gs' true

end BacktrackGen
