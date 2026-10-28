/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Segev Elazar-Mittelman
-/
module

public import Basalt.Enum.Graded

/-!
# Enumerating Inside a Generator: Local Backtracking

`exhaust B sub p` runs a sub-generator `sub` as an enumeration, every path of it costing at most `B`
choices, keeps the values satisfying `p`, and draws one with the probability its paths carry. It is
rejection sampling of `sub` against `p` with the retries replaced by one look at every path:

* some value survives: `found a`, with `a` distributed as `sub` given `p` (and, if `B` cut paths
  off, given that it cost at most `B`);
* none does, and the paths within `B` carry all of `sub`'s probability: `refuted`. Every value
  `sub` can produce was looked at, so `p` holds of none of them.
* none does, and some probability is beyond `B`: `exhausted`. The budget ran out first.

`sub` is passed at every interpretation, so it can be run as an enumeration whatever the
surrounding generator is run at. It suits a small premise checked after a small draw, the shape
derived generators have; for a large space, sampled backtracking is the cheaper tool.
-/

@[expose] public section

open RandomChoice

namespace Basalt

/-! ## Drawing by rational weights -/

/-- One of the values, with probability proportional to its weight (all weights positive): the
weights scaled to naturals over their common denominator, and a draw on the running total. -/
def pickWeighted [Monad G] [RandomChoice G] (xs : List (α × Rat)) (hne : xs ≠ []) : G α :=
  let d := xs.foldl (fun d (_, w) => Nat.lcm d w.den) 1
  let ns := xs.map fun (a, w) => (a, w.num.toNat * (d / w.den))
  let total := ns.foldl (fun t (_, n) => t + n) 0
  do
    let r := (← choose 0 (total - 1) (Nat.zero_le _)).down.val
    let rec go : List (α × Nat) → Nat → Option α
      | [], _ => none
      | (a, n) :: rest, r => if r < n then some a else go rest (r - n)
    match go ns r with
    | some a => pure a
    | none => pure (xs.head hne).1

/-! ## Local backtracking -/

/-- What a local search found. -/
inductive Local (α : Type) where
  | found (a : α)
  | refuted
  | exhausted
  deriving Repr, BEq

/-- A generator at every interpretation. -/
abbrev Poly (α : Type) : Type 1 := ∀ (H : Type → Type) [Gen H], H α

/-- Look at every path of `sub` costing at most `b` choices, and draw one of the values satisfying
`p` with the probability of the paths to it. -/
def exhaust [Monad G] [RandomChoice G] (b : Nat) (sub : Poly α) (p : α → Bool) : G (Local α) :=
  match (sub (CostGraded WFinite)).upTo? b with
  | none => pure .exhausted
  | some es =>
    let good := es.filter (p ·.1)
    if h : good = [] then
      pure (if es.foldl (fun s (_, w) => s + w) (0 : Rat) == 1 then .refuted else .exhausted)
    else .found <$> pickWeighted good h

end Basalt
