/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt.Gen
import Basalt.SPMF
import Basalt.SPMF.Cost
import Basalt.SPMF.Failure

/-!
# Generator Correctness Classes

The classes in this file encode the basic, mostly orthogonal, correctness properties that we expect
of an optimal PBT generator.

## Main Definitions

- `IsSoundAndComplete` — We expect that generators are sound and complete with respect to some
  validity predicate. A sound and complete generator is guaranteed not to miss important cases
  (complete) and also guaranteed not to need filtering (sound).
- `IsAlmostSurelyTerminating` — We expect that generators terminate with probability 1. Critically,
  this is different from being structurally terminating by Lean standards --- indeed, many
  generators will not be structurally terminating. Instead, we require that any infinite paths
  through the generator have probability 0.
- `IsCostBounded` — We expect that a generator makes a bounded number of choices while producing a
  given value. For example, we may expect that a generator for BSTs makes roughly `t.size` choices
  to produce a tree `t`.
- `LawfulGenerator` — A generator that is all of the above is _lawful_.
-/

/-- We say that a generator `g` `IsSoundAndComplete` with respect to a predicate `P` if, when
  interpreted as an `SPMF`, all values in the support of `g` satisfy `P` and all values satisfying
  `P` are in the support of `g`. -/
class IsSoundAndComplete (g : SPMF α) (P : α → Prop) where
  support_iff : a ∈ SPMF.support g ↔ P a

/-- We say that a generator `g` `IsAlmostSurelyTerminating` if, when
  interpreted as an `SPMF`, its mass sums to 1 (i.e., it is a true `PMF`). -/
class IsAlmostSurelyTerminating (g : SPMF α) where
  is_pmf : SPMF.IsPMF g

/-- We say that a generator `g` `IsCostBounded` with respect to a cost function `c` if, when
  generating a value `v`, the generator makes at most `c v` choices. -/
class IsCostBounded (g : SPMF.Cost α) (c : α → Nat) where
  is_bounded : IsBounded g c

class LawfulGenerator (g : ∀ {G : Type → Type} [Gen G], G α) (P : α → Prop) (c : α → Nat) extends IsSoundAndComplete g P, IsAlmostSurelyTerminating g, IsCostBounded g c

/-- A partial generator `IsFilterFree` if all of its mass lands on *successful* outcomes: it never
  actually fails.  -/
class IsFilterFree (g : SPMF (Option α)) where
  filter_free : SPMF.massSome g = 1

/-- A partial generator `IsProductive` if it succeeds with positive probability.  Proving this shows
  that rejection sampling is safe. -/
class IsProductive (g : SPMF (Option α)) where
  productive : 0 < SPMF.massSome g
