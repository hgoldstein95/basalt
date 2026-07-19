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
# Generator Correctness Properties

The definitions in this file encode basic, mostly orthogonal, correctness properties that a PBT
generator may have. Which of them apply depends on the generator.

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
-/

/-- We say that a generator `g` `IsSoundAndComplete` with respect to a predicate `P` if, when
  interpreted as an `SPMF`, all values in the support of `g` satisfy `P` and all values satisfying
  `P` are in the support of `g`. -/
def IsSoundAndComplete (g : SPMF α) (P : α → Prop) : Prop :=
  ∀ a, a ∈ SPMF.support g ↔ P a

/-- We say that a generator `g` `IsAlmostSurelyTerminating` if, when
  interpreted as an `SPMF`, its mass sums to 1 (i.e., it is a true `PMF`). -/
def IsAlmostSurelyTerminating (g : SPMF α) : Prop :=
  SPMF.IsPMF g

/-- We say that a generator `g` `IsCostBounded` with respect to a cost function `c` if, when
  generating a value `v`, the generator makes at most `c v` choices. -/
def IsCostBounded (g : SPMF.Cost α) (c : α → Nat) : Prop :=
  IsBounded g c

/-- A partial generator `IsFilterFree` if all of its mass lands on *successful* outcomes: it never
  actually fails.  -/
def IsFilterFree (g : SPMF (Option α)) : Prop :=
  SPMF.massSome g = 1

/-- A partial generator `IsProductive` if it succeeds with positive probability.  Proving this shows
  that rejection sampling is safe. -/
def IsProductive (g : SPMF (Option α)) : Prop :=
  0 < SPMF.massSome g
