/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/

/-!
# Tuning: runtime-addressable generator weights

A generator's branch weights live in `frequency` calls. `tunable def` (see `Basalt.Tuning.Macro`)
collects those sites and threads a `Tuning` — an ordinary runtime value — through the generator, so
a different weighting is a function call away instead of an edit-and-recompile away.

Weights are schedules in the recursion depth `d`: an affine `(a, b)` pair denotes `w(d) = a + b·d`,
and a constant weight is `(a, 0)`.  Depth-indexing is what lets a generator be exploratory near the
root and subcritical deep in the recursion.

## Ensuring Positivity

`Tuning.weight` weights so all branches have at least 1 weight. To prune a branch, the user must
remove it from the `frequency`.
-/

/-- A weight schedule per branch: entry `(aⱼ, bⱼ)` denotes the depth-indexed weight
  `wⱼ(d) = max aⱼ 1 + bⱼ · d`; a constant weight is `(a, 0)`. The schedules of all sites of one
  generator are concatenated into this one flat array; each `Site.offset` says where its block
  starts.  -/
structure Tuning where
  schedules : Array (Nat × Nat)
  deriving Repr, DecidableEq, Inhabited

/-- Metadata for one `frequency` site collected by `tunable def`. -/
structure Site where
  /-- A stable label for the site, for diagnostics and reviewable artifacts.  Defaults to the
    enclosing definition's name plus a positional suffix; override with `frequency (site := `myName)
    […]`. -/
  name   : Lean.Name
  /-- Index into `Tuning.schedules` of this site's first branch. -/
  offset : Nat
  /-- Number of branches at this site. -/
  arity  : Nat
  /-- Number of recursive calls made by each branch. -/
  holes  : Array Nat
  deriving Repr, DecidableEq, Inhabited

/-- The weight of the branch whose schedule lives at flat index `i` (that is, `Site.offset + j` for
  branch `j` of a site), at recursion depth `d`.  `tunable def` emits the flat index as a literal,
  so terms and proof goals stay small; `Site` carries the structure for diagnostics.  -/
def Tuning.weight (θ : Tuning) (i : Nat) (d : Nat) : Nat :=
  let p := θ.schedules.getD i (1, 0)
  max p.1 1 + d * p.2

/-- Every weight is positive — for every `θ`, index, and depth. This is what discharges
  `frequency`'s side condition with no precondition on `θ`. -/
theorem Tuning.weight_pos (θ : Tuning) (i d : Nat) :
    0 < θ.weight i d := by
  simp only [Tuning.weight]
  omega
