/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/

/-!
# Tuning: runtime-addressable generator weights

A generator's branch weights live in `frequency` calls. `@[tunable]` (see `Basalt.Tuning.Attr`)
collects those sites and threads a `Tuning` — an ordinary runtime value — through the generator, so
a different weighting is a function call away instead of an edit-and-recompile away.

Weights are schedules in the recursion depth `d`: an affine `(a, b)` pair denotes
`w(d) = max a 1 + b·d`, and a constant weight is `(a, 0)`.  Depth-indexing is what lets a generator
be exploratory near the root and subcritical deep in the recursion.

## Ensuring Positivity

`Tuning.weight` clamps every branch to a weight of at least 1, so a runtime `θ` can never zero one
out. To prune a branch, the user must remove it from the `frequency`.
-/

/-- A weight schedule per branch: entry `(aⱼ, bⱼ)` denotes the depth-indexed weight
`wⱼ(d) = max aⱼ 1 + bⱼ · d`; a constant weight is `(a, 0)`. The schedules of all sites of one
generator are concatenated into this one flat array; each `Site.offset` says where its block starts.
-/
structure Tuning where
  schedules : Array (Nat × Nat)
  deriving Repr, DecidableEq, Inhabited

/-- Metadata for one `frequency` site collected by `@[tunable]`. -/
structure Site where
  /-- A stable label for the site, for diagnostics and reviewable artifacts: the enclosing
  definition's name plus a positional suffix, in outside-in traversal order. -/
  name   : Lean.Name
  /-- Index into `Tuning.schedules` of this site's first branch. -/
  offset : Nat
  /-- Number of branches at this site. -/
  arity  : Nat
  /-- Number of recursive calls made by each branch. -/
  holes  : Array Nat
  deriving Repr, DecidableEq, Inhabited

/-- The weight of the branch whose schedule lives at flat index `i` (that is, `Site.offset + j` for
  branch `j` of a site), at recursion depth `d`.  `@[tunable]` emits the flat index as a literal,
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

/-- `frequency`'s side condition, for a branch list whose head weight is a `Tuning` read.  One
  positive summand is enough, and `Tuning.weight` is positive unconditionally, so this discharges the
  obligation for *every* `θ` — which is what `@[tunable]` needs, since it rewrites the weights before
  any `θ` exists.  Stated on `List.sum (List.map Prod.fst …)` so it matches `frequency`'s autoParam
  goal syntactically. -/
theorem Tuning.sum_map_fst_pos {β : Type u} (θ : Tuning) (i d : Nat) (g : β)
    (tl : List (Nat × β)) :
    0 < List.sum (List.map Prod.fst ((θ.weight i d, g) :: tl)) := by
  simp only [List.map_cons, List.sum_cons]
  have := Tuning.weight_pos θ i d
  omega
