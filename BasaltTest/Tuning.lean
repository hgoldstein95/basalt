/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/

import Basalt
import Basalt.Combinators
import BasaltExamples.BST
import BasaltExamples.BST.Weighted

open RandomChoice

/-!
# `tunable def` Examples

`Tree.genWeightedBST` (`BasaltExamples/BST.lean`) is declared `tunable`, so the
macro emitted `Tree.genWeightedBST.tuned/.defaults/.sites/.tuned_defaults`
alongside it. This file exercises the whole contract:

1. `genWeightedBST.tuned genWeightedBST.defaults` and `genWeightedBST` are
   interchangeable — `tuned_defaults` is definitional, and `BST.lean`'s
   existing proofs compile unchanged.
2. Two `Tuning`s can be compared in the same file with no recompilation
   between them, and the distributions differ.
3. A schedule with a nonzero depth coefficient produces a depth-varying
   distribution.
4. `sites` reports each site's offset, arity, and per-branch recursive calls.
5. A literal `0` weight is rejected at elaboration.
-/

namespace TunableExamples
open BST

/-! ## 1. The defaults are the generator as written -/

/-- `tuned_defaults` is proved by the macro — definitionally. -/
example [Gen G] (lo hi : Nat) :
    (Tree.genWeightedBST.tuned Tree.genWeightedBST.defaults lo hi : G (BST.Tree Nat)) =
      Tree.genWeightedBST lo hi :=
  Tree.genWeightedBST.tuned_defaults lo hi

/-- Facts about the untuned generator transfer to the default-tuned form by
    rewriting — adopting tuning does not change existing proofs. -/
example (lo hi : Nat) (t : BST.Tree Nat) :
    t ∈ SPMF.support (Tree.genWeightedBST.tuned Tree.genWeightedBST.defaults lo hi) ↔
      t ∈ SPMF.support (Tree.genWeightedBST lo hi) := by
  rw [Tree.genWeightedBST.tuned_defaults]

/-! ## 4. The site table -/

/--
info: #[{ name := `Tree.genWeightedBST.site0, offset := 0, arity := 2, holes := #[0, 2] }]
-/
#guard_msgs in
#eval Tree.genWeightedBST.sites

/-- `defaults` is the weights record with every field at its source weight (the record `{}`); its
fields are named after the constructors (`leaf`, `node`). -/
example : Tree.genWeightedBST.defaults = { leaf := (1, 0), node := (5, 0) } := rfl

/-- …and it flattens to the source `Tuning`. -/
example : Tree.genWeightedBST.defaults.toTuning = ⟨#[(1, 0), (5, 0)]⟩ := rfl

/-! ## 4a. Weights by constructor name

The macro emits a `genFoo.Weights` record with one field per `frequency` branch,
named after the constructor that branch produces. A caller sets weights by name
— no need to recall the constructor order — and unset fields keep their source
weight, so `{ node := … }` reweights `node` alone. -/

/-- Overriding one field leaves the other at its source weight. -/
example : ({ node := (2, 0) } : Tree.genWeightedBST.Weights)
    = { leaf := (1, 0), node := (2, 0) } := rfl

/-- A named override flattens to the expected `Tuning`. -/
example : ({ node := (2, 0) } : Tree.genWeightedBST.Weights).toTuning
    = ⟨#[(1, 0), (2, 0)]⟩ := rfl

/-- A weighting held as a flat `Tuning` still drives `.tuned`: `Tuning` coerces to
the weights record (field `i` reads schedule entry `i`), so nothing that used the
old positional API breaks. -/
example : ((⟨#[(5, 0), (1, 0)]⟩ : Tuning) : Tree.genWeightedBST.Weights)
    = { leaf := (5, 0), node := (1, 0) } := rfl

/-! ## 2. Two weightings, one compiled generator, one file

`θ` is an ordinary runtime value: evaluating a new candidate weighting is a
function call, not an edit-and-recompile. Weights are named by constructor, so
flipping leaf/node from 1:5 to 5:1 is `{ leaf := (5, 0), node := (1, 0) }` — no
need to recall the constructor order. The distribution collapses toward leaves
(compare `p50` and the head-constructor split). -/

/--
info: Tree.genWeightedBST.tuned { leaf := (1, 0), node := (5, 0) } 0 10 — 200 draws (seed 0, fuel 10000)

  outcomes    ok 200 (100.0%)
  size        mean 18.2   p50 17   p95 43   max 87
  choices     mean 19.0   p50 19   p95 45   max 87
  distinct    161 / 200

  head constructor
    node    82.0%  (164)
    leaf    18.0%   (36)

  most common
     18.0%  (36)  BST.Tree.leaf
      1.0%   (2)  BST.Tree.node (BST.Tree.leaf) 3 (BST.Tree.leaf)
      1.0%   (2)  BST.Tree.node (BST.Tree.leaf) 9 (BST.Tree.node (BST.Tree.leaf) 10 (BST.Tree.leaf))
      1.0%   (2)  BST.Tree.node (BST.Tree.node (BST.Tree.node (BST.Tree.leaf) 0 (BST.Tree.leaf)) 0 (BST.Tre…
      1.0%   (2)  BST.Tree.node (BST.Tree.node (BST.Tree.node (BST.Tree.node (BST.Tree.leaf) 0 (BST.Tree.le…

  samples
    BST.Tree.node (BST.Tree.node (BST.Tree.leaf) 0 (BST.Tree.node (BST.Tree.node (BST.Tree.no…
    BST.Tree.leaf
    BST.Tree.leaf
-/
#guard_msgs in
#genstats (draws := 200) Tree.genWeightedBST.tuned { leaf := (1, 0), node := (5, 0) } 0 10

/--
info: Tree.genWeightedBST.tuned { leaf := (5, 0), node := (1, 0) } 0 10 — 200 draws (seed 0, fuel 10000)

  outcomes    ok 200 (100.0%)
  size        mean 1.5   p50 1   p95 3   max 7
  choices     mean 1.6   p50 1   p95 4   max 9
  distinct    20 / 200

  head constructor
    leaf    84.0%  (168)
    node    16.0%   (32)

  most common
     84.0%  (168)  BST.Tree.leaf
      4.0%    (8)  BST.Tree.node (BST.Tree.leaf) 3 (BST.Tree.leaf)
      1.5%    (3)  BST.Tree.node (BST.Tree.leaf) 8 (BST.Tree.leaf)
      1.0%    (2)  BST.Tree.node (BST.Tree.leaf) 0 (BST.Tree.leaf)
      1.0%    (2)  BST.Tree.node (BST.Tree.leaf) 1 (BST.Tree.leaf)

  samples
    BST.Tree.node (BST.Tree.leaf) 10 (BST.Tree.leaf)
    BST.Tree.leaf
    BST.Tree.leaf
-/
#guard_msgs in
#genstats (draws := 200) Tree.genWeightedBST.tuned { leaf := (5, 0), node := (1, 0) } 0 10

/-! ## 3. Depth-indexed schedules

A generator with an explicit `depth` binder reads each site's weights at that
depth, so a nonzero growth coefficient `b` makes the distribution
depth-varying. Decay is expressed as base-weight *growth*: the leaf branch's
weight grows with depth (`w(d) = 1 + 8·d`), the
node branch's stays constant, so recursion is likely at the root and is forced
closed a few levels down — never forbidden, so the support is unchanged. -/

tunable def genTree [Gen G] (depth : Nat) : G (BST.Tree Nat) :=
  frequency (site := `genTree.spine) [
    (1, fun _ => pure .leaf),
    (2, fun _ => do
      let l ← genTree (depth + 1)
      let r ← genTree (depth + 1)
      return .node l 0 r)
  ] (by simp)
partial_fixpoint

/-- The site override names the site; one site, holes `#[0, 2]`. -/
example : genTree.sites = #[⟨`genTree.spine, 0, 2, #[0, 2]⟩] := rfl

/-- `tuned_defaults` is definitional for depth-threaded generators too. -/
example [Gen G] (depth : Nat) :
    (genTree.tuned genTree.defaults depth : G (BST.Tree Nat)) = genTree depth :=
  genTree.tuned_defaults depth

/-- With constant weights 1:2 the mean offspring is `2·(2/3) = 4/3 > 1` — the
    generator is *supercritical* and most draws exhaust the fuel budget. Weights
    are given by constructor name, as a `genTree.Weights` record. -/
def constantTuning : genTree.Weights := { leaf := (1, 0), node := (2, 0) }

/-- Same base weights, but the leaf weight grows by 8 per level of depth:
    `w_leaf(d) = 1 + 8·d`, `w_node(d) = 2`. Supercritical at the root, forced
    subcritical by depth 1. -/
def decayingTuning : genTree.Weights := { leaf := (1, 8), node := (2, 0) }

/--
info: genTree.tuned constantTuning 0 — 200 draws (seed 0, fuel 10000)

  outcomes    ok 98 (49.0%)   fuel-exhausted 102 (51.0%)
  size        mean 3.0   p50 1   p95 13   max 19
  choices     mean 3.0   p50 1   p95 13   max 19
  distinct    16 / 98

  head constructor
    leaf    63.3%  (62)
    node    36.7%  (36)

  most common
     63.3%  (62)  BST.Tree.leaf
     19.4%  (19)  BST.Tree.node (BST.Tree.leaf) 0 (BST.Tree.leaf)
      4.1%   (4)  BST.Tree.node (BST.Tree.leaf) 0 (BST.Tree.node (BST.Tree.leaf) 0 (BST.Tree.leaf))

  samples
    BST.Tree.leaf
    BST.Tree.leaf
    BST.Tree.leaf
-/
#guard_msgs in
#genstats (draws := 200) genTree.tuned constantTuning 0

/--
info: genTree.tuned decayingTuning 0 — 200 draws (seed 0, fuel 10000)

  outcomes    ok 200 (100.0%)
  size        mean 3.0   p50 3   p95 7   max 11
  choices     mean 3.0   p50 3   p95 7   max 11
  distinct    10 / 200

  head constructor
    node    69.0%  (138)
    leaf    31.0%   (62)

  most common
     46.0%  (92)  BST.Tree.node (BST.Tree.leaf) 0 (BST.Tree.leaf)
     31.0%  (62)  BST.Tree.leaf
      9.5%  (19)  BST.Tree.node (BST.Tree.leaf) 0 (BST.Tree.node (BST.Tree.leaf) 0 (BST.Tree.leaf))
      7.0%  (14)  BST.Tree.node (BST.Tree.node (BST.Tree.leaf) 0 (BST.Tree.leaf)) 0 (BST.Tree.leaf)
      2.5%   (5)  BST.Tree.node (BST.Tree.node (BST.Tree.node (BST.Tree.leaf) 0 (BST.Tree.leaf)) 0 (BST.Tre…

  samples
    BST.Tree.node (BST.Tree.node (BST.Tree.leaf) 0 (BST.Tree.node (BST.Tree.leaf) 0 (BST.Tree…
    BST.Tree.leaf
    BST.Tree.leaf
-/
#guard_msgs in
#genstats (draws := 200) genTree.tuned decayingTuning 0

/-! ## 5. A zero weight is rejected at elaboration -/

/--
error: tunable def: a literal weight of 0 is rejected: a zero weight removes its branch from the generator's support (see `SPMF.support_frequency`), breaking support-completeness (`IsSoundAndComplete`). To prune a branch, remove it from the source instead.
-/
#guard_msgs in
tunable def genZero [Gen G] : G Nat := do
  frequency [
    (0, fun _ => pure 0),
    (1, fun _ => pure 1)
  ] (by simp)

/-! Zero entries in a *runtime* `θ` cannot break support either: they read as
weight `1` (`Tuning.weight` clamps), so the generator is total in `θ`. -/

/-- A `θ` of all zeros reads as all-ones (uniform), not as an empty support:
    same distribution as `⟨#[(1, 0), (1, 0)]⟩`. -/
example (depth d : Nat) :
    Tuning.weight ⟨#[(0, 0), (0, 0)]⟩ d depth = Tuning.weight ⟨#[(1, 0), (1, 0)]⟩ d depth := by
  simp [Tuning.weight]
  rcases d with _ | _ | d <;> simp

end TunableExamples

section ReweightObligation

variable {α : Type}

-- Reweighting a uniform choice: `oneOf` to `frequency`, the shape `derive_tuning` rewrites.
example (gs : List (Unit → SPMF α)) (gs' : List (Nat × (Unit → SPMF α)))
    (hsnd : gs'.map Prod.snd = gs) (hpos : ∀ p ∈ gs', 0 < p.1)
    (hne : gs ≠ []) (h' : 0 < List.sum (List.map Prod.fst gs')) :
    SPMF.support (frequency gs' h') = SPMF.support (oneOf gs hne) :=
  SPMF.support_frequency_reweight hsnd hpos hne h'

-- Changing weights in place: `frequency` to `frequency`, the shape `tunable def` rewrites.
example (gs gs' : List (Nat × (Unit → SPMF α)))
    (hsnd : gs'.map Prod.snd = gs.map Prod.snd)
    (hpos : ∀ p ∈ gs', 0 < p.1) (hpos' : ∀ p ∈ gs, 0 < p.1)
    (h : 0 < List.sum (List.map Prod.fst gs)) (h' : 0 < List.sum (List.map Prod.fst gs')) :
    SPMF.support (frequency gs' h') = SPMF.support (frequency gs h) :=
  SPMF.support_frequency_congr_weights hsnd hpos hpos' h h'

-- `Tuning.weight` satisfies the positivity hypothesis unconditionally, for every `θ` and depth —
-- there is no tuning a user can supply that fails it.
example (θ : Tuning) (i d : Nat) : 0 < θ.weight i d := Tuning.weight_pos θ i d

-- And given a `tuned_support`, the law transfers in one application. This is
-- `genFoo.tuned_sound_complete`, on whichever side emits it.
example {g g' : SPMF α} {P : α → Prop}
    (tuned_support : SPMF.support g' = SPMF.support g) (sound_complete : IsSoundAndComplete g P) :
    IsSoundAndComplete g' P :=
  IsSoundAndComplete.of_support_eq tuned_support sound_complete

end ReweightObligation
