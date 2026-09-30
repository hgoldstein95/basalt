/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt
import BasaltExamples.AllTwoTree
import BasaltExamples.BST
import BasaltExamples.BST.Weighted
import BasaltExamples.STLC.GenTermSized

/-!
# `#genstats` Examples

`#genstats` draws from a generator and summarizes its distribution
-/

open RandomChoice

namespace GenStatsExamples

/--
info: BST.Tree.genBST 0 10 — 200 draws (seed 0, fuel 10000)

  outcomes    ok 200 (100.0%)
  size        mean 3.9   p50 1   p95 13   max 21
  choices     mean 4.4   p50 1   p95 15   max 21
  distinct    78 / 200

  head constructor
    leaf    54.0%  (108)
    node    46.0%   (92)

  most common
     54.0%  (108)  BST.Tree.leaf
      2.0%    (4)  BST.Tree.node (BST.Tree.leaf) 10 (BST.Tree.leaf)
      1.5%    (3)  BST.Tree.node (BST.Tree.leaf) 3 (BST.Tree.leaf)
      1.5%    (3)  BST.Tree.node (BST.Tree.leaf) 5 (BST.Tree.leaf)
      1.0%    (2)  BST.Tree.node (BST.Tree.leaf) 0 (BST.Tree.leaf)

  samples
    BST.Tree.node (BST.Tree.leaf) 10 (BST.Tree.leaf)
    BST.Tree.leaf
    BST.Tree.leaf
-/
#guard_msgs in
#genstats (draws := 200) BST.Tree.genBST 0 10

/--
info: BST.Tree.genWeightedBST 0 10 — 200 draws (seed 0, fuel 10000)

  outcomes    ok 200 (100.0%)
  size        mean 5.8   p50 7   p95 11   max 11
  choices     mean 12.8   p50 15   p95 22   max 22
  distinct    160 / 200

  head constructor
    node    82.0%  (164)
    leaf    18.0%   (36)

  most common
     18.0%  (36)  BST.Tree.leaf
      1.0%   (2)  BST.Tree.node (BST.Tree.leaf) 3 (BST.Tree.leaf)
      1.0%   (2)  BST.Tree.node (BST.Tree.leaf) 9 (BST.Tree.node (BST.Tree.leaf) 10 (BST.Tree.leaf))
      1.0%   (2)  BST.Tree.node (BST.Tree.node (BST.Tree.leaf) 0 (BST.Tree.leaf)) 1 (BST.Tree.leaf)
      1.0%   (2)  BST.Tree.node (BST.Tree.node (BST.Tree.leaf) 0 (BST.Tree.node (BST.Tree.leaf) 1 (BST.Tree…

  samples
    BST.Tree.node (BST.Tree.node (BST.Tree.leaf) 0 (BST.Tree.leaf)) 10 (BST.Tree.leaf)
    BST.Tree.leaf
    BST.Tree.leaf
-/
#guard_msgs in
#genstats (draws := 200) (size := BST.Tree.size) BST.Tree.genWeightedBST 0 10

/--
info: AllTwoTree.genTree — 1000 draws (seed 0, fuel 10000)

  outcomes    ok 995 (99.5%)   fuel-exhausted 5 (0.5%)
  size        mean 75.4   p50 1   p95 161   max 9851
  choices     mean 75.4   p50 1   p95 161   max 9851

  head constructor
    leaf    50.6%  (503)
    node    49.4%  (492)
-/
#guard_msgs in
#genstats AllTwoTree.genTree

/-
The subcritical variant (`m = 2/3`) makes at most `3` choices on average, one per constructor
(`AllTwoTree.genWeightedTree.cost`), and the measured mean below is 2.9 — against `genTree`'s fueled
mean of 75.4 with a 9851-node maximum above. The size function counts constructors
(`2 * size + 1` for a binary tree).
-/
/--
info: AllTwoTree.genWeightedTree — 200 draws (seed 0, fuel 10000)

  outcomes    ok 200 (100.0%)
  size        mean 2.9   p50 1   p95 11   max 37
  choices     mean 2.9   p50 1   p95 11   max 37

  head constructor
    leaf    65.5%  (131)
    node    34.5%   (69)
-/
#guard_msgs in
#genstats (draws := 200) (size := fun t => 2 * t.size + 1) AllTwoTree.genWeightedTree

/-
The two STLC generators: `Bool`'s share of each head-constructor split below is the probability
of a literal that `genTerm.prob_trivial_bool` and `genTermSized.prob_trivial_bool`
(`STLC/Distribution.lean`) state, and `genTermSized.cost_bounded` is the bound on its choices.
-/
/--
info: genTerm [] Ty.Bool — 1000 draws (seed 0, fuel 10000)

  outcomes    ok 979 (97.9%)   fuel-exhausted 21 (2.1%)
  size        mean 7.9   p50 1   p95 38   max 207
  choices     mean 140.1   p50 2   p95 477   max 9329
  distinct    261 / 979

  head constructor
    Bool    65.7%  (643)
    App     34.3%  (336)

  most common
     34.1%  (334)  false
     31.6%  (309)  true
      1.7%   (17)  (λ:Bool. false) true
      1.7%   (17)  (λ:Bool. true) true
      1.3%   (13)  (λ:Bool. true) false

  samples
    false
    false
    true
-/
#guard_msgs in
#genstats genTerm [] Ty.Bool

/--
info: genTermSized 5 [] Ty.Bool — 1000 draws (seed 0, fuel 10000)

  outcomes    ok 1000 (100.0%)
  size        mean 35.0   p50 38   p95 71   max 89
  choices     mean 32.1   p50 36   p95 59   max 68
  distinct    789 / 1000

  head constructor
    App     79.5%  (795)
    Bool    20.5%  (205)

  most common
     11.2%  (112)  false
      9.3%   (93)  true
      0.6%    (6)  (λ:Bool. #0) true
      0.3%    (3)  (λ:Bool. #0) false
      0.2%    (2)  (λ:Bool. true) false

  samples
    (λ:Bool. (λ:Bool. false) #0) ((λ:Bool. #0) true)
    false
    (λ:(Bool → Bool) → Bool. false) ((λ:Bool. λ:Bool → Bool. λ:Bool → Bool. λ:Bool → Bool. #3…
-/
#guard_msgs in
#genstats genTermSized 5 [] Ty.Bool

def genDiverge [Gen G] : G Nat := do
  let _ ← choose 0 1 (by omega)
  genDiverge
partial_fixpoint

/--
info: genDiverge — 50 draws (seed 0, fuel 100)

  outcomes    ok 0 (0.0%)   fuel-exhausted 50 (100.0%)
  size        (no data)
  choices     (no data)
-/
#guard_msgs in
#genstats (draws := 50) (fuel := 100) genDiverge

end GenStatsExamples
