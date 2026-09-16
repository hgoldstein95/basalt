import Basalt
import BasaltExamples.BST
import BasaltExamples.BST.Weighted
import BasaltExamples.AllTwoTree

open RandomChoice

/-!
# `#genstats` Examples

`#genstats` draws from a generator and summarizes its distribution
-/

namespace GenStatsExamples

/--
info: BST.Tree.genBST 0 10 — 200 draws (seed 0, fuel 10000)

  outcomes    ok 200 (100.0%)
  size        mean 3.8   p50 1   p95 13   max 19
  choices     mean 4.3   p50 1   p95 14   max 20
  distinct    77 / 200

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

  laws: sound_complete ✓  terminates ✓  cost_bounded ✓
        filter_free     — (not proved)
        productive      — (not proved)
-/
#guard_msgs in
#genstats (draws := 200) BST.Tree.genBST 0 10

/--
info: BST.Tree.genWeightedBST 0 10 — 200 draws (seed 0, fuel 10000)

  outcomes    ok 200 (100.0%)
  size        mean 5.7   p50 6   p95 11   max 11
  choices     mean 12.6   p50 14   p95 22   max 22
  distinct    158 / 200

  head constructor
    node    82.0%  (164)
    leaf    18.0%   (36)

  most common
     18.0%  (36)  BST.Tree.leaf
      1.5%   (3)  BST.Tree.node (BST.Tree.node (BST.Tree.leaf) 0 (BST.Tree.leaf)) 1 (BST.Tree.leaf)
      1.5%   (3)  BST.Tree.node (BST.Tree.node (BST.Tree.node (BST.Tree.leaf) 0 (BST.Tree.leaf)) 1 (BST.Tre…
      1.0%   (2)  BST.Tree.node (BST.Tree.leaf) 3 (BST.Tree.leaf)
      1.0%   (2)  BST.Tree.node (BST.Tree.leaf) 9 (BST.Tree.node (BST.Tree.leaf) 10 (BST.Tree.leaf))

  samples
    BST.Tree.node (BST.Tree.node (BST.Tree.leaf) 0 (BST.Tree.leaf)) 10 (BST.Tree.leaf)
    BST.Tree.leaf
    BST.Tree.leaf

  laws: sound_complete ✓  terminates ✓  cost_bounded ✓
        filter_free     — (not proved)
        productive      — (not proved)
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

  laws: sound_complete ✓  terminates ✓  cost_bounded ✓
        filter_free     — (not proved)
        productive      — (not proved)
-/
#guard_msgs in
#genstats AllTwoTree.genTree

/-
The subcritical variant (`m = 2/3`): the branching-process theory predicts an expected
`1/(1 - 2/3) = 3` constructors (`AllTwoTree.genWeightedTree_expectedSteps`), and the measured
mean below is 2.9 — against `genTree`'s fueled mean of 75.4 with a 9851-node maximum above.
The size function counts constructors (`2 * size + 1` for a binary tree), matching what
`LevelOp.expectedSteps` counts.
-/
/--
info: AllTwoTree.genWeightedTree — 200 draws (seed 0, fuel 10000)

  outcomes    ok 200 (100.0%)
  size        mean 2.9   p50 1   p95 11   max 37
  choices     mean 2.9   p50 1   p95 11   max 37

  head constructor
    leaf    65.5%  (131)
    node    34.5%   (69)

  laws: terminates ✓
        sound_complete  — (not proved)
        cost_bounded    — (not proved)
        filter_free     — (not proved)
        productive      — (not proved)
-/
#guard_msgs in
#genstats (draws := 200) (size := fun t => 2 * t.size + 1) AllTwoTree.genWeightedTree

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
