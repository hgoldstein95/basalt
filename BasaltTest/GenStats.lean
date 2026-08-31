import Basalt
import BasaltExamples.BST
import BasaltExamples.BST.Weighted
import BasaltExamples.AllTwoTree
import BasaltExamples.SplayTree.Unsplay

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
        filter_free         — (not proved)
        productive          — (not proved)
        productive_at_rate  — (not proved)
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
        filter_free         — (not proved)
        productive          — (not proved)
        productive_at_rate  — (not proved)
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
        filter_free         — (not proved)
        productive          — (not proved)
        productive_at_rate  — (not proved)
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
        sound_complete      — (not proved)
        cost_bounded        — (not proved)
        filter_free         — (not proved)
        productive          — (not proved)
        productive_at_rate  — (not proved)
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


/-! ## A filtering generator's acceptance rate

`SplayTree.Tree.genSpecial` is the cookbook's one generate-and-test generator, and the argument for
that choice (`BasaltExamples/SplayTree/Special.lean`, "Why this one filters") rests on rejection
being cheap and getting *cheaper* as the node budget grows. The `none`/`some` splits below are that
claim, pinned: going from the paper's medium splay bound to its large one nearly triples the
acceptance rate, because deep trees come to dominate the search trees on `n` keys while `splayBound`
grows only logarithmically. The third report is `Tree.genSpecialMixed`, whose acceptance rate is not
merely measured but proved — `productive_at_rate ✓`. -/

/--
info: (SplayTree.Tree.genSpecial 6 0 6) — 500 draws (seed 0, fuel 10000)

  outcomes    ok 500 (100.0%)
  size        mean 1.0   p50 1   p95 1   max 1
  choices     mean 9.9   p50 10   p95 19   max 19
  distinct    77 / 500

  head constructor
    none    83.4%  (417)
    some    16.6%   (83)

  most common
     83.4%  (417)  none
      1.0%    (5)  some (SplayTree.Tree.node (SplayTree.Tree.leaf) 2 (SplayTree.Tree.node (SplayTree.Tree.le…
      0.4%    (2)  some (SplayTree.Tree.node (SplayTree.Tree.leaf) 1 (SplayTree.Tree.node (SplayTree.Tree.no…
      0.4%    (2)  some (SplayTree.Tree.node (SplayTree.Tree.node (SplayTree.Tree.node (SplayTree.Tree.leaf)…
      0.4%    (2)  some (SplayTree.Tree.node (SplayTree.Tree.node (SplayTree.Tree.node (SplayTree.Tree.node …

  samples
    none
    none
    none

  laws: sound_complete ✓  terminates ✓  productive ✓
        cost_bounded        — (not proved)
        filter_free         — (not proved)
        productive_at_rate  — (not proved)
-/
#guard_msgs in
#genstats (draws := 500) (SplayTree.Tree.genSpecial 6 0 6)

/--
info: (SplayTree.Tree.genSpecial 12 0 12) — 500 draws (seed 0, fuel 10000)

  outcomes    ok 500 (100.0%)
  size        mean 1.0   p50 1   p95 1   max 1
  choices     mean 19.5   p50 19   p95 37   max 37
  distinct    234 / 500

  head constructor
    none    53.4%  (267)
    some    46.6%  (233)

  most common
     53.4%  (267)  none

  samples
    some (SplayTree.Tree.node (SplayTree.Tree.node (SplayTree.Tree.node (SplayTree.Tree.node …
    some (SplayTree.Tree.node (SplayTree.Tree.leaf) 3 (SplayTree.Tree.node (SplayTree.Tree.no…
    some (SplayTree.Tree.node (SplayTree.Tree.node (SplayTree.Tree.leaf) 1 (SplayTree.Tree.no…

  laws: sound_complete ✓  terminates ✓  productive ✓
        cost_bounded        — (not proved)
        filter_free         — (not proved)
        productive_at_rate  — (not proved)
-/
#guard_msgs in
#genstats (draws := 500) (SplayTree.Tree.genSpecial 12 0 12)

/--
info: (SplayTree.Tree.genSpecialMixed 12 0 12 (by omega)) — 500 draws (seed 0, fuel 10000)

  outcomes    ok 500 (100.0%)
  size        mean 1.0   p50 1   p95 1   max 1
  choices     mean 19.7   p50 19   p95 35   max 38
  distinct    363 / 500

  head constructor
    some    73.0%  (365)
    none    27.0%  (135)

  most common
     27.0%  (135)  none
      0.4%    (2)  some (SplayTree.Tree.node (SplayTree.Tree.leaf) 1 (SplayTree.Tree.node (SplayTree.Tree.no…
      0.4%    (2)  some (SplayTree.Tree.node (SplayTree.Tree.node (SplayTree.Tree.leaf) 0 (SplayTree.Tree.le…
      0.4%    (2)  some (SplayTree.Tree.node (SplayTree.Tree.node (SplayTree.Tree.leaf) 0 (SplayTree.Tree.le…

  samples
    some (SplayTree.Tree.node (SplayTree.Tree.leaf) 6 (SplayTree.Tree.node (SplayTree.Tree.le…
    some (SplayTree.Tree.node (SplayTree.Tree.leaf) 0 (SplayTree.Tree.node (SplayTree.Tree.no…
    some (SplayTree.Tree.node (SplayTree.Tree.node (SplayTree.Tree.node (SplayTree.Tree.leaf)…

  laws: sound_complete ✓  terminates ✓  productive ✓  productive_at_rate ✓
        cost_bounded        — (not proved)
        filter_free         — (not proved)
-/
#guard_msgs in
#genstats (draws := 500) (SplayTree.Tree.genSpecialMixed 12 0 12 (by omega))

end GenStatsExamples
