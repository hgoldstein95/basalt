/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
module

public import Basalt
public import BasaltExamples.AllTwoTree
meta import BasaltExamples.AllTwoTree
public import BasaltExamples.BST
public import BasaltExamples.BST.Weighted
meta import BasaltExamples.BST.Weighted
public import BasaltExamples.STLC.Rejection
meta import BasaltExamples.STLC.Rejection

/-!
# `#genstats` Examples

`#genstats` draws from a generator and summarizes its distribution.
-/

@[expose] public section

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
(`AllTwoTree.genWeightedTree.expected_cost_bounded`), and the measured mean below is 2.9 — against
`genTree`'s fueled mean of 75.4 with a 9851-node maximum above. The size function counts
constructors (`2 * size + 1` for a binary tree).
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
info: STLC.genTerm [] .Bool — 1000 draws (seed 0, fuel 10000)

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
#genstats STLC.genTerm [] .Bool

/--
info: STLC.genTermSized 5 [] .Bool — 1000 draws (seed 0, fuel 10000)

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
#genstats STLC.genTermSized 5 [] .Bool

/-
`genTerm` at closed functions on `Bool`, at three fuel limits: its mean size and mean choices grow
with the fuel, as a generator with no finite expected cost (`genTerm.not_expected_cost_bounded`,
`STLC/Cost.lean`) must. `genTermSized` beside it, whose choices are bounded
(`genTermSized.cost_bounded`, `STLC/GenTermSized.lean`).
-/
/--
info: STLC.genTerm [] (.Fun .Bool .Bool) — 1000 draws (seed 0, fuel 1000)

  outcomes    ok 943 (94.3%)   fuel-exhausted 57 (5.7%)
  size        mean 8.8   p50 2   p95 38   max 157
  choices     mean 45.9   p50 3   p95 284   max 951
  distinct    308 / 943

  head constructor
    Abs    67.4%  (636)
    App    32.6%  (307)

  most common
     27.6%  (260)  λ:Bool. false
     23.5%  (222)  λ:Bool. true
      8.1%   (76)  λ:Bool. #0
      1.9%   (18)  (λ:Bool. λ:Bool. false) true
      1.6%   (15)  (λ:Bool. λ:Bool. true) false

  samples
    λ:Bool. true
    λ:Bool. false
    λ:Bool. true
-/
#guard_msgs in
#genstats (fuel := 1000) STLC.genTerm [] (.Fun .Bool .Bool)

/--
info: STLC.genTerm [] (.Fun .Bool .Bool) — 1000 draws (seed 0, fuel 100000)

  outcomes    ok 992 (99.2%)   fuel-exhausted 8 (0.8%)
  size        mean 12.6   p50 2   p95 53   max 461
  choices     mean 699.9   p50 3   p95 936   max 97953
  distinct    357 / 992

  head constructor
    Abs    64.8%  (643)
    App    35.2%  (349)

  most common
     26.2%  (260)  λ:Bool. false
     22.4%  (222)  λ:Bool. true
      7.7%   (76)  λ:Bool. #0
      1.8%   (18)  (λ:Bool. λ:Bool. false) true
      1.5%   (15)  (λ:Bool. λ:Bool. true) false

  samples
    λ:Bool. true
    λ:Bool. false
    λ:Bool. true
-/
#guard_msgs in
#genstats (fuel := 100000) STLC.genTerm [] (.Fun .Bool .Bool)

/--
info: STLC.genTerm [] (.Fun .Bool .Bool) — 1000 draws (seed 0, fuel 1000000)

  outcomes    ok 997 (99.7%)   fuel-exhausted 3 (0.3%)
  size        mean 13.2   p50 2   p95 57   max 461
  choices     mean 1323.4   p50 3   p95 1137   max 173646
  distinct    362 / 997

  head constructor
    Abs    64.5%  (643)
    App    35.5%  (354)

  most common
     26.1%  (260)  λ:Bool. false
     22.3%  (222)  λ:Bool. true
      7.6%   (76)  λ:Bool. #0
      1.8%   (18)  (λ:Bool. λ:Bool. false) true
      1.5%   (15)  (λ:Bool. λ:Bool. true) false

  samples
    λ:Bool. true
    λ:Bool. false
    λ:Bool. true
-/
#guard_msgs in
#genstats (fuel := 1000000) STLC.genTerm [] (.Fun .Bool .Bool)

/--
info: STLC.genTermSized 5 [] (.Fun .Bool .Bool) — 1000 draws (seed 0, fuel 10000)

  outcomes    ok 1000 (100.0%)
  size        mean 35.2   p50 35   p95 70   max 89
  choices     mean 31.7   p50 32   p95 58   max 68
  distinct    866 / 1000

  head constructor
    App    66.3%  (663)
    Abs    33.7%  (337)

  most common
      7.9%  (79)  λ:Bool. #0
      3.1%  (31)  λ:Bool. true
      1.8%  (18)  λ:Bool. false
      0.5%   (5)  λ:Bool. (λ:Bool. #1) #0
      0.3%   (3)  (λ:Bool. λ:Bool. true) false

  samples
    λ:Bool. (λ:Bool. (λ:Bool. λ:Bool. #1) #0) #0 ((λ:Bool. λ:Bool. λ:Bool → Bool. #1) #0 ((λ:…
    (λ:(Bool → Bool) → Bool. (λ:Bool. (λ:Bool. λ:Bool. #2) #0) ((λ:Bool. #0) ((λ:Bool. #0) tr…
    (λ:(Bool → Bool) → Bool. λ:Bool. false) (λ:Bool → Bool. (λ:Bool. λ:Bool → Bool. #1) (#0 f…
-/
#guard_msgs in
#genstats STLC.genTermSized 5 [] (.Fun .Bool .Bool)

/-- The loop of `suchThat`, returning how many draws it took instead of the value it accepted. -/
def attempts [Gen G] (g : G α) (p : α → Bool) : G Nat := do
  let a ← g
  if p a then return 1 else
    let k ← attempts g p
    return k + 1
partial_fixpoint

/-
How many draws `genTermSizedNontrivial` and `genTermSizedUseful` (`STLC/Rejection.lean`) take at
closed functions on `Bool`: the mean is read off the counts, `1.0476` and `1.0519`. The first is
exactly `21/20` in expectation (`genTermSized.prob_trivial_closed_fun`); the second is at most
`21/16` (`genTermSized.prob_useless_le`).
-/
/--
info: attempts (STLC.genTermSized 5 [] (.Fun .Bool .Bool)) (!·.isTrivial) — 10000 draws (seed 0, fuel 10000)

  outcomes    ok 10000 (100.0%)
  size        mean 1.0   p50 1   p95 1   max 3
  choices     mean 33.3   p50 34   p95 60   max 73
  distinct    3 / 10000

  head constructor
    succ   100.0%  (10000)

  most common
     95.4%  (9537)  1
      4.5%   (450)  2
      0.1%    (13)  3

  samples
    1
    1
    1
-/
#guard_msgs in
#genstats (draws := 10000) (size := id) attempts (STLC.genTermSized 5 [] (.Fun .Bool .Bool))
  (!·.isTrivial)

/--
info: attempts (STLC.genTermSized 5 [] (.Fun .Bool .Bool)) (!·.isUselessAbs) — 10000 draws (seed 0, fuel 10000)

  outcomes    ok 10000 (100.0%)
  size        mean 1.1   p50 1   p95 2   max 3
  choices     mean 33.4   p50 34   p95 60   max 77
  distinct    3 / 10000

  head constructor
    succ   100.0%  (10000)

  most common
     95.0%  (9496)  1
      4.9%   (489)  2
      0.2%    (15)  3

  samples
    1
    1
    1
-/
#guard_msgs in
#genstats (draws := 10000) (size := id) attempts (STLC.genTermSized 5 [] (.Fun .Bool .Bool))
  (!·.isUselessAbs)

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
