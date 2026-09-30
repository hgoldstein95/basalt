/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Segev Elazar Mittelman
-/
import Basalt

/-!
# Graded Enumeration

One enumeration of binary trees, at every interpretation: `Cnt` counts what `Lv` produces, and the three
carriers to run (`LvT`, `LvL`, `LvC` at several chunk sizes) produce `Lv`'s levels in `Lv`'s order. The
agreement proofs are pinned free of `Classical.choice`, which `LvT.build`'s construction exists to keep.
-/

open Basalt

namespace GradedTest

inductive Tree where
  | leaf
  | node (l r : Tree)
  deriving Repr, DecidableEq

/-- A binary tree: a leaf at level 0, and a node costing one level over its convolved children. -/
def treeStep [Graded f] (rec : f Tree) : f Tree :=
  Choice.union (Graded.single .leaf)
    (Graded.pay (Graded.gmap (fun p => Tree.node p.1 p.2) (Graded.pair rec rec)))

def treesLv : Lv Tree := gradedIter treeStep 7
def treesCnt : Cnt Tree := gradedIter treeStep 7

def treesT (N : Nat) : Nat → LvT Tree
  | 0 => LvT.nothing N
  | k + 1 => LvT.union (LvT.single N .leaf)
      (LvT.pay (LvT.gmap (fun p => Tree.node p.1 p.2) (LvT.pair (treesT N k) (treesT N k))))

def treesL (N : Nat) : Nat → LvL Tree
  | 0 => LvL.nothing N
  | k + 1 => LvL.union (LvL.single N .leaf)
      (LvL.pay (LvL.gmap (fun p => Tree.node p.1 p.2) (LvL.pair (treesL N k) (treesL N k))))

def treesC (C N : Nat) : Nat → LvC Tree
  | 0 => LvC.nothing N
  | k + 1 => LvC.union C (LvC.single N .leaf)
      (LvC.pay (LvC.gmap (fun p => Tree.node p.1 p.2) (LvC.pair C (treesC C N k) (treesC C N k))))

-- The Catalan numbers, from counting alone, and the same from the values.
/-- info: ([1, 1, 2, 5, 14, 42], [1, 1, 2, 5, 14, 42]) -/
#guard_msgs in
#eval ((List.range 6).map treesCnt, (List.range 6).map fun n => (treesLv n).length)

-- Each carrier to run produces `Lv`'s levels, in `Lv`'s order.
/-- info: true -/
#guard_msgs in
#eval (List.range 6).all fun n =>
  (treesT 5 7).get n == treesLv n &&
  ((treesL 5 7).get n).toList == treesLv n &&
  [1, 3, 256].all fun C => (treesC C 5 7).flat n == treesLv n

-- A lazy read of whole chunks is a prefix of the level.
/-- info: true -/
#guard_msgs in
#eval (LList.takeC 4 ((treesC 3 5 7).get 4)) == (treesLv 4).take 4

end GradedTest

/-- info: 'Basalt.LvT.get_build' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LvT.get_build

/-- info: 'Basalt.Agrees.bindC' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Agrees.bindC

/-- info: 'Basalt.Agree.pair' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Agree.pair

/-- info: 'Basalt.AgreeL.bindC' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms AgreeL.bindC

/-- info: 'Basalt.AgreeC.bindC' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms AgreeC.bindC
