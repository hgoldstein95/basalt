/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt

/-!
# Red-Black Trees

The red-black tree type, the invariant it satisfies (search-tree ordering, black root, no red
parent of a red child, uniform black height), and Okasaki's insertion together with the `balance`
step whose firing `BasaltExamples/RedBlackTree/Special` targets.
-/

namespace RedBlackTree

inductive Color where
  | red
  | black
deriving Repr, DecidableEq

/-- A binary tree with `Int` keys and a colour at every internal node. -/
inductive RBTree where
  | leaf : RBTree
  | node : Color → RBTree → Int → RBTree → RBTree
deriving Repr, DecidableEq

namespace RBTree

/-- Leaves count as black. -/
def rootColor : RBTree → Color
  | leaf => .black
  | node c _ _ _ => c

/-- `x` occurs as a key. -/
def contains (x : Int) : RBTree → Prop
  | leaf => False
  | node _ l y r => x = y ∨ l.contains x ∨ r.contains x

/-- Search-tree ordering, with every key in `[lo, hi]`. -/
def isBST (lo hi : Int) : RBTree → Prop
  | leaf => True
  | node _ l y r => lo ≤ y ∧ y ≤ hi ∧ l.isBST lo (y - 1) ∧ r.isBST (y + 1) hi

/-- No red node has a red child. -/
def noRedRed : RBTree → Prop
  | leaf => True
  | node c l _ r =>
    (c = .red → l.rootColor = .black ∧ r.rootColor = .black) ∧ l.noRedRed ∧ r.noRedRed

/-- Every root-to-leaf path passes through exactly `n` black nodes. -/
def hasBlackHeight : Nat → RBTree → Prop
  | n, leaf => n = 0
  | n, node .red l _ r => hasBlackHeight n l ∧ hasBlackHeight n r
  | 0, node .black _ _ _ => False
  | n + 1, node .black l _ r => hasBlackHeight n l ∧ hasBlackHeight n r

/-- A subtree of a red-black tree: ordered with keys in `[lo, hi]`, no red parent of a red child,
and black height `n`. The root may be either colour. -/
def isRBSubtree (lo hi : Int) (n : Nat) (t : RBTree) : Prop :=
  t.isBST lo hi ∧ t.noRedRed ∧ t.hasBlackHeight n

/-- A red-black tree: an `isRBSubtree` whose root is black. -/
def isRB (lo hi : Int) (n : Nat) (t : RBTree) : Prop :=
  t.rootColor = .black ∧ t.isRBSubtree lo hi n

/-! ## Insertion -/

/-- Okasaki's rebalancing step: a red-red violation under a black parent becomes a red node with
two black children. -/
def balance : Color → RBTree → Int → RBTree → RBTree
  | .black, node .red (node .red a x b) y c, z, d
  | .black, node .red a x (node .red b y c), z, d
  | .black, a, x, node .red (node .red b y c) z d
  | .black, a, x, node .red b y (node .red c z d) =>
      node .red (node .black a x b) y (node .black c z d)
  | c, l, x, r => node c l x r

/-- `balance` restructures here, rather than rebuilding the same node. -/
def isRotation (c : Color) (l : RBTree) (x : Int) (r : RBTree) : Prop :=
  balance c l x r ≠ node c l x r

/-- The descending half of Okasaki's insertion: rebuild the search path, rebalancing on the way
back up. The caller blackens the resulting root. -/
def ins (x : Int) : RBTree → RBTree
  | leaf => node .red leaf x leaf
  | node c l y r =>
    if x < y then balance c (l.ins x) y r
    else if y < x then balance c l y (r.ins x)
    else node c l y r

/-- Inserting `x` rebalances `t`: somewhere along `x`'s search path, `balance` restructures rather
than rebuilding the node it was given. -/
def insertRebalances (x : Int) : RBTree → Prop
  | leaf => False
  | node c l y r =>
    if x < y then l.insertRebalances x ∨ isRotation c (l.ins x) y r
    else if y < x then r.insertRebalances x ∨ isRotation c l y (r.ins x)
    else False

end RBTree

end RedBlackTree
