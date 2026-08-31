/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt
import Mathlib.Data.Nat.Log

/-!
# Splay Trees: the Structure

The search trees of the splay-tree benchmark of Dewey, Nichols and Hardekopf (ICSE 2015, §V),
together with the `splay` operation and the size, height and key observations that the benchmark's
shape property is stated over. No generators live here.
-/

namespace SplayTree

/-- A binary tree with `Int` keys. -/
inductive Tree where
  | leaf : Tree
  | node : Tree → Int → Tree → Tree
deriving Repr, DecidableEq

/-- The number of internal nodes. -/
def Tree.size : Tree → Nat
  | leaf => 0
  | node l _ r => l.size + r.size + 1

/-- The number of nodes on the longest root-to-leaf path. Counting the root as depth `0`, a node at
depth `d` exists exactly when `d < t.height`. -/
def Tree.height : Tree → Nat
  | leaf => 0
  | node l _ r => max l.height r.height + 1

/-- Some node of `t` sits at depth greater than `d`. -/
def Tree.hasDeeperNode (d : Nat) (t : Tree) : Prop := d + 1 < t.height

/-- Every node of `t` sits at depth at most `d`. -/
def Tree.allWithinDepth (d : Nat) (t : Tree) : Prop := t.height ≤ d + 1

instance (d : Nat) (t : Tree) : Decidable (t.hasDeeperNode d) := by
  unfold Tree.hasDeeperNode; infer_instance

instance (d : Nat) (t : Tree) : Decidable (t.allWithinDepth d) := by
  unfold Tree.allWithinDepth; infer_instance

/-- The keys stored in the tree, in symmetric order. -/
def Tree.keys : Tree → List Int
  | leaf => []
  | node l x r => l.keys ++ x :: r.keys

/-- The validity predicate: a search tree with every key in `[lo, hi]`. -/
def Tree.isBST (lo hi : Int) : Tree → Prop
  | leaf => True
  | node l x r =>
    lo ≤ x ∧ x ≤ hi ∧
    isBST lo (x - 1) l ∧
    isBST (x + 1) hi r

/-- Exactly `⌊1.5 · log₂ n⌋`, in `Nat`: `Nat.log 4 m` is the greatest `k` with `4 ^ k ≤ m`, and
`4 ^ k ≤ n ^ 3 ↔ 2 ^ (2 * k) ≤ n ^ 3 ↔ k ≤ 1.5 · log₂ n`.

**The rounding is `⌊⌋`, and both of the benchmark's conjuncts are stated against it.** A depth is a
`Nat`, so `d > 1.5 · log₂ n ↔ d > ⌊1.5 · log₂ n⌋` and `d ≤ 1.5 · log₂ n ↔ d ≤ ⌊1.5 · log₂ n⌋`: the
floor is the integer at which the paper's two conditions actually change truth value, and it is the
same integer for both. Rounding up instead moves *both* thresholds by one — it makes "too deep"
strictly harder and "flat enough" strictly easier — so the pair it describes is neither a subset nor
a superset of the intended one. -/
def splayBound (n : Nat) : Nat := Nat.log 4 (n ^ 3)

/-- Moves `x` to the root by the usual zig / zig-zig / zig-zag rotations. A key that is absent, and
a rotation whose recursive splay returns `leaf`, leave the tree unchanged. -/
def Tree.splay (x : Int) : Tree → Tree
  | leaf => leaf
  | node l y r =>
    if x = y then node l y r
    else if x < y then
      match l with
      | leaf => node l y r
      | node ll z lr =>
        if x = z then node ll z (node lr y r)
        else if x < z then
          match splay x ll with
          | leaf => node ll z (node lr y r)
          | node a u b => node a u (node b z (node lr y r))
        else
          match splay x lr with
          | leaf => node ll z (node lr y r)
          | node a u b => node (node ll z a) u (node b y r)
    else
      match r with
      | leaf => node l y r
      | node rl z rr =>
        if x = z then node (node l y rl) z rr
        else if z < x then
          match splay x rr with
          | leaf => node (node l y rl) z rr
          | node a u b => node (node (node l y rl) z a) u b
        else
          match splay x rl with
          | leaf => node (node l y rl) z rr
          | node a u b => node (node l y a) u (node b z rr)

end SplayTree
