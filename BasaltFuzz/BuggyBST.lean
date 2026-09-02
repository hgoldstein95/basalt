/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Michael Hicks
-/
import Basalt.Combinators
import Basalt.PBT.Property

/-!
# A worked fuzzing target: binary search trees with buggy operations

A self-contained demonstration of coverage-guided fuzzing: generate binary search trees, run
insert/delete on them, and check the output against a postcondition. Each operation comes in a
correct version (whose property never fails, showing no false positives) and a buggy one (whose
property every backend finds a counterexample for).

The duplication of `BasaltExamples/BST`'s `genBST` here is forced, not a choice: an executable links
everything it imports, and that module imports the `Basalt` umbrella for its proofs, which reaches
Mathlib (`fuzz-run/README.md`). `genBST` is the one declaration held identical to the original, and
`BasaltTest/Fuzz.lean` pins that.
-/

namespace BasaltFuzz.BuggyBST

open Basalt.PBT RandomChoice

/-- A binary tree with `Int` keys. -/
inductive Tree where
  | leaf
  | node (l : Tree) (x : Int) (r : Tree)
deriving Repr, Inhabited

/-- In-order traversal. A tree is a valid BST with distinct keys iff this is strictly increasing. -/
def Tree.toList : Tree → List Int
  | leaf => []
  | node l x r => l.toList ++ x :: r.toList

/-- Strictly-increasing check on a list of keys. -/
def sortedStrict : List Int → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => a < b && sortedStrict (b :: rest)

/-- The BST invariant, as a decidable `Bool`: the in-order traversal is strictly increasing. A
property must *run*, so this is a `Bool`, where `BasaltExamples/BST`'s `Tree.isBST` is the `Prop` its
`sound_complete` proof needs — the two say the same thing to different consumers. -/
def Tree.isBST (t : Tree) : Bool := sortedStrict t.toList

/-- Is `k` present? -/
def Tree.contains (t : Tree) (k : Int) : Bool :=
  match t with
  | leaf => false
  | node l x r => if k == x then true else if k < x then l.contains k else r.contains k

/-- Correct insert: descend left/right by comparison, and treat an equal key as a no-op. -/
def Tree.insert (t : Tree) (k : Int) : Tree :=
  match t with
  | leaf => node leaf k leaf
  | node l x r =>
    if k < x then node (l.insert k) x r
    else if x < k then node l x (r.insert k)
    else node l x r

/-- Buggy insert. The bug is a missing equal-key guard: when `k == x` it falls into the `else`
branch and inserts a **duplicate** into the right subtree, so the in-order traversal contains `x`
twice and `isBST` fails. Triggering it requires inserting a key that is already present — a
condition coverage-guided search reaches by driving generation toward the equal-key branch. -/
def Tree.insertBuggy (t : Tree) (k : Int) : Tree :=
  match t with
  | leaf => node leaf k leaf
  | node l x r =>
    if k < x then node (l.insertBuggy k) x r
    else node l x (r.insertBuggy k)

/-! ### A bug an invariant cannot catch: `delete`, checked against a list model

`insertBuggy` above breaks `isBST` outright, so any ill-formed output is a witness. The `delete` bug
below instead *silently drops* keys: the output is still a perfectly valid BST, so `isBST` passes on
every input and the postcondition has to be a model comparison (`toList` against `List.erase`). The
lesson is about the specification, not the search — an invariant check is strictly weaker than a
model, and this bug is invisible to the former. It is still a shallow bug (a few dozen runs for any
backend); `BasaltFuzz/Staged.lean` is the one that separates them. -/

/-- Split off the smallest key: `some (min, rest)`, or `none` for a leaf. -/
def Tree.deleteMin : Tree → Option (Int × Tree)
  | leaf => none
  | node leaf x r => some (x, r)
  | node l x r =>
    match l.deleteMin with
    | some (m, l') => some (m, node l' x r)
    | none => some (x, r)

/-- As `deleteMin`, but the left-spine base case returns `.leaf` where it should return the removed
node's right subtree, so every key under that subtree vanishes. The result is still a *sorted* tree,
so `isBST` passes — only a model comparison catches it. -/
def Tree.deleteMinBuggy : Tree → Option (Int × Tree)
  | leaf => none
  | node leaf x _ => some (x, .leaf)
  | node l x r =>
    match l.deleteMinBuggy with
    | some (m, l') => some (m, node l' x r)
    | none => some (x, r)

/-- Standard BST delete: the two-child case promotes the right subtree's minimum. -/
def Tree.deleteWith (dmin : Tree → Option (Int × Tree)) (t : Tree) (k : Int) : Tree :=
  match t with
  | leaf => leaf
  | node l x r =>
    if k < x then node (Tree.deleteWith dmin l k) x r
    else if x < k then node l x (Tree.deleteWith dmin r k)
    else
      match dmin r with
      | some (m, r') => node l m r'
      | none => l

/-- Correct delete. -/
def Tree.delete (t : Tree) (k : Int) : Tree := Tree.deleteWith Tree.deleteMin t k

/-- Delete built on `deleteMinBuggy`. Reaching the bug needs three things at once: `k` must be a key
the tree actually contains, that key's node must have a non-empty right subtree, and the leftmost
node of *that* subtree must itself have a right child. -/
def Tree.deleteBuggy (t : Tree) (k : Int) : Tree := Tree.deleteWith Tree.deleteMinBuggy t k

/-- Generate a BST with keys in `[lo, hi]`: `leaf` on an empty interval, else equal weight between a
leaf and a node from a uniform pivot with two recursive subtrees over the disjoint subintervals (so
keys are automatically distinct).

Deliberately term-for-term `BasaltExamples/BST`'s `Tree.genBST`, monomorphized to the `Int` keys that
module instantiates and stripped of its proofs, so what this module fuzzes is the generator that
module proves sound, complete, almost-surely terminating, and cost-bounded. `BasaltTest/Fuzz.lean`
runs both at `FuzzGen` on fixed buffers and pins that they agree, so drift between them is a
`lake build` failure. -/
def genBST [Gen G] (lo hi : Int) : G Tree := do
  if h : lo > hi then
    return .leaf
  else
    frequency [
      (1, fun () => pure .leaf),
      (1, fun () => do
        let x ← chooseInt lo hi (by omega)
        let l ← genBST lo (x - 1)
        let r ← genBST (x + 1) hi
        return .node l x r)
    ] (by simp)
partial_fixpoint

/-! ### Properties

Each is `forAll <generator> <predicate>`, left polymorphic in `G` so the *same* property runs under
every interpretation the runner offers — libFuzzer (`FuzzGen`), random `IO`, or `Plausible.Gen`. -/

/-- Key bounds for generated trees and inserted keys. The range is small so equal-key collisions —
the condition that exposes `insertBuggy` — are reachable. -/
abbrev loKey : Int := 1
abbrev hiKey : Int := 15

/-- Generator of a `(BST, key)` pair to run an insert on. -/
def genTreeAndKey [Gen G] : G (Tree × Int) := do
  let t ← genBST loKey hiKey
  let k ← chooseInt loKey hiKey (by decide)
  return (t, k)

/-- Sanity: the generator only ever produces valid BSTs. Should never fail. -/
def prop_genBST_isBST [Gen G] : G TestOutcome :=
  forAll (genBST loKey hiKey) (fun t => t.isBST)

/-- The correct insert preserves the BST invariant. Should never fail (no false positives). -/
def prop_insert_preserves_BST [Gen G] : G TestOutcome :=
  forAll genTreeAndKey (fun (t, k) => t.insert k |>.isBST)

/-- The buggy insert claims to preserve the BST invariant. Every backend finds a counterexample: a
valid BST plus a key it already contains, which the missing equal-key guard duplicates. -/
def prop_insertBuggy_preserves_BST [Gen G] : G TestOutcome :=
  forAll genTreeAndKey (fun (t, k) => t.insertBuggy k |>.isBST)

/-! ### Model-based properties for `delete`

The postcondition is `t.delete k`'s in-order traversal against the list model `t.toList.erase k` —
strictly stronger than `isBST`, and the only thing that sees a silently dropped key. Both properties
`discard` unless the tree actually contains `k`, since deleting an absent key exercises nothing. -/

/-- Correct delete agrees with the list model. Never fails. -/
def prop_delete_model [Gen G] : G TestOutcome := do
  let (t, k) ← genTreeAndKey
  if !t.contains k then return .discard
  checkWith ((t.delete k).toList == t.toList.erase k)
    (fun () => s!"t={reprStr t}, k={k}")

/-- The buggy delete claims to agree with the list model. The counterexample renders both traversals,
so the dropped keys are visible in the report. -/
def prop_deleteBuggy_model [Gen G] : G TestOutcome := do
  let (t, k) ← genTreeAndKey
  if !t.contains k then return .discard
  let got := (t.deleteBuggy k).toList
  let want := t.toList.erase k
  checkWith (got == want)
    (fun () => s!"t={reprStr t}, k={k}, got={got}, want={want}")

/-! ### Composed, multi-input properties

These illustrate that a property composes with ordinary monadic `do`: several inputs drawn in
sequence, a precondition as an early `return .discard`, and one `check`/`checkWith` at the end.
They are polymorphic in `G`, so the *same* term runs under `Plausible.Gen` too. -/

/-- Insert two *distinct* keys with the correct `insert`; the invariant is preserved. Never fails.
Composition: one tree + two keys, a distinctness precondition, then `check`. -/
def prop_insert_two_distinct [Gen G] : G TestOutcome := do
  let t  ← genBST loKey hiKey
  let k1 ← chooseInt loKey hiKey (by decide)
  let k2 ← chooseInt loKey hiKey (by decide)
  if k1 == k2 then return .discard
  let t' := (t.insert k1).insert k2
  check t'.isBST

/-- The same composition with the buggy insert: libFuzzer finds a `(t, k1, k2)` counterexample, and
`checkWith` renders all three drawn inputs. -/
def prop_insertBuggy_two_distinct [Gen G] : G TestOutcome := do
  let t  ← genBST loKey hiKey
  let k1 ← chooseInt loKey hiKey (by decide)
  let k2 ← chooseInt loKey hiKey (by decide)
  if k1 == k2 then return .discard
  let t' := (t.insertBuggy k1).insertBuggy k2
  checkWith t'.isBST (fun () => s!"t={reprStr t}, k1={k1}, k2={k2}")

end BasaltFuzz.BuggyBST
