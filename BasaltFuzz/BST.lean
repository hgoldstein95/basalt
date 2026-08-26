/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Michael Hicks
-/
import Basalt.Combinators
import Basalt.Fuzz.Core

/-!
# A worked fuzzing target: binary search trees with a buggy `insert`

A self-contained, Mathlib-free demonstration of coverage-guided fuzzing. We generate binary search
trees, run insert/delete operations on them, and check that the outputs still satisfy the BST
invariant — the shape of test the request asked for. Two operations are provided: a correct one
(whose property never fails, showing no false positives) and a buggy one (whose property libFuzzer
discovers a counterexample for).

Everything here is decidable `Bool` and imports only `Basalt.Combinators`/`Basalt.Fuzz.Core`, so
the executable that links it stays Mathlib-free (`FUZZING-DESIGN.md` §6).
-/

namespace BasaltFuzz.BST

open Basalt.Fuzz RandomChoice

/-- A binary tree with `Nat` keys. -/
inductive Tree where
  | leaf
  | node (l : Tree) (x : Nat) (r : Tree)
deriving Repr, Inhabited

/-- In-order traversal. A tree is a valid BST with distinct keys iff this is strictly increasing. -/
def Tree.toList : Tree → List Nat
  | leaf => []
  | node l x r => l.toList ++ x :: r.toList

/-- Strictly-increasing check on a list of naturals. -/
def sortedStrict : List Nat → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => a < b && sortedStrict (b :: rest)

/-- The BST invariant, as a decidable `Bool`: the in-order traversal is strictly increasing. -/
def Tree.isBST (t : Tree) : Bool := sortedStrict t.toList

/-- Is `k` present? -/
def Tree.contains (t : Tree) (k : Nat) : Bool :=
  match t with
  | leaf => false
  | node l x r => if k == x then true else if k < x then l.contains k else r.contains k

/-- Correct insert: descend left/right by comparison, and treat an equal key as a no-op. -/
def Tree.insert (t : Tree) (k : Nat) : Tree :=
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
def Tree.insertBuggy (t : Tree) (k : Nat) : Tree :=
  match t with
  | leaf => node leaf k leaf
  | node l x r =>
    if k < x then node (l.insertBuggy k) x r
    else node l x (r.insertBuggy k)

/-- Generate a BST with keys in `[lo, hi]`: `leaf` on an empty interval, else `pick` between a leaf
and a node from a uniform pivot with two recursive subtrees over the disjoint subintervals (so keys
are automatically distinct). Same generator as `BasaltExamples/BST`, minus the proofs. -/
def genBST [Gen G] (lo hi : Nat) : G Tree := do
  if h : lo > hi then
    return .leaf
  else
    pick
      (fun () => pure .leaf)
      (fun () => do
        let x ← chooseNat lo hi (by omega)
        let l ← genBST lo (x - 1)
        let r ← genBST (x + 1) hi
        return .node l x r)
partial_fixpoint

/-! ### Properties

Each is `forAll <generator> <predicate>` at `FuzzGen`, so `runOne` (and libFuzzer) can drive it. -/

/-- Key bounds for generated trees and inserted keys. Keys start at `1`, not `0`: `genBST`'s left
recursion uses `x - 1`, and truncated `Nat` subtraction makes `0 - 1 = 0`, so a pivot of `0` would
recurse on `[0,0]` again and emit duplicate `0` keys — which strict `isBST` rejects independent of
any insert. Starting at `1` keeps every generated tree strictly sorted. The range is small so
equal-key collisions — the condition that exposes `insertBuggy` — are reachable. -/
abbrev loKey : Nat := 1
abbrev hiKey : Nat := 15

/-- Generator of a `(BST, key)` pair to run an insert on. -/
def genTreeAndKey : FuzzGen (Tree × Nat) := do
  let t ← genBST loKey hiKey
  let k ← chooseNat loKey hiKey (by decide)
  return (t, k)

/-- Sanity: the generator only ever produces valid BSTs. Should never fail. -/
def prop_genBST_isBST : FuzzGen TestOutcome :=
  forAll (genBST loKey hiKey) (fun t => t.isBST)

/-- The correct insert preserves the BST invariant. Should never fail (no false positives). -/
def prop_insert_preserves_BST : FuzzGen TestOutcome :=
  forAll genTreeAndKey (fun (t, k) => t.insert k |>.isBST)

/-- The buggy insert claims to preserve the BST invariant. libFuzzer finds a counterexample: a valid
BST plus a key it already contains, which the missing equal-key guard duplicates. -/
def prop_insertBuggy_preserves_BST : FuzzGen TestOutcome :=
  forAll genTreeAndKey (fun (t, k) => t.insertBuggy k |>.isBST)

/-! ### Composed, multi-input properties

These illustrate that a property composes with ordinary monadic `do`: several inputs drawn in
sequence, a precondition as an early `return .discard`, and one `check`/`checkWith` at the end.
They are polymorphic in `G`, so the *same* term runs under `Plausible.Gen` too. -/

/-- Insert two *distinct* keys with the correct `insert`; the invariant is preserved. Never fails.
Composition: one tree + two keys, a distinctness precondition, then `check`. -/
def prop_insert_two_distinct [Gen G] : G TestOutcome := do
  let t  ← genBST loKey hiKey
  let k1 ← chooseNat loKey hiKey (by decide)
  let k2 ← chooseNat loKey hiKey (by decide)
  if k1 == k2 then return .discard
  let t' := (t.insert k1).insert k2
  check t'.isBST

/-- The same composition with the buggy insert: libFuzzer finds a `(t, k1, k2)` counterexample, and
`checkWith` renders all three drawn inputs. -/
def prop_insertBuggy_two_distinct [Gen G] : G TestOutcome := do
  let t  ← genBST loKey hiKey
  let k1 ← chooseNat loKey hiKey (by decide)
  let k2 ← chooseNat loKey hiKey (by decide)
  if k1 == k2 then return .discard
  let t' := (t.insertBuggy k1).insertBuggy k2
  checkWith t'.isBST (fun () => s!"t={reprStr t}, k1={k1}, k2={k2}")

end BasaltFuzz.BST
