/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Segev Elazar-Mittelman
-/
module

public import Basalt
public import BasaltExamples.Heap

/-!
# The Walk's Options

Pins what `basalt.walk.dropUnreachable` (with `basalt.walk.failHeads`) and
`basalt.walk.keepMatchesOn` change in the precondition `walk` leaves on `SPMF.mayObs.spec`.
-/

@[expose] public section

namespace WalkOptionsTest

/-! ## `basalt.walk.dropUnreachable`

Every value the generator returns has another constructor than the one asked for, at some depth:
the precondition is `False`, without walking the generator. The prune alone leaves the equation,
whose constructors clash only under an injectivity it does not use. -/

def genSmall [Gen G] (h : G Nat) : G Heap.Tree := do
  let n ← h
  if n = 0 then pure (.node .leaf n .leaf) else pure .leaf

/--
trace: h : SPMF ℕ
l r : Heap.Tree
x : ℕ
hf : False
⊢ False
-/
#guard_msgs in
set_option basalt.walk.dropUnreachable true in
example (h : SPMF Nat) (l r : Heap.Tree) (x : Nat) (hf : False) :
    SPMF.mayObs.spec (genSmall h) (· = .node (.node l x r) x .leaf) := by
  rw [genSmall]
  walk
  trace_state
  exact hf

/--
trace: h : SPMF ℕ
l r : Heap.Tree
x : ℕ
hf : False
⊢ ∃ n ∈ h.support, if n = 0 then Heap.Tree.leaf.node n Heap.Tree.leaf = (l.node x r).node x Heap.Tree.leaf else False
-/
#guard_msgs in
example (h : SPMF Nat) (l r : Heap.Tree) (x : Nat) (hf : False) :
    SPMF.mayObs.spec (genSmall h) (· = .node (.node l x r) x .leaf) := by
  rw [genSmall]
  walk
  trace_state
  exact hf.elim

/-! A tail named in `basalt.walk.failHeads` is taken to return nothing; unnamed, it is a call, which
may return anything, and nothing is dropped. (`stop` does return a value: the option is the caller's
word for it.) -/

def stop [Gen G] : G Heap.Tree := pure (.node .leaf 0 .leaf)

def genOrStop [Gen G] (h : G Nat) : G Heap.Tree := do
  let n ← h
  if n = 0 then stop else pure .leaf

/--
trace: h : SPMF ℕ
l r : Heap.Tree
x : ℕ
hf : False
⊢ False
-/
#guard_msgs in
set_option basalt.walk.dropUnreachable true in
set_option basalt.walk.failHeads "WalkOptionsTest.stop" in
example (h : SPMF Nat) (l r : Heap.Tree) (x : Nat) (hf : False) :
    SPMF.mayObs.spec (genOrStop h) (· = .node l x r) := by
  rw [genOrStop]
  walk
  trace_state
  exact hf

/--
trace: h : SPMF ℕ
l r : Heap.Tree
x : ℕ
hf : False
⊢ ∃ n ∈ h.support, if n = 0 then Heap.Tree.leaf.node 0 Heap.Tree.leaf = l.node x r else False
-/
#guard_msgs in
set_option basalt.walk.dropUnreachable true in
example (h : SPMF Nat) (l r : Heap.Tree) (x : Nat) (hf : False) :
    SPMF.mayObs.spec (genOrStop h) (· = .node l x r) := by
  rw [genOrStop]
  walk
  trace_state
  exact hf.elim

/-! ## `basalt.walk.keepMatchesOn`

A `match` whose discriminant mentions a named constant is left in the precondition for the caller
to decide, rather than split on. -/

def tag (n : Nat) : Bool := n == 0

def genTagged [Gen G] (k : Nat) : G Nat :=
  match tag k with
  | true => pure 0
  | false => pure 1

/--
trace: k : ℕ
hk : tag k = false
⊢ match tag k with
  | true => False
  | false => True
-/
#guard_msgs in
set_option basalt.walk.keepMatchesOn "WalkOptionsTest.tag" in
example (k : Nat) (hk : tag k = false) : SPMF.mayObs.spec (genTagged k) (· = 1) := by
  rw [genTagged]
  walk
  trace_state
  rw [hk]; trivial

end WalkOptionsTest
