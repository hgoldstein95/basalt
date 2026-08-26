/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Michael Hicks
-/
import Basalt.Fuzz.Runner
import Basalt.Combinators
import BasaltFuzz.BuggyBST
import BasaltFuzz.Staged

/-!
# `basalt-fuzz` executable entry point

Lean owns `main`; it selects a named property and a backend, and `Fuzz.dispatch` runs the campaign
(libFuzzer via `Fuzz.go`, or a random loop). This module (and everything it imports) is Mathlib-free
so the executable links a small closure; it is built by `fuzz-run/build.sh`, never by the default
`lake build`.
-/

open Basalt.Fuzz RandomChoice

/-- Infrastructure self-test: a deliberately false property. Its failure lives on a distinct branch
(`fail` vs `pass`), so it is reachable by coverage-guided search — libFuzzer hits a byte `≥ 200`
quickly, the counterexample is reported, and the process crashes for libFuzzer to record. -/
def propThreshold [Gen G] : G TestOutcome :=
  forAll (chooseNat 0 255) (· < 200)

/-- The property registry, selected by the first non-flag CLI argument. `bst-*` are the worked BST
demo (`BasaltFuzz/BuggyBST.lean`): the `-buggy-*` ones have real bugs every backend can find; the
others must never fail. `chain-*` are the staged microbenchmark (`BasaltFuzz/Staged.lean`), the one
place the backends differ by orders of magnitude.

Each entry is a `Property` — a property still polymorphic in its monad — so one registry serves all
three backends. The `fun _ =>` is the explicit `G` binder `Property` asks for; nothing else about a
property changes to make it fuzzable or randomly testable. -/
def properties : List (String × Property) :=
  [ ("threshold",            fun _ => propThreshold),
    ("bst-gen",              fun _ => BasaltFuzz.BuggyBST.prop_genBST_isBST),
    ("bst-insert",           fun _ => BasaltFuzz.BuggyBST.prop_insert_preserves_BST),
    ("bst-buggy-insert",     fun _ => BasaltFuzz.BuggyBST.prop_insertBuggy_preserves_BST),
    ("bst-insert2",          fun _ => BasaltFuzz.BuggyBST.prop_insert_two_distinct),
    ("bst-buggy-insert2",    fun _ => BasaltFuzz.BuggyBST.prop_insertBuggy_two_distinct),
    ("bst-delete",           fun _ => BasaltFuzz.BuggyBST.prop_delete_model),
    ("bst-buggy-delete",     fun _ => BasaltFuzz.BuggyBST.prop_deleteBuggy_model),
    ("chain-2",              fun _ => BasaltFuzz.Staged.propChain 2),
    ("chain-3",              fun _ => BasaltFuzz.Staged.propChain 3),
    ("chain-4",              fun _ => BasaltFuzz.Staged.propChain 4) ]

def main (args : List String) : IO Unit :=
  dispatch properties args
