/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Michael Hicks
-/
import Basalt.Fuzz.Runner
import Basalt.Combinators
import BasaltFuzz.BST

/-!
# `basalt-fuzz` executable entry point

Lean owns `main`; it selects a named property and hands control to libFuzzer via `Fuzz.go`. This
module (and everything it imports) is Mathlib-free so the executable links a small closure; it is
built by `fuzz-run/build.sh`, never by the default `lake build`.
-/

open Basalt.Fuzz RandomChoice

/-- Infrastructure self-test: a deliberately false property. Its failure lives on a distinct branch
(`fail` vs `pass`), so it is reachable by coverage-guided search — libFuzzer hits a byte `≥ 200`
quickly, the counterexample is reported, and the process crashes for libFuzzer to record. -/
def propThreshold : FuzzGen TestOutcome :=
  forAll (chooseNat 0 255) (· < 200)

/-- The property registry, selected by the first CLI argument. `bst-*` are the worked BST demo
(`BasaltFuzz/BST.lean`): the `-buggy-*` ones have real bugs libFuzzer finds; the others must never
fail. -/
def properties : List (String × FuzzGen TestOutcome) :=
  [ ("threshold",            propThreshold),
    ("bst-gen",              BasaltFuzz.BST.prop_genBST_isBST),
    ("bst-insert",           BasaltFuzz.BST.prop_insert_preserves_BST),
    ("bst-buggy-insert",     BasaltFuzz.BST.prop_insertBuggy_preserves_BST),
    ("bst-insert2",          BasaltFuzz.BST.prop_insert_two_distinct),
    ("bst-buggy-insert2",    BasaltFuzz.BST.prop_insertBuggy_two_distinct) ]

def main (args : List String) : IO Unit :=
  dispatch properties args
