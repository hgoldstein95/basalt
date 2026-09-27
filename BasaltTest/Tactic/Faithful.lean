/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt
import BasaltExamples.BST

/-!
# The `faithful_fixpoint` Contract

Pins how `faithful_fixpoint` takes a callee's `IsFaithful` law: whole, whether its arguments are
implicit or quantified explicitly.
-/

namespace FaithfulFixpointTest

open BST

def twoBSTs [Gen G] : G (BST.Tree Int × BST.Tree Int) := do
  let a ← Tree.genBST 0 3
  let b ← Tree.genBST 1 2
  pure (a, b)

theorem twoBSTs.terminates : IsAlmostSurelyTerminating twoBSTs := by
  rw [IsAlmostSurelyTerminating.iff_obs, twoBSTs]
  walk [Tree.genBST.terminates.obs]
  simp

theorem genBST.faithful_explicit (lo hi : Int) : IsFaithful (Tree.genBST lo hi) :=
  Tree.genBST.faithful

example : IsFaithful twoBSTs := by
  faithful_fixpoint [twoBSTs.terminates, Tree.genBST.faithful]

example : IsFaithful twoBSTs := by
  faithful_fixpoint [twoBSTs.terminates, genBST.faithful_explicit]

end FaithfulFixpointTest
