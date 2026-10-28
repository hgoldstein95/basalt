/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
module

public import Basalt
public import BasaltExamples.ArbList
public import BasaltExamples.BST

/-!
# The Cost-Erasure Walk Contract

Pins how `walk fixpoint` proves the two fields of `IsCostFaithful`, `SPMF.Cost.ErasedLe` and
`SPMF.Cost.LeErased`: construct by construct, with a callee's law passed by its fields.
-/

@[expose] public section

open RandomChoice ArbNat ArbList BST

namespace CostErasureTest

-- Every combinator relates itself at the two interpretations, so a generator's walk leaves nothing.
theorem natFaithful : IsCostFaithful Nat.arbitrary := ⟨by walk fixpoint, by walk fixpoint⟩

example : IsCostFaithful (Tree.genBST lo hi) := ⟨by walk fixpoint, by walk fixpoint⟩

example : IsCostFaithful (suchThat Nat.arbitrary (· != 0)) :=
  ⟨by walk [natFaithful.erasedLe], by walk [natFaithful.leErased]⟩

/-- Defined here rather than imported, so `walk fixpoint` must realize its `eq_def` itself. -/
def coins [Gen G] : G (List Bool) := do
  if (← choose 0 1 (by omega)).down.val = 0 then pure []
  else return ((← choose 0 1 (by omega)).down.val == 1) :: (← coins)
partial_fixpoint

example : IsCostFaithful coins := ⟨by walk fixpoint, by walk fixpoint⟩

-- A callee's law is passed by the field the walk is proving.
example : IsCostFaithful List.arbitrary :=
  ⟨by walk fixpoint [natFaithful.erasedLe], by walk fixpoint [natFaithful.leErased]⟩

/--
error: no rule, hypothesis, or fact relates
  Nat.arbitrary
to its counterpart. Pass a fact about it to `walk [_]`; a recursive combinator needs a `@[gen_rel_rule]` relating it under every `GenRel` (as `GenRel.listOf` does) or a `@[gen_rule]` relating it under `SPMF.Cost.ErasedLe` alone.
(in the unfolding of `oneOfWith`)
-/
#guard_msgs in
example : SPMF.Cost.ErasedLe (List.arbitrary : SPMF.Cost (List Nat)) List.arbitrary := by
  walk fixpoint

end CostErasureTest
