/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt

namespace MutationTest

open RandomChoice

inductive Tree (α : Type) where
  | leaf : Tree α
  | node : Tree α → α → Tree α → Tree α
deriving Repr

def Tree.isBST (lo hi : Nat) : Tree Nat → Prop
  | leaf => true
  | node l x r =>
    lo ≤ x ∧ x ≤ hi ∧
    isBST lo (x - 1) l ∧
    isBST (x + 1) hi r

def Tree.dropRandomLeaf [Gen G] : Tree α → G (Tree α)
  | leaf => pure leaf
  | node leaf x leaf => pure leaf
  | node l x leaf => (node · x leaf) <$> Tree.dropRandomLeaf l
  | node leaf x r => (node leaf x ·) <$> Tree.dropRandomLeaf r
  | node l x r => do
    if (← choose 0 1 (by simp)).down.val == 0 then
      (node · x r) <$> Tree.dropRandomLeaf l
    else
      (node l x ·) <$> Tree.dropRandomLeaf r

attribute [local simp]
  Tree.dropRandomLeaf
  Tree.isBST
  SPMF.support_pure
  SPMF.support_map
  SPMF.support_bind
  SPMF.support_choose
in
example {t t' : Tree Nat} :
    t.isBST lo hi →
    t' ∈ SPMF.support (Tree.dropRandomLeaf t) →
    t'.isBST lo hi := by
  intro hbst hmem
  induction t generalizing t' lo hi with
  | leaf => simp_all
  | node l x r ihl ihr =>
    match l, r with
    | .leaf, .leaf => simp_all
    | .node _ _ _, .leaf => fun_cases Tree.isBST lo hi t' <;> simp_all
    | .leaf, .node _ _ _ => fun_cases Tree.isBST lo hi t' <;> simp_all
    | .node ll lx lr, .node rl rx rr =>
      simp_all
      obtain ⟨n, _, hmem'⟩ := hmem
      rcases hmem' with ⟨_, hmem'⟩ | ⟨_, hmem'⟩
      · fun_cases Tree.isBST lo hi t' <;> simp_all
      · fun_cases Tree.isBST lo hi t' <;> simp_all
