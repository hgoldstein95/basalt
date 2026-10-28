/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Segev Elazar-Mittelman
-/
module

public import Basalt
public import BasaltExamples.ArbNat
public import BasaltExamples.ArbList
public import BasaltExamples.BST
public import BasaltExamples.STLC.GenType

/-!
# The Enumeration Laws, Walked

`walk fixpoint` proves `IsEnumerated`, `IsWeighed` and `IsCostEnumerated` construct by construct,
through `genRel_enumerates`, `genRel_weighs` and `genRel_costEnumerates`, and `EnumeratesSome` for a
generator that fails and backtracks, through `genRel_enumeratesSome`.
-/

@[expose] public section

open Basalt ArbNat ArbList BST

namespace EnumLawTest

theorem nat_enumerated : IsEnumerated Nat.arbitrary := ⟨by walk fixpoint⟩
theorem bst_enumerated : IsEnumerated (Tree.genBST lo hi) := ⟨by walk fixpoint⟩
theorem genType_enumerated : IsEnumerated STLC.genType := ⟨by walk fixpoint⟩
theorem list_enumerated : IsEnumerated List.arbitrary := ⟨by walk fixpoint [nat_enumerated.enumerates]⟩

theorem nat_weighed : IsWeighed Nat.arbitrary := ⟨by walk fixpoint⟩
theorem bst_weighed : IsWeighed (Tree.genBST lo hi) := ⟨by walk fixpoint⟩
theorem genType_weighed : IsWeighed STLC.genType := ⟨by walk fixpoint⟩
theorem list_weighed : IsWeighed List.arbitrary := ⟨by walk fixpoint [nat_weighed.weighs]⟩

theorem nat_costEnumerated : IsCostEnumerated Nat.arbitrary := ⟨by walk fixpoint⟩
theorem bst_costEnumerated : IsCostEnumerated (Tree.genBST lo hi) := ⟨by walk fixpoint⟩
theorem genType_costEnumerated : IsCostEnumerated STLC.genType := ⟨by walk fixpoint⟩
theorem list_costEnumerated : IsCostEnumerated List.arbitrary :=
  ⟨by walk fixpoint [nat_costEnumerated.costEnumerates]⟩

/-- `genBST`'s enumeration, where defined, is exactly the valid BSTs: the walked law and the
generator's correctness proof, combined. -/
example (hd : (Tree.genBST (G := Basalt.Finite) lo hi) ≠ .undef) (t : BST.Tree Int) :
    (Tree.genBST (G := Basalt.Finite) lo hi).Mem t ↔ t.isBST lo hi :=
  bst_enumerated.mem_iff Tree.genBST.sound_complete hd t

/-! ## Failure and backtracking

Defined here, not imported, so `walk fixpoint` must realize their `eq_def` itself. -/

inductive Ty | nat | bool

inductive Expr | lit (n : Nat) | isPos (n : Nat) | add (l r : Expr)

def digit [Gen G] : G Nat := do return (← RandomChoice.choose 0 2 (by omega)).down.val

/-- A derived generator's shape: a rule per branch, `fail` where a rule does not apply, recursion
on a size. -/
def hasType [Gen G] [Fail G] [Backtrack G] (τ : Ty) : Nat → G Expr
  | 0 => Backtrack.backtrack [
      (1, fun _ => match τ with | .nat => do return .lit (← digit) | _ => Fail.fail),
      (1, fun _ => match τ with
        | .bool => do let n ← digit; if n ≠ 0 then pure (.isPos n) else Fail.fail
        | _ => Fail.fail)]
  | size + 1 => Backtrack.backtrack [
      (1, fun _ => match τ with | .nat => do return .lit (← digit) | _ => Fail.fail),
      (1, fun _ => match τ with
        | .bool => do let n ← digit; if n ≠ 0 then pure (.isPos n) else Fail.fail
        | _ => Fail.fail),
      (size + 1, fun _ => match τ with
        | .nat => Expr.add <$> hasType .nat size <*> hasType .nat size
        | _ => Fail.fail)]

theorem hasType_enumeratesSome (τ : Ty) (n : Nat) :
    EnumeratesSome (hasType (G := Basalt.Finite) τ n) (hasType (G := OptionT SPMF) τ n) := by
  induction n generalizing τ with
  | zero => unfold hasType; walk
  | succ n ih => unfold hasType; walk [ih .nat]

/-- Unbounded recursion through `backtrack`, so a `partial_fixpoint`. -/
def digits [Gen G] [Fail G] [Backtrack G] [MonoBacktrack G] : G (List Nat) :=
  Backtrack.backtrack [(1, fun _ => pure []), (2, fun _ => do return (← digit) :: (← digits))]
partial_fixpoint

theorem digits_enumeratesSome :
    EnumeratesSome (digits (G := Basalt.Finite)) (digits (G := OptionT SPMF)) := by
  walk fixpoint

end EnumLawTest
