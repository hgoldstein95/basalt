/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
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
through `genRel_enumerates`, `genRel_weighs` and `genRel_costEnumerates`.
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

end EnumLawTest
