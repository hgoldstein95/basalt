import Basalt
import Basalt.Examples.HowToSpecifyIt.BST
import Basalt.Experiments.BDT.BST.Generator

namespace BDTExperiments

open BST

/-- Generate a random Nat in range [0, 100] -/
def genTestNat : Gen Nat := RandomChoice.choose 0 100 (by omega)

/-- Boolean implication: `A ==> B` is equivalent to `¬A ∨ B` -/
def boolImplies (a b : Bool) : Bool := !a || b

-- Pure property definitions (return Bool directly)

/-- After inserting a key-value pair, find should return that value -/
def prop_insert_find (tree : BST Nat Nat) (key val : Nat)
    (insert : Nat → Nat → BST Nat Nat → BST Nat Nat)
    (find : Nat → BST Nat Nat → Option Nat) : Bool :=
  find key (insert key val tree) == some val

/-- Inserting twice with the same key should keep the second value -/
def prop_insert_insert (tree : BST Nat Nat) (key val1 val2 : Nat)
    (insert : Nat → Nat → BST Nat Nat → BST Nat Nat)
    (find : Nat → BST Nat Nat → Option Nat) : Bool :=
  find key (insert key val2 (insert key val1 tree)) == some val2

/-- After deleting a key, find should return none -/
def prop_delete_find (tree : BST Nat Nat) (key : Nat)
    (delete : Nat → BST Nat Nat → BST Nat Nat)
    (find : Nat → BST Nat Nat → Option Nat) : Bool :=
  find key (delete key tree) == none

/-- The size should increase by at most 1 after insert -/
def prop_insert_size (tree : BST Nat Nat) (key val : Nat)
    (insert : Nat → Nat → BST Nat Nat → BST Nat Nat)
    (size : BST Nat Nat → Nat) : Bool :=
  let newSize := size (insert key val tree)
  let oldSize := size tree
  newSize == oldSize || newSize == oldSize + 1

/-- The size should decrease by at most 1 after delete -/
def prop_delete_size (tree : BST Nat Nat) (key : Nat)
    (delete : Nat → BST Nat Nat → BST Nat Nat)
    (size : BST Nat Nat → Nat) : Bool :=
  let newSize := size (delete key tree)
  let oldSize := size tree
  newSize == oldSize || newSize == oldSize - 1

/-- Valid BST after insert -/
def prop_insert_valid (tree : BST Nat Nat) (key val : Nat)
    (insert : Nat → Nat → BST Nat Nat → BST Nat Nat)
    (valid : BST Nat Nat → Bool) : Bool :=
  boolImplies (valid tree) (valid (insert key val tree))

/-- Valid BST after delete -/
def prop_delete_valid (tree : BST Nat Nat) (key : Nat)
    (delete : Nat → BST Nat Nat → BST Nat Nat)
    (valid : BST Nat Nat → Bool) : Bool :=
  boolImplies (valid tree) (valid (delete key tree))

/-- Keys in toList should be sorted -/
def prop_toList_sorted (tree : BST Nat Nat)
    (toList : BST Nat Nat → List (Nat × Nat)) : Bool :=
  let keys := (toList tree).map (·.1)
  keys == keys.mergeSort (fun a b => compare a b == .lt)

/-- Union should contain all keys from both trees -/
def prop_union_contains (tree1 tree2 : BST Nat Nat) (key : Nat)
    (union : BST Nat Nat → BST Nat Nat → BST Nat Nat)
    (find : Nat → BST Nat Nat → Option Nat) : Bool :=
  let result := union tree1 tree2
  match find key tree1, find key tree2 with
  | some _, _ => find key result != none
  | none, some _ => find key result != none
  | none, none => true

/-- Union should prefer left tree for duplicate keys -/
def prop_union_left_priority (tree1 tree2 : BST Nat Nat) (key : Nat)
    (union : BST Nat Nat → BST Nat Nat → BST Nat Nat)
    (find : Nat → BST Nat Nat → Option Nat) : Bool :=
  match find key tree1 with
  | some v1 => find key (union tree1 tree2) == some v1
  | none => true

/-- Valid BST after union -/
def prop_union_valid (tree1 tree2 : BST Nat Nat)
    (union : BST Nat Nat → BST Nat Nat → BST Nat Nat)
    (valid : BST Nat Nat → Bool) : Bool :=
  boolImplies (valid tree1 && valid tree2) (valid (union tree1 tree2))

end BDTExperiments
