import Basalt
import Basalt.Examples.HowToSpecifyIt.BST
import Basalt.Experiments.BDT.BSTGenerator

namespace BDTExperiments

open BST

/-- Generate a random Nat in range [0, 100] -/
def genTestNat : Gen Nat := RandomChoice.choose 0 100 (by omega)

/-- Boolean implication: A → B is equivalent to ¬A ∨ B -/
def boolImplies (a b : Bool) : Bool := !a || b

/-- After inserting a key-value pair, find should return that value -/
def prop_insert_find (tree : BST Nat Nat)
    (insert : Nat → Nat → BST Nat Nat → BST Nat Nat)
    (find : Nat → BST Nat Nat → Option Nat) : Gen Bool := do
  let key ← genTestNat
  let val ← genTestNat
  return find key (insert key val tree) == some val

/-- Inserting twice with the same key should keep the second value -/
def prop_insert_insert (tree : BST Nat Nat)
    (insert : Nat → Nat → BST Nat Nat → BST Nat Nat)
    (find : Nat → BST Nat Nat → Option Nat) : Gen Bool := do
  let key ← genTestNat
  let val1 ← genTestNat
  let val2 ← genTestNat
  return find key (insert key val2 (insert key val1 tree)) == some val2

/-- After deleting a key, find should return none -/
def prop_delete_find (tree : BST Nat Nat)
    (delete : Nat → BST Nat Nat → BST Nat Nat)
    (find : Nat → BST Nat Nat → Option Nat) : Gen Bool := do
  let key ← genTestNat
  return find key (delete key tree) == none

/-- The size should increase by at most 1 after insert -/
def prop_insert_size (tree : BST Nat Nat)
    (insert : Nat → Nat → BST Nat Nat → BST Nat Nat)
    (size : BST Nat Nat → Nat) : Gen Bool := do
  let key ← genTestNat
  let val ← genTestNat
  let newSize := size (insert key val tree)
  let oldSize := size tree
  return newSize == oldSize || newSize == oldSize + 1

/-- The size should decrease by at most 1 after delete -/
def prop_delete_size (tree : BST Nat Nat)
    (delete : Nat → BST Nat Nat → BST Nat Nat)
    (size : BST Nat Nat → Nat) : Gen Bool := do
  let key ← genTestNat
  let newSize := size (delete key tree)
  let oldSize := size tree
  return newSize == oldSize || newSize == oldSize - 1

/-- Valid BST after insert -/
def prop_insert_valid (tree : BST Nat Nat)
    (insert : Nat → Nat → BST Nat Nat → BST Nat Nat)
    (valid : BST Nat Nat → Bool) : Gen Bool := do
  let key ← genTestNat
  let val ← genTestNat
  return boolImplies (valid tree) (valid (insert key val tree))

/-- Valid BST after delete -/
def prop_delete_valid (tree : BST Nat Nat)
    (delete : Nat → BST Nat Nat → BST Nat Nat)
    (valid : BST Nat Nat → Bool) : Gen Bool := do
  let key ← genTestNat
  return boolImplies (valid tree) (valid (delete key tree))

/-- Keys in toList should be sorted -/
def prop_toList_sorted (tree : BST Nat Nat)
    (toList : BST Nat Nat → List (Nat × Nat)) : Gen Bool := do
  let keys := (toList tree).map (·.1)
  return keys == keys.mergeSort (fun a b => compare a b == .lt)

/-- Union should contain all keys from both trees -/
def prop_union_contains (tree1 : BST Nat Nat) (params : BDTParams)
    (union : BST Nat Nat → BST Nat Nat → BST Nat Nat)
    (find : Nat → BST Nat Nat → Option Nat) : Gen Bool := do
  let tree2 ← BDTExperiments.genBST params
  let key ← genTestNat
  let result := union tree1 tree2
  match find key tree1, find key tree2 with
  | some _, _ => return find key result != none
  | none, some _ => return find key result != none
  | none, none => return true

/-- Union should prefer left tree for duplicate keys -/
def prop_union_left_priority (tree1 : BST Nat Nat) (params : BDTParams)
    (union : BST Nat Nat → BST Nat Nat → BST Nat Nat)
    (find : Nat → BST Nat Nat → Option Nat) : Gen Bool := do
  let tree2 ← BDTExperiments.genBST params
  let key ← genTestNat
  match find key tree1 with
  | some v1 => return find key (union tree1 tree2) == some v1
  | none => return true

/-- Valid BST after union -/
def prop_union_valid (tree1 : BST Nat Nat) (params : BDTParams)
    (union : BST Nat Nat → BST Nat Nat → BST Nat Nat)
    (valid : BST Nat Nat → Bool) : Gen Bool := do
  let tree2 ← BDTExperiments.genBST params
  return boolImplies (valid tree1 && valid tree2) (valid (union tree1 tree2))

end BDTExperiments
