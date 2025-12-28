import Basalt
import Basalt.Examples.HowToSpecifyIt.BST

namespace BDTExperiments

open BST

/-- Generate a random Nat in range [0, 100] -/
def genTestNat : Gen Nat := RandomChoice.choose 0 100 (by omega)

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

end BDTExperiments
