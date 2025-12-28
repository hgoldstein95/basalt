import Basalt.Examples.HowToSpecifyIt.BST

namespace BDTExperiments

open BST

variable {k v : Type} [Ord k] [BEq k] [BEq v]

/-- Property: After inserting a key-value pair, find should return that value -/
def prop_insert_find (tree : BST k v) (key : k) (val : v)
    (insert : k → v → BST k v → BST k v)
    (find : k → BST k v → Option v) : Bool :=
  find key (insert key val tree) == some val

/-- Property: After deleting a key, find should return none -/
def prop_delete_find (tree : BST k v) (key : k)
    (delete : k → BST k v → BST k v)
    (find : k → BST k v → Option v) : Bool :=
  find key (delete key tree) == none

/-- Property: Inserting twice with the same key should keep the second value -/
def prop_insert_insert (tree : BST k v) (key : k) (val1 val2 : v)
    (insert : k → v → BST k v → BST k v)
    (find : k → BST k v → Option v) : Bool :=
  find key (insert key val2 (insert key val1 tree)) == some val2

/-- Property: Deleting a key from an empty tree should return empty -/
def prop_delete_empty (key : k)
    (delete : k → BST k v → BST k v)
    (nil : BST k v) : Bool :=
  delete key nil == nil

/-- Property: The size should increase by at most 1 after insert -/
def prop_insert_size (tree : BST k v) (key : k) (val : v)
    (insert : k → v → BST k v → BST k v)
    (size : BST k v → Nat) : Bool :=
  let newSize := size (insert key val tree)
  let oldSize := size tree
  newSize == oldSize || newSize == oldSize + 1

/-- Property: The size should decrease by at most 1 after delete -/
def prop_delete_size (tree : BST k v) (key : k)
    (delete : k → BST k v → BST k v)
    (size : BST k v → Nat) : Bool :=
  let newSize := size (delete key tree)
  let oldSize := size tree
  newSize == oldSize || newSize == oldSize - 1

/-- Property: Keys in toList should be sorted -/
def prop_toList_sorted (tree : BST k v)
    (toList : BST k v → List (k × v)) : Bool :=
  let keys := (toList tree).map (·.1)
  keys == keys.mergeSort (fun a b => compare a b == .lt)

/-- Property: Union should contain all keys from both trees -/
def prop_union_contains (tree1 tree2 : BST k v) (key : k)
    (union : BST k v → BST k v → BST k v)
    (find : k → BST k v → Option v) : Bool :=
  let result := union tree1 tree2
  match find key tree1, find key tree2 with
  | some _, _ => find key result != none
  | none, some _ => find key result != none
  | none, none => true

/-- Property: Union should prefer left tree for duplicate keys -/
def prop_union_left_priority (tree1 tree2 : BST k v) (key : k)
    (union : BST k v → BST k v → BST k v)
    (find : k → BST k v → Option v) : Bool :=
  match find key tree1 with
  | some v1 => find key (union tree1 tree2) == some v1
  | none => true

/-- Property: Valid BST after insert -/
def prop_insert_valid (tree : BST k v) (key : k) (val : v)
    (insert : k → v → BST k v → BST k v)
    (valid : BST k v → Bool) : Bool :=
  valid tree → valid (insert key val tree)

/-- Property: Valid BST after delete -/
def prop_delete_valid (tree : BST k v) (key : k)
    (delete : k → BST k v → BST k v)
    (valid : BST k v → Bool) : Bool :=
  valid tree → valid (delete key tree)

/-- Property: Valid BST after union -/
def prop_union_valid (tree1 tree2 : BST k v)
    (union : BST k v → BST k v → BST k v)
    (valid : BST k v → Bool) : Bool :=
  valid tree1 → valid tree2 → valid (union tree1 tree2)

end BDTExperiments
