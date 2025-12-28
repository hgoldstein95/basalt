import Basalt

/-- Binary Search Tree with keys of type `k` and values of type `v` -/
inductive BST (k v : Type) where
  | Leaf : BST k v
  | Branch : BST k v → k → v → BST k v → BST k v
  deriving BEq, Inhabited, Repr

namespace BST

variable {k v : Type}

/-- Smart constructor for Branch -/
def branch (l : BST k v) (key : k) (val : v) (r : BST k v) : BST k v :=
  Branch l key val r

/-- Smart constructor for Leaf -/
def leaf : BST k v := Leaf

/-- Convert BST to list via in-order traversal -/
def toList [Ord k] : BST k v → List (k × v)
  | Leaf => []
  | Branch l k v r => toList l ++ [(k, v)] ++ toList r

/-- Get all keys from the BST -/
def keys [Ord k] (t : BST k v) : List k :=
  (toList t).map (·.1)

/-- Check if BST is valid (satisfies BST invariant) -/
def valid [Ord k] : BST k v → Bool
  | Leaf => true
  | Branch l k _ r =>
    valid l && valid r
    && (keys l).all (fun x => compare x k == .lt)
    && (keys r).all (fun x => compare k x == .lt)

/-- Find a value by key -/
def find [Ord k] (key : k) : BST k v → Option v
  | Leaf => none
  | Branch l k' val r =>
    match compare key k' with
    | .lt => find key l
    | .gt => find key r
    | .eq => some val

/-- Get the size of the BST -/
def size [Ord k] (t : BST k v) : Nat :=
  (keys t).length

end BST
