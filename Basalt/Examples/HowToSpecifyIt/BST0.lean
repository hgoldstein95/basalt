import Basalt.Examples.HowToSpecifyIt.BST

namespace HowToSpecifyIt

open BST

variable {k v : Type} [Ord k]

/-- The empty BST -/
def nil : BST k v := leaf

/-- Insert a key-value pair into the BST -/
def insert (key : k) (val : v) : BST k v → BST k v
  | Leaf => branch leaf key val leaf
  | Branch l k' v' r =>
    match compare key k' with
    | .lt => branch (insert key val l) k' v' r
    | .gt => branch l k' v' (insert key val r)
    | .eq => branch l k' val r

/-- Join two BSTs (helper for delete) -/
def join : BST k v → BST k v → BST k v
  | Leaf, r => r
  | l, Leaf => l
  | Branch l k v r, Branch l' k' v' r' =>
    branch l k v (branch (join r l') k' v' r')

/-- Delete a key from the BST -/
def delete (key : k) : BST k v → BST k v
  | Leaf => Leaf
  | Branch l k' v' r =>
    match compare key k' with
    | .lt => branch (delete key l) k' v' r
    | .gt => branch l k' v' (delete key r)
    | .eq => join l r

/-- Get all elements below a given key -/
def below (key : k) : BST k v → BST k v
  | Leaf => Leaf
  | Branch l k' v r =>
    match compare key k' with
    | .lt | .eq => below key l
    | .gt => branch l k' v (below key r)

/-- Get all elements above a given key -/
def above (key : k) : BST k v → BST k v
  | Leaf => Leaf
  | Branch l k' v r =>
    match compare key k' with
    | .gt | .eq => above key r
    | .lt => branch (above key l) k' v r

/-- Union of two BSTs (left has priority for duplicate keys) -/
def union : BST k v → BST k v → BST k v
  | Leaf, r => r
  | l, Leaf => l
  | Branch l k v r, t =>
    branch (union l (below k t)) k v (union r (above k t))

/-- Get a list of insertions that would build the tree -/
def insertions : BST k v → List (k × v)
  | Leaf => []
  | Branch l k v r => (k, v) :: insertions l ++ insertions r

end HowToSpecifyIt
