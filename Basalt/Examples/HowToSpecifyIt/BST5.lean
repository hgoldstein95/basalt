import Basalt.Examples.HowToSpecifyIt.BST

namespace HowToSpecifyIt.BST5

open BST

variable {k v : Type} [Ord k]

def nil : BST k v := leaf

def insert (key : k) (val : v) : BST k v → BST k v
  | Leaf => branch Leaf key val Leaf
  | Branch l k' v' r =>
    match compare key k' with
    | .lt => branch (insert key val l) k' v' r
    | .gt => branch l k' v' (insert key val r)
    | .eq => branch l k' val r

def join : BST k v → BST k v → BST k v
  | Leaf, r => r
  | l, Leaf => l
  | Branch l k v r, Branch l' k' v' r' =>
    branch l k v (branch (join r l') k' v' r')

/-- Bug 5: Key comparisons reversed in `delete`;
    only works correctly at the root of the tree -/
def delete (key : k) : BST k v → BST k v
  | Leaf => Leaf
  | Branch l k' v' r =>
    match compare key k' with
    | .gt => branch (delete key l) k' v' r  -- Bug: gt should go right, not left
    | .lt => branch l k' v' (delete key r)  -- Bug: lt should go left, not right
    | .eq => join l r

def below (key : k) : BST k v → BST k v
  | Leaf => Leaf
  | Branch l k' v r =>
    match compare key k' with
    | .lt | .eq => below key l
    | .gt => branch l k' v (below key r)

def above (key : k) : BST k v → BST k v
  | Leaf => Leaf
  | Branch l k' v r =>
    match compare key k' with
    | .gt | .eq => above key r
    | .lt => branch (above key l) k' v r

def union : BST k v → BST k v → BST k v
  | Leaf, r => r
  | l, Leaf => l
  | Branch l k v r, t =>
    branch (union l (below k t)) k v (union r (above k t))

def insertions : BST k v → List (k × v)
  | Leaf => []
  | Branch l k v r => (k, v) :: insertions l ++ insertions r

end HowToSpecifyIt.BST5
