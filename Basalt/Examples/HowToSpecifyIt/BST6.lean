import Basalt.Examples.HowToSpecifyIt.BST

namespace HowToSpecifyIt.BST6

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

/-- Bug 6: `union` wrongly assumes that all the keys in the first argument
    precede those in the second. -/
def union : BST k v → BST k v → BST k v
  | Leaf, r => r
  | l, Leaf => l
  | Branch l k v r, Branch l' k' v' r' =>
    branch l k v (branch (union r l') k' v' r')  -- Bug: doesn't use below/above

def delete (key : k) : BST k v → BST k v
  | Leaf => Leaf
  | Branch l k' v' r =>
    match compare key k' with
    | .lt => branch (delete key l) k' v' r
    | .gt => branch l k' v' (delete key r)
    | .eq => union l r

def insertions : BST k v → List (k × v)
  | Leaf => []
  | Branch l k v r => (k, v) :: insertions l ++ insertions r

end HowToSpecifyIt.BST6
