import Basalt.Examples.HowToSpecifyIt.BST

namespace HowToSpecifyIt.BST7

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

def delete (key : k) : BST k v → BST k v
  | Leaf => Leaf
  | Branch l k' v' r =>
    match compare key k' with
    | .lt => branch (delete key l) k' v' r
    | .gt => branch l k' v' (delete key r)
    | .eq => join l r

/-- Bug 7: `union` wrongly assumes that if the key at the root of `t` is
    smaller than the key at the root of `t'`, then all the keys in `t` will
    be smaller than the key at the root of `t'`. -/
partial def union : BST k v → BST k v → BST k v
  | Leaf, r => r
  | l, Leaf => l
  | Branch l k v r, Branch l' k' v' r' =>
    match compare k k' with
    | .eq => branch (union l l') k v (union r r')
    | .lt => branch l k v (branch (union r l') k' v' r)  -- Bug: assumes all of r < k'
    | .gt => union (branch l' k' v' r) (branch l k v r)

def insertions : BST k v → List (k × v)
  | Leaf => []
  | Branch l k v r => (k, v) :: insertions l ++ insertions r

end HowToSpecifyIt.BST7
