import Basalt.Examples.HowToSpecifyIt.BST

namespace HowToSpecifyIt.BST8

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

/-- Bug 8: `union` works correctly, except that when both trees contain the
    same key, the left argument does not always take priority -/
partial def union : BST k v → BST k v → BST k v
  | Leaf, r => r
  | l, Leaf => l
  | Branch l k v r, Branch l' k' v' r' =>
    match compare k k' with
    | .eq => branch (union l l') k v (union r r')
    | .lt => branch (union l (below k l')) k v (union r (branch (above k l') k' v' r'))
      -- Bug: when k < k', the right subtree contains k' from the right tree,
      -- but if the left tree's right subtree also contains k', the priority is wrong
    | .gt => union (branch l' k' v' r) (branch l k v r)

def insertions : BST k v → List (k × v)
  | Leaf => []
  | Branch l k v r => (k, v) :: insertions l ++ insertions r

end HowToSpecifyIt.BST8
