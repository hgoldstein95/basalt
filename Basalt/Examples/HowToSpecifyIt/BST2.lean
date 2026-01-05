import Basalt.Examples.HowToSpecifyIt.BST

namespace HowToSpecifyIt.BST2

open BST

variable {k v : Type} [Ord k]

def nil : BST k v := leaf

/-- Bug 2: `insert` fails to recognize and update an existing key,
    inserting a duplicate entry instead -/
def insert (key : k) (val : v) : BST k v → BST k v
  | Leaf => branch Leaf key val Leaf
  | Branch l k' v' r =>
    match compare key k' with
    | .lt => branch (insert key val l) k' v' r
    | _ => branch l k' v' (insert key val r)  -- Missing .eq case!

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

def union : BST k v → BST k v → BST k v
  | Leaf, r => r
  | l, Leaf => l
  | Branch l k v r, t =>
    branch (union l (below k t)) k v (union r (above k t))

def insertions : BST k v → List (k × v)
  | Leaf => []
  | Branch l k v r => (k, v) :: insertions l ++ insertions r

end HowToSpecifyIt.BST2
