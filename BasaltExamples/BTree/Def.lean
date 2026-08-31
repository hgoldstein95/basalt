/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
/-!
# B-Trees (definitions)

The B-tree data type, the validity predicate `Tree.IsBTree` — a tree of order `t` whose keys lie in
`[lo, hi]` and whose leaves are all at depth `h` — and insertion. Insertion is *bottom-up*: the key
goes into the leaf the search reaches and a node that overflows splits, so a tree that inserting `x`
splits is one whose leaf on `x`'s path is already full (`Tree.SplitsOn`).
-/

namespace BTree

/-- A B-tree node: a list of keys and a list of subtrees. A leaf has no subtrees; the invariant
relating the two lengths is `Forest`, not the type. -/
inductive Tree where
  | mk : List Int → List Tree → Tree
deriving Repr

/-! ## Validity -/

/-- `Gapped g lo hi ks`: the keys `ks` are strictly increasing inside `[lo, hi]`, and every interval
they cut out of `[lo, hi]` — before the first key, between two keys, after the last — holds at least
`g` values. At `g = 0` this is exactly "sorted, and inside `[lo, hi]`". -/
def Gapped (g : Nat) : Int → Int → List Int → Prop
  | lo, hi, [] => lo + g ≤ hi + 1
  | lo, hi, k :: ks => lo + g ≤ k ∧ Gapped g (k + 1) hi ks

/-- `Forest P lo hi ks cs`: there is one more child than there are keys, and the `i`-th child
satisfies `P` on the `i`-th interval that `ks` cuts out of `[lo, hi]`. -/
def Forest (P : Int → Int → Tree → Prop) : Int → Int → List Int → List Tree → Prop
  | lo, hi, [], [c] => P lo hi c
  | lo, hi, k :: ks, c :: cs => P lo (k - 1) c ∧ Forest P (k + 1) hi ks cs
  | _, _, _, _ => False

/-- `Tree.IsBTreeAt t kmin h lo hi tr`: `tr` is a B-tree of order `t` (minimum degree) with all keys
in `[lo, hi]` and all leaves at depth `h`. Every node holds at most `2 * t - 1` keys and has one
more child than it has keys; every node but the root holds at least `t - 1` keys, the root at least
`kmin`. -/
def Tree.IsBTreeAt (t kmin : Nat) : Nat → Int → Int → Tree → Prop
  | 0, lo, hi, ⟨ks, cs⟩ =>
      cs = [] ∧ kmin ≤ ks.length ∧ ks.length ≤ 2 * t - 1 ∧ Gapped 0 lo hi ks
  | h + 1, lo, hi, ⟨ks, cs⟩ =>
      kmin ≤ ks.length ∧ ks.length ≤ 2 * t - 1 ∧ Gapped 0 lo hi ks ∧
      Forest (fun a b c => Tree.IsBTreeAt t (t - 1) h a b c) lo hi ks cs

/-- The root of a nonempty B-tree holds at least one key; a tree of height `0` may be empty. -/
def Tree.IsBTree (t h : Nat) (lo hi : Int) (tr : Tree) : Prop :=
  Tree.IsBTreeAt t (min 1 h) h lo hi tr

/-! ## Insertion -/

/-- The subtree the search for `x` descends into: the child whose key interval contains `x`. -/
def childFor (x : Int) : List Int → List Tree → Option Tree
  | [], [c] => some c
  | k :: ks, c :: cs => if x < k then some c else childFor x ks cs
  | _, _ => none

/-- The leaf the search for `x` reaches in a tree whose leaves are at depth `h`. -/
def leafFor (x : Int) : Nat → Tree → Option Tree
  | 0, tr => some tr
  | h + 1, ⟨ks, cs⟩ => (childFor x ks cs).bind (leafFor x h)

/-- Inserts `x` into a sorted key list, ignoring a key that is already present. -/
def insSorted (x : Int) : List Int → List Int
  | [] => [x]
  | k :: ks => if x < k then x :: k :: ks else if k < x then k :: insSorted x ks else k :: ks

/-- Splits an overfull node into its lower half, its median key, and its upper half. -/
def splitNode (t : Nat) : Tree → Tree × Int × Tree
  | ⟨ks, cs⟩ => (⟨ks.take (t - 1), cs.take t⟩, ks.getD (t - 1) 0, ⟨ks.drop t, cs.drop t⟩)

/-- The result of inserting into a subtree: either the subtree absorbed the key, or it was full and
split, handing its median key up to its parent. -/
inductive Ins where
  | keep : Tree → Ins
  | split : Tree → Int → Tree → Ins

/-- Splits a node if the key it just took made it overfull. -/
def mkNode (t : Nat) (tr : Tree) : Ins :=
  match tr with
  | ⟨ks, _⟩ =>
    if ks.length ≤ 2 * t - 1 then .keep tr
    else let (l, k, r) := splitNode t tr; .split l k r

mutual

/-- Inserts `x` below the keys `ks` and children `cs` of one node, absorbing a child's split into
the node's own keys. -/
def insChildren (t : Nat) (x : Int) : Nat → List Int → List Tree → List Int × List Tree
  | h, [], [c] =>
    match insertAt t x h c with
    | .keep c' => ([], [c'])
    | .split l k r => ([k], [l, r])
  | h, k :: ks, c :: cs =>
    if x < k then
      match insertAt t x h c with
      | .keep c' => (k :: ks, c' :: cs)
      | .split l m r => (m :: k :: ks, l :: r :: cs)
    else
      let (ks', cs') := insChildren t x h ks cs
      (k :: ks', c :: cs')
  | _, _, _ => ([], [])

/-- Bottom-up insertion: `x` goes into the leaf the search reaches, and a node that overflows splits
and hands its median key to its parent. -/
def insertAt (t : Nat) (x : Int) : Nat → Tree → Ins
  | 0, ⟨ks, _⟩ => mkNode t ⟨insSorted x ks, []⟩
  | h + 1, ⟨ks, cs⟩ => let (ks', cs') := insChildren t x h ks cs; mkNode t ⟨ks', cs'⟩

end

/-- Inserts `x` into a whole tree: a root that splits becomes the two halves of a new root one
level taller. -/
def insert (t : Nat) (x : Int) (h : Nat) (tr : Tree) : Tree :=
  match insertAt t x h tr with
  | .keep tr' => tr'
  | .split l k r => ⟨[k], [l, r]⟩

/-- `Tree.SplitsOn t x h tr`: the search for `x` walks all `h` levels down `tr` without meeting `x`,
and the leaf it reaches is full — the trees in which inserting `x` splits a node
(`Tree.splitsOn_iff`). -/
def Tree.SplitsOn (t : Nat) (x : Int) : Nat → Tree → Prop
  | 0, ⟨ks, _⟩ => x ∉ ks ∧ ks.length = 2 * t - 1
  | h + 1, ⟨ks, cs⟩ => x ∉ ks ∧ ∃ c, childFor x ks cs = some c ∧ Tree.SplitsOn t x h c

/-- The search for `x` meets no key equal to `x` on its way down. -/
def Tree.PathMisses (x : Int) : Nat → Tree → Prop
  | 0, ⟨ks, _⟩ => x ∉ ks
  | h + 1, ⟨ks, cs⟩ => x ∉ ks ∧ ∃ c, childFor x ks cs = some c ∧ Tree.PathMisses x h c

/-- `x` is one of the keys of `tr`, whose leaves are at depth `h`. -/
def Tree.HasKey (x : Int) : Nat → Tree → Prop
  | 0, ⟨ks, _⟩ => x ∈ ks
  | h + 1, ⟨ks, cs⟩ => x ∈ ks ∨ ∃ c ∈ cs, Tree.HasKey x h c

end BTree
