import Basalt
import Basalt.Examples.HowToSpecifyIt.BST

open RandomChoice

namespace BDTExperiments

open BST

/-- Hyperparameters for Boltzmann Decay Tuning -/
structure BDTParams where
  /-- Initial "energy" level -/
  alpha0 : Rat
  /-- Weight for arity-0 constructors (leaves) -/
  t0 : Rat
  /-- Weight for arity-2 constructors (nodes) -/
  t2 : Rat
  /-- Decay factor for alpha -/
  decay : Rat
  deriving Repr, Inhabited

/-- Default BDT parameters -/
def BDTParams.default : BDTParams :=
  { alpha0 := 2.0
  , t0 := 1.0
  , t2 := 1.0
  , decay := 0.5 }

/-- Generates a random BST using Boltzmann Decay Tuning (BDT) -/
partial def genBSTWithBDT (params : BDTParams) (lo hi : Nat) : Gen (BST Nat Nat) :=
  let rec go (α : Rat) (lo hi : Nat) : Gen (BST Nat Nat) := do
    if h : lo > hi then
      pure Leaf
    else
      let leafWeight := params.t0
      let nodeWeight := params.t2 * α * α

      let bias := leafWeight / (leafWeight + nodeWeight)
      if (← RandomChoice.coin bias) then
        pure Leaf
      else do
        -- We use `Nat.le_of_not_gt` to avoid the overhead of calling `omega`
        -- from influencing measurements
        have hle : lo ≤ hi := Nat.le_of_not_gt h
        let k ← choose lo hi hle
        -- Generate left and right subtrees with decayed α
        let α' := α * params.decay
        let left ← if k > lo then go α' lo (k - 1) else pure Leaf
        let right ← if k < hi then go α' (k + 1) hi else pure Leaf
        -- Return the node with `k` as both the key & value (for simplicity)
        pure (Branch left k k right)

  go params.alpha0 lo hi

/-- Generate a random BST with keys in range [0, maxKey] -/
def genBST (params : BDTParams) (maxKey : Nat := 100) : Gen (BST Nat Nat) :=
  genBSTWithBDT params 0 maxKey

end BDTExperiments
