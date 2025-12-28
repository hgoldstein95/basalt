import Basalt
import Basalt.Examples.HowToSpecifyIt.BST

open RandomChoice

namespace BDTExperiments

open BST

/-- Hyperparameters for Boltzmann Decay Tuning -/
structure BDTParams where
  /-- Initial "energy" level -/
  alpha0 : Float
  /-- Weight for arity-0 constructors (leaves) -/
  t0 : Float
  /-- Weight for arity-2 constructors (nodes) -/
  t2 : Float
  /-- Decay factor for alpha -/
  decay : Float
  deriving Repr, Inhabited

/-- Default BDT parameters (reasonable starting point) -/
def BDTParams.default : BDTParams :=
  { alpha0 := 2.0
  , t0 := 1.0
  , t2 := 1.0
  , decay := 0.5 }

/-- Generate a random BST using Boltzmann Decay Tuning

    This follows the approach from the paper:
    - Thread alpha through the generation process
    - Use weights t_k * alpha^k for constructors of arity k
    - Decay alpha by the decay factor at each recursive step
-/
partial def genBSTWithBDT (params : BDTParams) (lo hi : Nat) : Gen (BST Nat Nat) :=
  let rec go (alpha : Float) (lo hi : Nat) : Gen (BST Nat Nat) := do
    if h : lo > hi then
      -- No valid keys in range, must return leaf
      pure Leaf
    else
      -- Calculate weights for leaf (arity 0) and node (arity 2)
      let leafWeight := params.t0
      let nodeWeight := params.t2 * alpha * alpha

      -- Simple weighted choice using randomness
      -- Generate a random float between 0 and totalWeight, then check if it's < leafWeight
      let totalWeight := leafWeight + nodeWeight
      if totalWeight <= 0 then
        pure Leaf  -- Defensive: if weights are invalid, return leaf
      else
        -- Generate random value in [0, totalWeight) conceptually
        -- We'll use choose to pick between 0 and 1000, then scale
        let randomVal ← choose 0 1000 (by omega)
        let threshold := ((leafWeight / totalWeight) * 1000).toUInt64.toNat

        if randomVal < threshold then
          pure Leaf
        else do
          -- Choose a key in the valid range
          have hle : lo ≤ hi := Nat.le_of_not_gt h
          let k ← choose lo hi hle
          -- Generate left and right subtrees with decayed alpha
          let newAlpha := alpha * params.decay
          let left ← if k > lo then go newAlpha lo (k - 1) else pure Leaf
          let right ← if k < hi then go newAlpha (k + 1) hi else pure Leaf
          -- Return the node with k as both key and value
          pure (Branch left k k right)

  go params.alpha0 lo hi

/-- Generate a random BST with keys in range [0, maxKey] -/
def genBST (params : BDTParams) (maxKey : Nat := 100) : Gen (BST Nat Nat) :=
  genBSTWithBDT params 0 maxKey

end BDTExperiments
