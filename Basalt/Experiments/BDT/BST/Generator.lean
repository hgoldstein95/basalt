import Basalt
import Basalt.Examples.HowToSpecifyIt.BST
import Basalt.Experiments.BDT.Hyperparameters

open RandomChoice

namespace BDTExperiments

open BST

/-- Generates a random BST using Boltzmann Decay Tuning (BDT) -/
def genBSTWithBDT (α t0 t2 d : Rat) (lo hi : Nat) : Gen (BST Nat Nat) := do
  if h : lo > hi then
    pure .Leaf
  else
    let leafWeight := t0
    let nodeWeight := t2 * α * α
    let bias := leafWeight / (leafWeight + nodeWeight)
    if (← RandomChoice.coin bias) then
      pure Leaf
    else do
      -- We use `Nat.le_of_not_gt` to avoid the overhead of
      -- calling `omega` from influencing benchmarks
      have hle : lo ≤ hi := Nat.le_of_not_gt h
      let k ← choose lo hi hle
      -- Generate left and right subtrees with decayed α
      let α' := α * d
      let left ←
        if k > lo then
          genBSTWithBDT α' t0 t2 d lo (k - 1)
        else
          pure Leaf
      let right ←
        if k < hi then
          genBSTWithBDT α' t0 t2 d (k + 1) hi
        else
          pure Leaf
      -- For simplicity, we use `k` as both the key & value for the node
      pure (.Branch left k k right)
  partial_fixpoint

/-- Generate a random BST with keys in range [0, maxKey] -/
def genBST (params : BDTParams) (maxKey : Nat := 100) : Gen (BST Nat Nat) :=
  let { alpha0 := α, t0, t2, decay := d, t1 := _t1 } := params
  genBSTWithBDT α t0 t2 d 0 maxKey

end BDTExperiments
