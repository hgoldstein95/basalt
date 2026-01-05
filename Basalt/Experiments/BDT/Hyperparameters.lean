import Basalt


/-- Hyperparameters for Boltzmann Decay Tuning -/
structure BDTParams where
  /-- Initial "energy" level -/
  alpha0 : Rat

  /-- Weight for arity-0 constructors -/
  t0 : Rat

  /-- Weight for arity-1 constructors -/
  t1: Rat

  /-- Weight for arity-2 constructors -/
  t2 : Rat

  /-- Decay factor for alpha -/
  decay : Rat
  deriving Repr, Inhabited


/-- Default BDT parameters for BST -/
def BDTParams.BSTdefault : BDTParams :=
  { alpha0 := 2.0
  , t0 := 1.0
  , t1 := 0.0
  , t2 := 1.0
  , decay := 0.5 }
