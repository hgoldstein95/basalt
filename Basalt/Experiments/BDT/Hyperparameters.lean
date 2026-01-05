import Basalt

open RandomChoice

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

/-- Generates a rational number within
    in the unit interval `[0, 1]` (inclusive )-/
def genUnitIntervalRat (denominator : Nat) : Gen Rat := do
  let numerator ← choose 0 denominator (by simp)
  return (numerator / denominator)

/-- Generates a set of BDT parameters.
    (Note: this is currently unused,
    the idea being we can tune this generator later and sample lots
    of different parameters for an ensemble approach to generation)  -/
def genBDTParams : Gen BDTParams := do
  let decay ← genUnitIntervalRat 10
  let t0 ← genUnitIntervalRat 10
  let t1 ← genUnitIntervalRat 10
  let t2 ← genUnitIntervalRat 10

  -- To generate a value for α_0, we first generate a base value
  -- then multiply it by some factor between 1 & 5.
  -- This allows us to generate values for α_0 ∈ [0, 5]
  let alpha0_base ← genUnitIntervalRat 10
  let multiplier ← choose 1 5 (by omega)
  return { alpha0 := alpha0_base * multiplier, t0, t1, t2, decay }
