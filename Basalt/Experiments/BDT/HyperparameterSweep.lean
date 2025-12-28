import Basalt.Experiments.BDT.BSTGenerator
import Basalt.Experiments.BDT.TestHarness

namespace BDTExperiments

/-- Result from a single hyperparameter configuration -/
structure ExperimentResult where
  params : BDTParams
  results : List ImplTestResult
  deriving Repr

/-- Generate a grid of hyperparameter values to test -/
def generateParamGrid : List BDTParams :=
  let alpha0Values := [0.5, 1.0, 2.0, 4.0]
  let t0Values := [0.5, 1.0, 2.0]
  let t2Values := [0.5, 1.0, 2.0]
  let decayValues := [0.3, 0.5, 0.7, 0.9]

  alpha0Values >>= fun alpha0 =>
    t0Values >>= fun t0 =>
      t2Values >>= fun t2 =>
        decayValues.map fun decay =>
          { alpha0, t0, t2, decay }

/-- Run experiments for all hyperparameter configurations -/
def runFullSweep (maxTests : Nat := 1000) : IO (List ExperimentResult) := do
  let grid := generateParamGrid
  IO.println s!"Running {grid.length} experiments..."

  let mut allResults := []
  for _h : i in [:grid.length] do
    let params := grid[i]!
    let sep := String.pushn "" '=' 60
    IO.println s!"\n{sep}"
    IO.println s!"Experiment {i+1}/{grid.length}"
    IO.println s!"Parameters: α₀={params.alpha0}, t₀={params.t0}, t₂={params.t2}, d={params.decay}"
    IO.println s!"{sep}"

    let results ← testAllImplementations params maxTests
    allResults := { params, results } :: allResults

  return allResults.reverse

/-- Run a small experiment with just a few parameter settings -/
def runQuickSweep (maxTests : Nat := 100) : IO (List ExperimentResult) := do
  let quickGrid : List BDTParams := [
    { alpha0 := 1.0, t0 := 1.0, t2 := 1.0, decay := 0.5 },  -- Balanced
    { alpha0 := 4.0, t0 := 0.5, t2 := 2.0, decay := 0.7 },  -- Favors nodes
    { alpha0 := 0.5, t0 := 2.0, t2 := 0.5, decay := 0.3 },  -- Favors leaves
    { alpha0 := 2.0, t0 := 1.0, t2 := 1.0, decay := 0.9 }   -- Slow decay
  ]

  IO.println s!"Running {quickGrid.length} quick experiments..."

  let mut allResults := []
  for _h : i in [:quickGrid.length] do
    let params := quickGrid[i]!
    let sep := String.pushn "" '=' 60
    IO.println s!"\n{sep}"
    IO.println s!"Quick Experiment {i+1}/{quickGrid.length}"
    IO.println s!"Parameters: α₀={params.alpha0}, t₀={params.t0}, t₂={params.t2}, d={params.decay}"
    IO.println s!"{sep}"

    let results ← testAllImplementations params maxTests
    allResults := { params, results } :: allResults

  return allResults.reverse

/-- Test a single specific hyperparameter configuration -/
def runSingleExperiment (alpha0 t0 t2 decay : Float) (maxTests : Nat := 1000)
    : IO ExperimentResult := do
  let params : BDTParams := { alpha0, t0, t2, decay }
  IO.println s!"Running single experiment with parameters:"
  IO.println s!"  α₀={params.alpha0}, t₀={params.t0}, t₂={params.t2}, d={params.decay}"

  let results ← testAllImplementations params maxTests
  return { params, results }

end BDTExperiments
