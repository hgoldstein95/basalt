import Basalt.Experiments.BDT.TestHarness
import Basalt.Experiments.BDT.Hyperparameters

namespace BDTExperiments

/-- Summary of an entire experiment run -/
structure ExperimentSummary where
  params : BDTParams
  totalBugsFound : Nat
  bugsFoundPerImpl : List (String × Nat)
  avgTestsToFindBug : Float
  deriving Repr, Inhabited

/-- Compute summary for an experiment result -/
def summarizeExperiment (exp : ExperimentResult) : ExperimentSummary :=
  -- Count bugs found per implementation
  let bugsPerImpl := exp.results.map fun r =>
    let bugsFound := r.propertyResults.map (·.stats) |>.filter (·.bugFound) |>.length
    (r.implName, bugsFound)
  let totalBugs := bugsPerImpl.map (·.2) |>.sum

  let bugStats : List TestStats := exp.results >>= fun r =>
    (r.propertyResults.map (·.stats)).filter (·.bugFound)

  let avgTests := if bugStats.isEmpty then 0.0
    else ((bugStats.map (·.testsUntilFailure.toFloat)).sum) / bugStats.length.toFloat

  { params := exp.params
  , totalBugsFound := totalBugs
  , bugsFoundPerImpl := bugsPerImpl
  , avgTestsToFindBug := avgTests }

/-- Prints a formatted summary of a single experiment -/
def printExperimentSummary (summary : ExperimentSummary) : IO Unit := do
  IO.println "--- Experiment Summary ---"
  IO.println s!"Parameters:"
  IO.println s!"  α₀ = {summary.params.alpha0}"
  IO.println s!"  t₀ = {summary.params.t0}"
  IO.println s!"  t₂ = {summary.params.t2}"
  IO.println s!"  decay = {summary.params.decay}"
  IO.println s!"\nTotal Bugs Found: {summary.totalBugsFound}"
  IO.println s!"Average Tests to Find Bug: {summary.avgTestsToFindBug}"
  IO.println "\nBugs per Implementation:"
  for (implName, bugCount) in summary.bugsFoundPerImpl do
    IO.println s!"  {implName}: {bugCount}"

end BDTExperiments
