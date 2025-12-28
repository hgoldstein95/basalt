import Basalt.Experiments.BDT.HyperparameterSweep

namespace BDTExperiments

/-- Summary statistics for a single implementation across properties -/
structure ImplSummary where
  implName : String
  totalBugsFound : Nat
  avgTestsUntilFailure : Float
  propertiesTested : Nat
  deriving Repr

/-- Compute summary for a single implementation's test results -/
def summarizeImplResult (result : ImplTestResult) : ImplSummary :=
  let stats := result.propertyResults.map (·.stats)
  let bugsFound := stats.filter (·.bugFound) |>.length
  let totalTests := stats.map (·.testsUntilFailure) |>.sum
  let avgTests := (totalTests.toFloat / stats.length.toFloat)

  { implName := result.implName
  , totalBugsFound := bugsFound
  , avgTestsUntilFailure := avgTests
  , propertiesTested := stats.length }

/-- Summary of an entire experiment run -/
structure ExperimentSummary where
  params : BDTParams
  totalBugsFound : Nat
  bugsFoundPerImpl : List (String × Nat)
  avgTestsToFindBug : Float
  deriving Repr, Inhabited

/-- Compute summary for an experiment result -/
def summarizeExperiment (exp : ExperimentResult) : ExperimentSummary :=
  let summaries := exp.results.map summarizeImplResult
  let totalBugs := (summaries.map (·.totalBugsFound)).sum
  let bugsPerImpl := summaries.map (fun s => (s.implName, s.totalBugsFound))

  let bugStats : List TestStats := exp.results >>= fun r =>
    (r.propertyResults.map (·.stats)).filter (·.bugFound)

  let avgTests := if bugStats.isEmpty then 0.0
    else ((bugStats.map (·.testsUntilFailure.toFloat)).sum) / bugStats.length.toFloat

  { params := exp.params
  , totalBugsFound := totalBugs
  , bugsFoundPerImpl := bugsPerImpl
  , avgTestsToFindBug := avgTests }

/-- Print a formatted summary of a single experiment -/
def printExperimentSummary (summary : ExperimentSummary) : IO Unit := do
  IO.println "\n--- Experiment Summary ---"
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

/-- Find the best hyperparameter configuration from a sweep -/
def findBestConfig (results : List ExperimentResult) : Option ExperimentSummary :=
  let summaries := results.map summarizeExperiment
  summaries.foldl (fun best curr =>
    match best with
    | none => some curr
    | some b =>
      if curr.totalBugsFound > b.totalBugsFound then
        some curr
      else if curr.totalBugsFound == b.totalBugsFound &&
              curr.avgTestsToFindBug < b.avgTestsToFindBug then
        some curr
      else
        some b
  ) none

/-- Print analysis of all experiments in a sweep -/
def analyzeSweep (results : List ExperimentResult) : IO Unit := do
  let summaries := results.map summarizeExperiment
  let sep := String.pushn "" '=' 60

  IO.println s!"\n{sep}"
  IO.println "SWEEP ANALYSIS"
  IO.println s!"{sep}\n"

  IO.println s!"Total Experiments Run: {summaries.length}\n"

  -- Print each experiment summary
  for _h : i in [:summaries.length] do
    let summary := summaries[i]!
    IO.println s!"Experiment {i+1}:"
    printExperimentSummary summary
    IO.println ""

  -- Find and print best configuration
  match findBestConfig results with
  | none => IO.println "No valid configurations found"
  | some best => do
    IO.println s!"\n{sep}"
    IO.println "BEST CONFIGURATION:"
    IO.println s!"{sep}"
    printExperimentSummary best

/-- Export results to CSV format for external analysis -/
def exportToCSV (results : List ExperimentResult) (filename : String) : IO Unit := do
  let summaries := results.map summarizeExperiment

  let handle ← IO.FS.Handle.mk filename IO.FS.Mode.write

  -- Write header
  handle.putStrLn "alpha0,t0,t2,decay,totalBugsFound,avgTestsToFindBug"

  -- Write data rows
  for summary in summaries do
    let row := s!"{summary.params.alpha0},{summary.params.t0},{summary.params.t2},{summary.params.decay},{summary.totalBugsFound},{summary.avgTestsToFindBug}"
    handle.putStrLn row

  IO.println s!"Results exported to {filename}"

end BDTExperiments
