import Basalt.Experiments.BDT.Analysis

namespace BDTExperiments

/-- Main entry point for BDT experiments -/
def main (args : List String) : IO Unit := do
  match args with
  | ["quick"] => do
      IO.println "Running quick sweep (4 configurations, 100 tests each)..."
      let results ← runQuickSweep 100
      analyzeSweep results

  | ["full"] => do
      IO.println "Running full sweep (144 configurations, 1000 tests each)..."
      IO.println "WARNING: This will take a long time!"
      let results ← runFullSweep 1000
      analyzeSweep results
      exportToCSV results "bdt_full_sweep_results.csv"

  | ["default"] => do
      IO.println "Running experiment with default parameters..."
      let result ← runSingleExperiment 2.0 1.0 1.0 0.5 1000
      let summary := summarizeExperiment result
      printExperimentSummary summary

  | _ => printUsage

where
  printUsage : IO Unit := do
    IO.println "Usage:"
    IO.println "  lake exe bdt_experiments quick"
    IO.println "    Run a quick sweep with 4 hyperparameter configurations"
    IO.println ""
    IO.println "  lake exe bdt_experiments full"
    IO.println "    Run a full sweep with 144 hyperparameter configurations"
    IO.println ""
    IO.println "  lake exe bdt_experiments default"
    IO.println "    Test with default hyperparameters (α₀=2.0, t₀=1.0, t₂=1.0, d=0.5)"

end BDTExperiments

-- Entry point for the executable
def main := BDTExperiments.main
