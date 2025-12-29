import Cli
import Basalt.Experiments.BDT.Analysis

open Cli

namespace BDTExperiments

/-- Parse a string to float with error handling -/
def parseFloat (s : String) : IO Float := do
  -- Simple float parser: handles formats like "2.5", "0.3", "10"
  let parts := s.splitOn "."
  match parts with
  | [whole] =>
    match whole.toNat? with
    | some n => pure n.toFloat
    | none => throw (IO.userError s!"Invalid float value: {s}")
  | [whole, frac] =>
    match whole.toNat?, frac.toNat? with
    | some w, some f =>
      let wholePart := w.toFloat
      let fracPart := f.toFloat / (10 ^ frac.length).toFloat
      pure (wholePart + fracPart)
    | _, _ => throw (IO.userError s!"Invalid float value: {s}")
  | _ => throw (IO.userError s!"Invalid float value: {s}")

/-- Run BDT experiments with specified hyperparameters -/
def runCmd (p : Parsed) : IO UInt32 := do
  let alpha0Str := p.flag! "alpha0" |>.as! String
  let t0Str := p.flag! "t0" |>.as! String
  let t2Str := p.flag! "t2" |>.as! String
  let decayStr := p.flag! "decay" |>.as! String
  let maxTests := p.flag? "max-tests" |>.map (·.as! Nat) |>.getD 1000

  let alpha0 ← parseFloat alpha0Str
  let t0 ← parseFloat t0Str
  let t2 ← parseFloat t2Str
  let decay ← parseFloat decayStr

  IO.println "Running BDT experiment..."
  IO.println s!"Parameters: α₀={alpha0}, t₀={t0}, t₂={t2}, d={decay}"
  let result ← runSingleExperiment alpha0 t0 t2 decay maxTests
  let summary := summarizeExperiment result
  printExperimentSummary summary
  return 0

/-- Main BDT experiments command -/
def bdtCmd : Cmd := `[Cli|
  bdt_experiments VIA runCmd; ["0.1.0"]
  "Boltzmann Decay Tuning experiments for BST bug detection.

This tool measures the impact of BDT hyperparameters on property-based testing
effectiveness. It tests 9 BST implementations (1 correct + 8 buggy) against 11
properties to measure bug-catching ability.

Hyperparameters:
  α₀ (alpha0): Initial energy level
  t₀ (t0):     Weight for leaves (arity-0 constructors)
  t₂ (t2):     Weight for nodes (arity-2 constructors)
  d (decay):   Decay factor"

  FLAGS:
    "alpha0" : String;     "Initial energy level α₀ (required)"
    "t0" : String;         "Weight for arity-0 constructors (leaves) (required)"
    "t2" : String;         "Weight for arity-2 constructors (nodes) (required)"
    "decay" : String;      "Decay factor d (required)"
    "max-tests" : Nat;    "Maximum number of tests per property (default: 1000)"

  EXTENSIONS:
    author "Ernest Ng, Harrison Goldstein"
]

end BDTExperiments

/-- Main entry point -/
def main (args : List String) : IO UInt32 :=
  BDTExperiments.bdtCmd.validate args
