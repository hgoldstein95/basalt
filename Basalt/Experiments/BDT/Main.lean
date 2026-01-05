import Batteries.Data.Rat.Float
import Cli
import Basalt.Experiments.BDT.Analysis

open Cli

namespace BDTExperiments

/-- Parse a string to float, throwing an exception if this fails -/
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


/-- Parses a string as a `Rat`, throwing an exception if this fails -/
def parseRational (s : String) : IO Rat := do
  let f ← parseFloat s
  match Float.toRat? f with
  | some r => pure r
  | none => throw (IO.userError s!"Unable to convert float {f} to a rational number")

/-- Extracts the parsed string value for a CLI flag (identified by its `flagName`),
    returning a `default` value if the flag isn't passed -/
def getFlagStrWithDefault (p : Parsed) (flagName : String) (default : String) : String :=
  p.flag? flagName |>.map (·.as! String) |>.getD default

/-- Run BDT experiments with specified hyperparameters -/
def runCmd (p : Parsed) : IO UInt32 := do
  let alpha0Str := p.flag! "alpha0" |>.as! String
  let t0Str := getFlagStrWithDefault p "t0" "0.0"
  let t1Str := getFlagStrWithDefault p "t1" "0.0"
  let t2Str := getFlagStrWithDefault p "t2" "0.0"
  let decayStr := p.flag! "decay" |>.as! String
  let maxTests := p.flag? "max-tests" |>.map (·.as! Nat) |>.getD 1000

  let alpha0 ← parseRational alpha0Str
  let t0 ←  parseRational t0Str
  let t1 ← parseRational t1Str
  let t2 ← parseRational t2Str
  let decay ← parseRational decayStr

  let result ← runSingleExperiment alpha0 t0 t1 t2 decay maxTests
  let summary := summarizeExperiment result
  printExperimentSummary summary
  return 0

/-- Main BDT experiments command -/
def bdtCmd : Cmd := `[Cli|
  bdt_experiments VIA runCmd; ["0.1.0"]
  "Boltzmann Decay Tuning experiments for BST bug detection.

This script tests 9 BST implementations (1 correct + 8 buggy) against 11
properties to measure bug-catching ability.

Hyperparameters (specify these as decimals, but these ought to be expressible as Rationals):
  α₀ (alpha0): Initial energy level
  t0: Weight for arity-0 constructors
  t1: Weight for arity-0 constructors
  t2: Weight forarity-2 constructors
  d (decay): Decay factor"

  FLAGS:
    "alpha0" : String;     "Initial energy level α₀ (required)"
    "t0" : String;         "Weight for arity-0 constructors (optional, default: 0.0)"
    "t1" : String;         "Weight for arity-1 constructors (optional, default: 0.0)"
    "t2" : String;         "Weight for arity-2 constructors (optional, default: 0.0)"
    "decay" : String;      "Decay factor d (required)"
    "max-tests" : Nat;    "Max no. of trials per property (default: 1000)"

  EXTENSIONS:
    author "Ernest Ng, Harrison Goldstein"
]

end BDTExperiments

/-- Main entry point -/
def main (args : List String) : IO UInt32 :=
  BDTExperiments.bdtCmd.validate args
