# BDT Hyperparameter Experiments

This directory contains an experimental framework for measuring the impact of Boltzmann Decay Tuning (BDT) hyperparameters on bug-catching ability in property-based testing.

## Overview

Based on the paper "Boltzmann Decay Tuning", this framework implements:
- **BDT-based BST generator** with configurable hyperparameters
- **Property-based tests** for BST operations
- **Bug detection experiments** against 8 buggy BST implementations
- **Hyperparameter sweep** capabilities
- **Analysis tools** for comparing configurations

## BDT Hyperparameters

The framework tests four hyperparameters:

1. **α₀ (alpha0)**: Initial "energy" level
   - Controls starting size tendency
   - Higher values favor larger initial structures

2. **t₀ (t0)**: Weight for arity-0 constructors (leaves)
   - Baseline weight for leaf nodes
   - Default: 1.0

3. **t₂ (t2)**: Weight for arity-2 constructors (branch nodes)
   - Weight multiplier for branch nodes
   - Higher values favor more branching

4. **d (decay)**: Decay factor
   - Controls how quickly α decreases
   - Range: 0.0 (fast decay) to 1.0 (no decay)
   - Typical values: 0.3 - 0.9

## File Structure

```
BDT/
├── BSTGenerator.lean       # BDT-based BST generator
├── Properties.lean          # BST property specifications
├── TestHarness.lean        # Testing infrastructure
├── HyperparameterSweep.lean # Experiment runners
├── Analysis.lean           # Results analysis tools
├── Main.lean               # CLI entry point
└── README.md               # This file
```

## Usage

### Quick Sweep (Recommended for initial exploration)

Run a quick sweep with 4 hyperparameter configurations:

```bash
lake exe bdt_experiments quick
```

This tests:
- Balanced: α₀=1.0, t₀=1.0, t₂=1.0, d=0.5
- Node-favoring: α₀=4.0, t₀=0.5, t₂=2.0, d=0.7
- Leaf-favoring: α₀=0.5, t₀=2.0, t₂=0.5, d=0.3
- Slow decay: α₀=2.0, t₀=1.0, t₂=1.0, d=0.9

### Full Sweep (Warning: Time-intensive!)

Run a complete grid search over 144 hyperparameter combinations:

```bash
lake exe bdt_experiments full
```

This will:
- Test 4 α₀ values × 3 t₀ values × 3 t₂ values × 4 decay values
- Run 1000 tests per property per implementation
- Export results to CSV for analysis

### Default Configuration

Test with default hyperparameters:

```bash
lake exe bdt_experiments default
```

This uses the balanced configuration: α₀=2.0, t₀=1.0, t₂=1.0, d=0.5

## Properties Tested

The framework tests these BST properties:

1. **insert-find**: After inserting a key, `find` should return its value
2. **insert-insert**: Inserting twice with the same key keeps the second value
3. **delete-find**: After deleting a key, `find` should return `none`
4. **insert-size**: Size increases by at most 1 after insert
5. **delete-size**: Size decreases by at most 1 after delete

## Buggy Implementations

Tests run against all 8 buggy BST implementations from the "How to Specify It" case study:

- **BST1**: `insert` discards the tree
- **BST2**: `insert` creates duplicates
- **BST3**: `insert` doesn't update existing keys
- **BST4**: `delete` doesn't rebuild tree structure
- **BST5**: `delete` has reversed comparisons
- **BST6**: `union` assumes key ordering
- **BST7**: `union` makes wrong ordering assumptions
- **BST8**: `union` has priority bug for duplicates

## Output Format

Each experiment reports:
- **Total bugs found**: Across all implementations and properties
- **Bugs per implementation**: How many bugs detected in each implementation
- **Average tests to find bug**: Efficiency metric
- **Best configuration**: Hyperparameters that found the most bugs

Example output:
```
--- Experiment Summary ---
Parameters:
  α₀ = 2.0
  t₀ = 1.0
  t₂ = 1.0
  decay = 0.5

Total Bugs Found: 28
Average Tests to Find Bug: 45.7

Bugs per Implementation:
  BST0 (correct): 0
  BST1 (insert discards tree): 4
  BST2 (insert creates duplicates): 3
  ...
```

## Analysis

The framework automatically:
- Identifies the best hyperparameter configuration
- Compares effectiveness across all tested configurations
- Exports results to CSV for further analysis in R/Python

CSV columns:
- `alpha0`, `t0`, `t2`, `decay`: Hyperparameters
- `totalBugsFound`: Total bugs detected
- `avgTestsToFindBug`: Average tests needed to find a bug

## Research Questions

This framework helps answer:

1. **Which hyperparameters matter most** for bug finding?
2. **What trade-offs exist** between different parameter settings?
3. **Are certain bugs easier to find** with specific hyperparameters?
4. **How does decay rate affect** bug detection?
5. **What's the optimal balance** between leaves and nodes?

## Extending the Framework

To add new properties:
1. Define property in `Properties.lean`
2. Add test case in `TestHarness.lean` (`testImplementation` function)
3. Update `ImplTestResult` structure to include new property stats

To test different hyperparameter ranges:
1. Modify `generateParamGrid` in `HyperparameterSweep.lean`
2. Or use custom ranges in `runQuickSweep`

## Notes

- The correct implementation (BST0) should always pass all tests
- Some bugs may be harder to find than others
- Hyperparameter effectiveness may vary by bug type
- Results are stochastic - run multiple times for statistical significance
