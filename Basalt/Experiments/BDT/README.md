# BDT Hyperparameter Experiments

We examine the impact of four hyperparameters on the BST example:

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

## Usage

To add new properties:
1. Define property in `Properties.lean`
2. Add test case in `TestHarness.lean` (see the `testImplementation` function)
3. Update `ImplTestResult` structure to include new property stats

To test different hyperparameter ranges:
1. Modify `generateParamGrid` in `HyperparameterSweep.lean`
2. Or use custom ranges in `runQuickSweep`

## File Structure

```
BDT/
├── BSTGenerator.lean       # BDT-based BST generator
├── Properties.lean          # BST property specifications
├── TestHarness.lean        # Testing infrastructure
├── HyperparameterSweep.lean # Experiment runners
├── Analysis.lean           # Results analysis tools
├── Main.lean               # CLI entry point
```

## Usage

### Quick Sweep (Recommended for initial exploration)

Run a quick sweep with 4 hyperparameter configurations:

```bash
$ lake exe bdt_experiments quick
```

This tests:
- Balanced: α₀=1.0, t₀=1.0, t₂=1.0, d=0.5
- Node-favoring: α₀=4.0, t₀=0.5, t₂=2.0, d=0.7
- Leaf-favoring: α₀=0.5, t₀=2.0, t₂=0.5, d=0.3
- Slow decay: α₀=2.0, t₀=1.0, t₂=1.0, d=0.9

### Default Configuration

Test with default hyperparameters:

```bash
$ lake exe bdt_experiments default
```

This uses the config: `α₀=2.0, t₀=1.0, t₂=1.0, d=0.5`

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
```bash
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
