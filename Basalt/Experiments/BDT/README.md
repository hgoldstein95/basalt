# BDT Hyperparameter Experiments

We examine the impact of four hyperparameters on the 11 BST properties & 8 buggy BST implementations 
from *How to Specify It*:

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
1. Define property in `Properties.lean` (should be a monadic function with return type `Gen Bool`)
2. Add entry to `allProperties` list in `TestHarness.lean`
3. The test harness will automatically include it in all runs

To test different hyperparameter ranges:
1. Modify the `QUICK_CONFIGS` list in `benchmark_bdt.py`
2. Or run individual experiments with custom parameters via the CLI


## Running Experiments

### Command Line Interface

Run experiments by specifying hyperparameter values:

```bash
$ lake exe bdt_experiments --alpha0 1.0 --t0 1.0 --t2 1.0 --decay 0.5 --max-tests 100
```

All four hyperparameters are required:
- `--alpha0`: Initial energy level (e.g., 1.0, 2.0, 4.0)
- `--t0`: Weight for leaves (e.g., 0.5, 1.0, 2.0)
- `--t2`: Weight for nodes (e.g., 0.5, 1.0, 2.0)
- `--decay`: Decay factor (e.g., 0.3, 0.5, 0.9)
- `--max-tests`: Maximum tests per property (optional, default: 1000)

### Example Configurations

**Balanced configuration:**
```bash
$ lake exe bdt_experiments --alpha0 1.0 --t0 1.0 --t2 1.0 --decay 0.5
```

**Node-favoring (larger trees):**
```bash
$ lake exe bdt_experiments --alpha0 4.0 --t0 0.5 --t2 2.0 --decay 0.7
```

**Leaf-favoring (smaller trees):**
```bash
$ lake exe bdt_experiments --alpha0 0.5 --t0 2.0 --t2 0.5 --decay 0.3
```

**Slow decay (maintains energy):**
```bash
$ lake exe bdt_experiments --alpha0 2.0 --t0 1.0 --t2 1.0 --decay 0.9
```

### Benchmarking Multiple Configurations

Use the Python benchmarking script to test multiple configurations:

```bash
$ cd scripts
$ uv run benchmark_bdt.py --max-tests 100 --runs 10 --warmup 1
```

This will:
- Run all quick sweep configurations (4 presets)
- Measure execution time with hyperfine
- Extract bug detection metrics
- Export results to `../benchmark_results/benchmark_results.csv`

To generate visualizations from the results:

```bash
$ uv run plot_results.py
```

This creates plots at `../benchmark_results/benchmark_plots.png`

## Properties Tested

The 11 BST properties from *How To Specify It* are as follows:

### Basic Operations
1. **insert-find**: After inserting a key, `find` should return its value
2. **insert-insert**: Inserting twice with the same key keeps the second value
3. **delete-find**: After deleting a key, `find` should return `none`
4. **insert-size**: Size increases by at most 1 after insert
5. **delete-size**: Size decreases by at most 1 after delete

### Invariants
6. **insert-valid**: Valid BST remains valid after insert
7. **delete-valid**: Valid BST remains valid after delete
8. **toList-sorted**: Keys in `toList` output are sorted

### Union Operations
9. **union-contains**: Union contains all keys from both trees
10. **union-left-priority**: Union prefers left tree for duplicate keys
11. **union-valid**: Union of valid BSTs produces valid BST

## Output Format
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
