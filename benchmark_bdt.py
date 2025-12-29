"""
Benchmark BDT experiments with different hyperparameter configurations.

This script runs the BDT experiments for each configuration in the quick sweep,
measuring wall-clock time with hyperfine and extracting bug detection metrics.
"""

import argparse
import csv
import json
import re
import subprocess
import sys
from dataclasses import dataclass
from typing import List

from tqdm import tqdm


@dataclass
class BDTConfig:
    """BDT hyperparameter values"""

    alpha0: float
    t0: float
    t2: float
    decay: float
    name: str


@dataclass
class BenchmarkResult:
    """Results from benchmarking a single configuration."""

    config: BDTConfig
    mean_time_s: float
    stddev_time_s: float
    total_bugs_found: int
    avg_tests_to_find_bug: float
    runs: int


# Quick sweep configurations (from HyperparameterSweep.lean)
QUICK_CONFIGS = [
    BDTConfig(1.0, 1.0, 1.0, 0.5, "Balanced"),
    BDTConfig(4.0, 0.5, 2.0, 0.7, "Favors nodes"),
    BDTConfig(0.5, 2.0, 0.5, 0.3, "Favors leaves"),
    BDTConfig(2.0, 1.0, 1.0, 0.9, "Slow decay"),
]


def check_hyperfine() -> bool:
    """Checks if hyperfine is installed."""
    try:
        subprocess.run(
            ["hyperfine", "--version"],
            capture_output=True,
            check=True,
        )
        return True
    except (subprocess.CalledProcessError, FileNotFoundError):
        return False


def run_single_experiment(config: BDTConfig, max_tests: int = 100) -> tuple[int, float]:
    """
    Run a single BDT experiment and extract metrics.

    Returns:
        Tuple of (total_bugs_found, avg_tests_to_find_bug)
    """
    cmd = [
        "lake",
        "exe",
        "bdt_experiments",
        "--alpha0",
        str(config.alpha0),
        "--t0",
        str(config.t0),
        "--t2",
        str(config.t2),
        "--decay",
        str(config.decay),
        "--max-tests",
        str(max_tests),
    ]

    result = subprocess.run(
        cmd,
        capture_output=True,
        text=True,
        check=True,
    )

    # Parse output for metrics
    output = result.stdout

    # Extract "Total Bugs Found: X"
    bugs_match = re.search(r"Total Bugs Found:\s*(\d+)", output)
    total_bugs = int(bugs_match.group(1)) if bugs_match else 0

    # Extract "Average Tests to Find Bug: X.X"
    avg_match = re.search(r"Average Tests to Find Bug:\s*([\d.]+)", output)
    avg_tests = float(avg_match.group(1)) if avg_match else 0.0

    return total_bugs, avg_tests


def benchmark_config(
    config: BDTConfig,
    max_tests: int = 100,
    runs: int = 10,
    warmup: int = 1,
) -> BenchmarkResult:
    """
    Benchmark a single configuration using hyperfine.

    Args:
        config: Hyperparameter configuration
        max_tests: Maximum tests per property
        runs: Number of benchmark runs
        warmup: Number of warmup runs

    Returns:
        BenchmarkResult with timing and bug detection metrics
    """
    tqdm.write(f"\nBenchmarking: {config.name}")
    tqdm.write(
        f"Parameters: α₀={config.alpha0}, t₀={config.t0}, t₂={config.t2}, d={config.decay}"
    )

    # Build the command
    cmd = [
        "lake",
        "exe",
        "bdt_experiments",
        "--alpha0",
        str(config.alpha0),
        "--t0",
        str(config.t0),
        "--t2",
        str(config.t2),
        "--decay",
        str(config.decay),
        "--max-tests",
        str(max_tests),
    ]

    # Run hyperfine for timing
    hyperfine_cmd = [
        "hyperfine",
        # Disable shell startup to avoid noise in measurements
        "--shell=none",
        "--runs",
        str(runs),
        "--warmup",
        str(warmup),
        "--style",
        "none",  # Suppress hyperfine output (results are checked separately)
        "--export-json",
        "/tmp/hyperfine_result.json",
        " ".join(cmd),
    ]

    tqdm.write(f"Running hyperfine with {runs} runs (warmup: {warmup})...")
    subprocess.run(hyperfine_cmd, check=True)

    # Parse hyperfine results
    with open("/tmp/hyperfine_result.json") as f:
        hyperfine_data = json.load(f)

    result = hyperfine_data["results"][0]
    mean_time = result["mean"]
    stddev_time = result["stddev"]

    # Run once more to get bug detection metrics
    tqdm.write("Extracting bug detection metrics...")
    total_bugs, avg_tests = run_single_experiment(config, max_tests)

    return BenchmarkResult(
        config=config,
        mean_time_s=mean_time,
        stddev_time_s=stddev_time,
        total_bugs_found=total_bugs,
        avg_tests_to_find_bug=avg_tests,
        runs=runs,
    )


def print_results_table(results: List[BenchmarkResult]):
    """Prints a formatted table of benchmark results."""
    print("\n" + "=" * 80)
    print("BENCHMARK RESULTS")
    print("=" * 80)

    # Header
    print(
        f"\n{'Configuration':<20} {'Mean Time (s)':<15} {'±StdDev':<12} "
        f"{'Bugs Found':<12} {'Avg Tests':<12}"
    )
    print("-" * 80)

    # Data rows
    for r in results:
        print(
            f"{r.config.name:<20} {r.mean_time_s:.3f}s{'':<10} "
            f"±{r.stddev_time_s:.3f}s{'':<5} "
            f"{r.total_bugs_found:<12} {r.avg_tests_to_find_bug:.2f}"
        )

    # Summary statistics
    print("\n" + "=" * 80)
    print("SUMMARY")
    print("=" * 80)

    mean_time_avg = sum(r.mean_time_s for r in results) / len(results)
    total_bugs_avg = sum(r.total_bugs_found for r in results) / len(results)
    avg_tests_avg = sum(r.avg_tests_to_find_bug for r in results) / len(results)

    print(f"Average mean time:       {mean_time_avg:.3f}s")
    print(f"Average bugs found:      {total_bugs_avg:.2f}")
    print(f"Average tests to bug:    {avg_tests_avg:.2f}")

    # Best configuration by bugs found
    best_bugs = max(results, key=lambda r: r.total_bugs_found)
    print(
        f"\nBest for bug detection:  {best_bugs.config.name} "
        f"({best_bugs.total_bugs_found} bugs)"
    )

    # Fastest configuration
    fastest = min(results, key=lambda r: r.mean_time_s)
    print(
        f"Fastest configuration:   {fastest.config.name} ({fastest.mean_time_s:.3f}s)"
    )


def export_csv(results: List[BenchmarkResult], filename: str = "benchmark_results.csv"):
    """Export results to CSV."""

    with open(filename, "w", newline="") as f:
        writer = csv.writer(f)
        writer.writerow(
            [
                "configuration",
                "alpha0",
                "t0",
                "t2",
                "decay",
                "mean_time_s",
                "stddev_time_s",
                "total_bugs_found",
                "avg_tests_to_find_bug",
                "runs",
            ]
        )

        for r in results:
            writer.writerow(
                [
                    r.config.name,
                    r.config.alpha0,
                    r.config.t0,
                    r.config.t2,
                    r.config.decay,
                    r.mean_time_s,
                    r.stddev_time_s,
                    r.total_bugs_found,
                    r.avg_tests_to_find_bug,
                    r.runs,
                ]
            )

    print(f"\nResults exported to: {filename}")


def main():
    """Run benchmarks for all quick sweep configurations."""
    # Parse command line arguments
    parser = argparse.ArgumentParser(
        description="Benchmark BDT experiments with different hyperparameter configurations.",
        formatter_class=argparse.ArgumentDefaultsHelpFormatter,
    )
    parser.add_argument(
        "--max-tests",
        type=int,
        default=100,
        help="Maximum number of tests per property",
    )
    parser.add_argument(
        "--runs",
        type=int,
        default=10,
        help="Number of benchmark runs for hyperfine",
    )
    parser.add_argument(
        "--warmup",
        type=int,
        default=1,
        help="Number of warmup runs for hyperfine",
    )
    args = parser.parse_args()

    # Check prerequisites
    if not check_hyperfine():
        print(
            "Error: Hyperfine isn't installed, install it via `brew install hyperfine`",
            file=sys.stderr,
        )
        sys.exit(1)

    print("BDT Benchmark Configuration:")
    print(f"  Max tests per property: {args.max_tests}")
    print(f"  Benchmark runs: {args.runs}")
    print(f"  Warmup runs: {args.warmup}\n")

    # Run benchmarks
    results = []
    for config in tqdm(
        QUICK_CONFIGS, desc="Benchmarking configurations", unit="config"
    ):
        result = benchmark_config(config, args.max_tests, args.runs, args.warmup)
        results.append(result)

    # Print and export results
    print_results_table(results)
    export_csv(results)


if __name__ == "__main__":
    main()
