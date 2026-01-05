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


def run_single_experiment(config: BDTConfig, max_tests: int) -> tuple[int, float]:
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
        cwd="..",  # Run from project root
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
    max_tests: int,
    runs: int,
) -> BenchmarkResult:
    """
    Benchmark a single configuration using hyperfine.

    Args:
        config: Hyperparameter configuration
        max_tests: Maximum tests per property
        runs: Number of benchmark runs

    Returns:
        BenchmarkResult with timing and bug detection metrics
    """
    tqdm.write(f"Benchmarking: {config.name}")
    tqdm.write(
        f"Parameters: α₀={config.alpha0}, t₀={config.t0}, t₂={config.t2}, d={config.decay}"
    )

    # Command for running the Lean Basalt executable with the specified
    # parameter values
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

    # Run hyperfine for measuring wall-clock time
    # Need to run from parent directory since lake must be run from project root
    cmd_str = " ".join(cmd)
    hyperfine_cmd = [
        "hyperfine",
        "--runs",
        str(runs),
        "--style",
        "none",  # Suppress hyperfine output (results are checked separately)
        "--export-json",
        "/tmp/hyperfine_result.json",
        f"cd .. && {cmd_str}",
    ]

    tqdm.write(f"Running hyperfine with {runs} runs...")
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


def export_csv(
    results: List[BenchmarkResult],
    filename: str = "../benchmark_results/benchmark_results.csv",
):
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
        default=1000,
        help="Maximum number of tests per property",
    )
    parser.add_argument(
        "--runs",
        type=int,
        default=5,
        help="No. of benchmark runs for Hyperfine",
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

    # Run benchmarks
    results = []
    for config in tqdm(
        QUICK_CONFIGS, desc="Benchmarking configurations", unit="config"
    ):
        result = benchmark_config(config, args.max_tests, args.runs)
        results.append(result)

    export_csv(results)


if __name__ == "__main__":
    main()
