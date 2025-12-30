"""
Plots benchmark results from the CSV produced by `benchmark_bdt.py`
"""

import argparse
import csv
from typing import List

import matplotlib.pyplot as plt
import numpy as np

from benchmark_bdt import BDTConfig, BenchmarkResult


def parse_csv(
    filename: str = "../benchmark_results/benchmark_results.csv",
) -> List[BenchmarkResult]:
    """
    Parses benchmark results from CSV file,
    returning a list of `BenchmarkResult`s
    """
    results = []
    with open(filename, newline="") as f:
        reader = csv.DictReader(f)
        for row in reader:
            config = BDTConfig(
                alpha0=float(row["alpha0"]),
                t0=float(row["t0"]),
                t2=float(row["t2"]),
                decay=float(row["decay"]),
                name=row["configuration"],
            )
            result = BenchmarkResult(
                config=config,
                mean_time_s=float(row["mean_time_s"]),
                stddev_time_s=float(row["stddev_time_s"]),
                total_bugs_found=int(row["total_bugs_found"]),
                avg_tests_to_find_bug=float(row["avg_tests_to_find_bug"]),
                runs=int(row["runs"]),
            )
            results.append(result)
    return results


def plot_results(
    results: List[BenchmarkResult],
    filename: str = "../benchmark_results/benchmark_plots.png",
):
    """Plots benchmark results."""
    configs = [r.config.name for r in results]
    mean_times = [r.mean_time_s for r in results]
    stddev_times = [r.stddev_time_s for r in results]
    bugs_found = [r.total_bugs_found for r in results]
    avg_tests = [r.avg_tests_to_find_bug for r in results]

    # Create a 2x2 subplot figure
    fig, ((ax1, ax2), (ax3, ax4)) = plt.subplots(2, 2, figsize=(14, 10))
    fig.suptitle(
        'BDT Experiments for "How to Specify It" BST Case Study',
        fontsize=16,
        fontweight="bold",
        y=1.05,
    )

    # Add subtitle with hyperparameter values for each configuration
    subtitle_lines = []
    for r in results:
        c = r.config
        subtitle_lines.append(
            f"{c.name}: α₀={c.alpha0}, t₀={c.t0}, t₂={c.t2}, d={c.decay}"
        )
    subtitle = " | ".join(subtitle_lines)
    fig.text(
        0.5,
        0.98,
        subtitle,
        ha="center",
        fontsize=9,
        style="italic",
        wrap=True,
    )

    # Adjust subplot spacing to prevent overlap with titles
    plt.subplots_adjust(top=0.90)

    # 1. Mean execution time with error bars
    x_pos = np.arange(len(configs))
    ax1.bar(
        x_pos, mean_times, yerr=stddev_times, capsize=5, alpha=0.7, color="steelblue"
    )
    ax1.set_xlabel("Configuration", fontweight="bold")
    ax1.set_ylabel("Time (s)", fontweight="bold")
    ax1.set_title("Time to generate 1000 random BSTs, averaged over 5 runs")
    ax1.set_xticks(x_pos)
    ax1.set_xticklabels(configs, rotation=15, ha="right")
    ax1.grid(axis="y", alpha=0.3)

    # 2. Total bugs found
    ax2.bar(x_pos, bugs_found, alpha=0.7, color="forestgreen")
    ax2.set_xlabel("Configuration", fontweight="bold")
    ax2.set_ylabel("No. of bugs Found", fontweight="bold")
    ax2.set_title(
        "Total bugs found across 11 properties and 8 buggy BST implementations"
    )
    ax2.set_xticks(x_pos)
    ax2.set_xticklabels(configs, rotation=15, ha="right")
    ax2.grid(axis="y", alpha=0.3)

    # 3. Mean no. of trials before bug caught
    ax3.bar(x_pos, avg_tests, alpha=0.7, color="coral")
    ax3.set_xlabel("Configuration", fontweight="bold")
    ax3.set_ylabel("Mean no. of trials before bug caught", fontweight="bold")
    ax3.set_title("Mean no. of random trials before bug caught, averaged over 5 runs")
    ax3.set_xticks(x_pos)
    ax3.set_xticklabels(configs, rotation=15, ha="right")
    # Make y-ticks every 20 
    ystart, yend = ax3.get_ylim()
    ax3.set_yticks(np.arange(ystart, yend, step=20))
    ax3.grid(axis="y", alpha=0.3)

    # 4. Trade-off: Speed vs Effectiveness (scatter plot)
    colors = ["steelblue", "forestgreen", "coral", "mediumpurple"]
    for i, (config, time, bugs) in enumerate(zip(configs, mean_times, bugs_found)):
        ax4.scatter(time, bugs, s=200, alpha=0.7, color=colors[i], label=config)

    ax4.set_xlabel("Average time (s) to generate 1000 random BSTs", fontweight="bold")
    ax4.set_ylabel("No. of bugs found across 8 BST implementations", fontweight="bold")
    ax4.set_title("Generation time vs Bug-finding effectiveness")
    ax4.legend(loc="best")
    ax4.grid(alpha=0.3)

    # Add annotations to scatter plot
    for i, (time, bugs, config) in enumerate(zip(mean_times, bugs_found, configs)):
        ax4.annotate(
            f"{config}",
            (time, bugs),
            xytext=(5, 5),
            textcoords="offset points",
            fontsize=8,
            alpha=0.7,
        )

    plt.tight_layout()
    plt.savefig(filename, dpi=300, bbox_inches="tight")
    print(f"Plots saved to: {filename}")


def main():
    """Parse CSV and generate plots."""
    parser = argparse.ArgumentParser(
        description="Generate plots from BDT benchmark results CSV.",
        formatter_class=argparse.ArgumentDefaultsHelpFormatter,
    )
    parser.add_argument(
        "--input",
        type=str,
        default="../benchmark_results/benchmark_results.csv",
        help="Input CSV file with benchmark results",
    )
    parser.add_argument(
        "--output",
        type=str,
        default="../benchmark_results/benchmark_plots.png",
        help="Output PNG file for plots",
    )
    args = parser.parse_args()

    # Parse CSV and generate plots
    results = parse_csv(args.input)
    plot_results(results, args.output)


if __name__ == "__main__":
    main()
