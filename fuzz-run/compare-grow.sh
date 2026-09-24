#!/usr/bin/env bash
# Copyright (c) 2026 Harrison Goldstein. All rights reserved.
# Released under MIT license as described in the file LICENSE.
# Authors: Michael Hicks

# Compare the fuzz backend with and without `--grow`. Reproduces the tables in fuzz-run/README.md
# ("How much growth helps").
#
# This is the intra-backend counterpart of compare-backends.sh, which compares fuzz against the
# random backends. Only a property whose generator *outruns its buffer* can separate the two settings
# — one that always fits reads no bytes past the end and reports no deficit, so growth never fires and
# both columns are the same campaign. `long-*` is the case built for it
# (BasaltFuzz/Staged.lean).
#
# Two modes, because the obvious metric is the bad one:
#
#   MODE=rate    (default) share of trials that find the counterexample within a fixed run budget.
#                A binomial, so its error bar is sqrt(p(1-p)/n) and two cells are comparable.
#   MODE=median  runs and wall-clock to first failure, median over TRIALS. Kept only because
#                fuzz-run/README.md cites it as *evidence that it cannot be trusted*: repeated passes
#                over the same binary disagree in sign.
#
# Usage: fuzz-run/compare-grow.sh [property...]        (default: long-16 long-32 long-64)
#        MODE=median fuzz-run/compare-grow.sh long-32
set -euo pipefail
cd "$(dirname "$0")/.."

MODE="${MODE:-rate}"
PROPS=("$@")
[ ${#PROPS[@]} -gt 0 ] || PROPS=(long-16 long-32 long-64)

[ -x fuzz-run/basalt-fuzz ] || { echo "build first: fuzz-run/build.sh" >&2; exit 1; }

# One length regime for both settings: `--grow` otherwise inherits libFuzzer's own decision to drop
# the `-len_control` ramp when a custom mutator is linked (Basalt/Fuzz/Runner.lean), and the ramp
# rather than the setting would decide how long an input may get.
COMMON=(-len_control=0 -max_len=65536)

TIMEOUT="${TIMEOUT:-180}"           # per-trial seconds; a bounded `-runs` should never reach it

# A campaign either printed a counterexample or it did not; the exit status cannot be used, because
# the timeout below kills the process for a nonzero status too.
#
# The output is captured before being matched rather than piped into `grep -q`. Under `pipefail` that
# pipeline reports failure whenever it *succeeds*: `grep -q` exits at the first match, `tr` then dies
# on SIGPIPE, and the pipeline takes `tr`'s status — so every trial reads as a miss and both settings
# score 0.
found_within() { # property budget flag... -> 0 if a counterexample was reported
  local p=$1 budget=$2; shift 2
  local out
  rm -rf /tmp/basalt-grow; mkdir -p /tmp/basalt-grow
  out=$(perl -e "alarm $TIMEOUT; exec @ARGV" \
          fuzz-run/basalt-fuzz "$p" "$@" "${COMMON[@]}" -runs="$budget" \
          -artifact_prefix=/tmp/basalt-grow/ 2>&1 | tr -d '\000' || true)
  printf '%s' "$out" | grep -aq 'BASALT PROPERTY FAILED'
}

# Budgets are set near each property's own median, where a shift in either direction moves the rate
# the most. A property not listed here needs `BUDGET=` given explicitly: there is no meaningful
# default, since a budget far above the median puts both cells at 100% and measures nothing.
budget_for() {
  if [ -n "${BUDGET:-}" ]; then echo "$BUDGET"; return; fi
  case $1 in
    long-16) echo 3000 ;;
    long-32) echo 30000 ;;
    long-64) echo 120000 ;;
    *) echo "no budget known for '$1'; pass BUDGET=N" >&2; exit 1 ;;
  esac
}

run_rate() {
  local trials="${TRIALS:-300}"
  printf '%-10s %-8s %9s %14s\n' property setting budget "found (±1 SE)"
  printf '%.0s-' {1..45}; echo
  for p in "${PROPS[@]}"; do
    local budget; budget=$(budget_for "$p")
    for setting in "off" "--grow"; do
      local hits=0 flags=()
      if [ "$setting" = "--grow" ]; then flags=(--grow); fi
      for _ in $(seq "$trials"); do
        found_within "$p" "$budget" "${flags[@]+"${flags[@]}"}" && hits=$((hits+1))
      done
      printf '%-10s %-8s %9s %14s\n' "$p" "$setting" "$budget" \
        "$(python3 -c "
h,n=$hits,$trials; p=h/n
print(f'{h}/{n} {p*100:.1f}% ±{(p*(1-p)/n)**.5*100:.1f}')")"
    done
  done
}

MAXRUNS="${MAXRUNS:-50000000}"      # cap so a setting that cannot find the bug terminates

trial() { # property flag... -> "runs seconds", or "- -" if no counterexample within the caps
  local p=$1; shift
  local t0 t1 out
  rm -rf /tmp/basalt-grow; mkdir -p /tmp/basalt-grow
  t0=$(python3 -c 'import time;print(time.time())')
  out=$(perl -e "alarm $TIMEOUT; exec @ARGV" \
          fuzz-run/basalt-fuzz "$p" "$@" "${COMMON[@]}" -runs="$MAXRUNS" \
          -artifact_prefix=/tmp/basalt-grow/ 2>&1 | tr -d '\000' || true)
  t1=$(python3 -c 'import time;print(time.time())')
  local runs
  runs=$(printf '%s' "$out" | grep -aE '^runs +:' | head -1 | awk '{print $3}')
  if [ -z "$runs" ]; then echo "- -"; else
    echo "$runs $(python3 -c "print(f'{$t1-$t0:.2f}')")"
  fi
}

median() { python3 -c '
import sys
xs=[v for v in sys.argv[1:] if v!="-"]
if not xs: print("none"); raise SystemExit
xs=sorted(float(x) for x in xs); n=len(xs)
m=xs[n//2] if n%2 else (xs[n//2-1]+xs[n//2])/2
print(f"{m:,.0f}" if m>=100 else f"{m:.2f}")' "$@"; }

# Read the medians together with the `found` column: a setting that found the bug in 2/15 trials has
# a median conditioned on its lucky trials and is strictly worse than one with the same median at
# 15/15. Read the whole table knowing that a repeat of it may reverse the ordering.
run_median() {
  local trials="${TRIALS:-61}"
  printf '%-10s %-10s %14s %10s %8s\n' property setting "median runs" "median s" "found"
  printf '%.0s-' {1..56}; echo
  for p in "${PROPS[@]}"; do
    for setting in "off" "--grow"; do
      local rs=() ss=() found=0 flags=()
      if [ "$setting" = "--grow" ]; then flags=(--grow); fi
      for _ in $(seq "$trials"); do
        read -r r s <<<"$(trial "$p" "${flags[@]+"${flags[@]}"}")"
        rs+=("$r"); ss+=("$s"); [ "$r" != "-" ] && found=$((found+1))
      done
      printf '%-10s %-10s %14s %10s %5s/%s\n' \
        "$p" "$setting" "$(median "${rs[@]}")" "$(median "${ss[@]}")" "$found" "$trials"
    done
  done
}

case "$MODE" in
  rate)   run_rate ;;
  median) run_median ;;
  *) echo "MODE must be 'rate' or 'median'" >&2; exit 1 ;;
esac
