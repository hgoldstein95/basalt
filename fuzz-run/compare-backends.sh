#!/usr/bin/env bash
# Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All rights reserved.
# Released under MIT license as described in the file LICENSE.
# Authors: Michael Hicks

# Compare the three backends on how fast they find a counterexample: runs and wall-clock to first
# failure, median over N trials. Reproduces the table in fuzz-run/README.md ("Backend comparison").
#
# Only buggy properties are meaningful here — a property with no bug has no time-to-failure. Each
# trial is a fresh process, so libFuzzer starts from an empty corpus and the random backends from a
# fresh seed; that is the honest comparison for "find a bug from a cold start".
#
# Usage: fuzz-run/compare-backends.sh [property...]   (default: the buggy demo properties)
set -euo pipefail
cd "$(dirname "$0")/.."

TRIALS="${TRIALS:-9}"
MAXRUNS="${MAXRUNS:-50000000}"      # cap so a backend that cannot find the bug terminates
TIMEOUT="${TIMEOUT:-300}"           # per-trial seconds
PROPS=("$@")
[ ${#PROPS[@]} -gt 0 ] || PROPS=(threshold bst-buggy-insert bst-buggy-insert2 bst-buggy-delete)

[ -x fuzz-run/basalt-fuzz ] || { echo "build first: fuzz-run/build.sh" >&2; exit 1; }

# `runs : N (M discarded)` is printed by every backend on the failing input (Basalt/Fuzz/Runner.lean),
# which is what makes the three directly comparable.
trial() { # backend property -> "runs seconds", or "- -" if no counterexample within the caps
  local b=$1 p=$2 extra=""
  [ "$b" = fuzz ] && extra="-max_len=64 -artifact_prefix=/tmp/basalt-cmp/"
  local t0 t1 out
  mkdir -p /tmp/basalt-cmp
  t0=$(python3 -c 'import time;print(time.time())')
  out=$(perl -e "alarm $TIMEOUT; exec @ARGV" \
          fuzz-run/basalt-fuzz --backend="$b" "$p" -runs="$MAXRUNS" $extra 2>&1 | tr -d '\000' || true)
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

# The medians are over the trials that *found* the bug, so read them together with the `found`
# column: a backend that found it in 3/9 trials has a median conditioned on its lucky trials and is
# strictly worse than one with the same median at 9/9.
printf '%-22s %-14s %14s %10s %8s\n' property backend "median runs" "median s" "found"
printf '%.0s-' {1..72}; echo
for p in "${PROPS[@]}"; do
  for b in fuzz io plausible; do
    rs=(); ss=(); found=0
    for _ in $(seq "$TRIALS"); do
      read -r r s <<<"$(trial "$b" "$p")"
      rs+=("$r"); ss+=("$s"); [ "$r" != "-" ] && found=$((found+1))
    done
    printf '%-22s %-14s %14s %10s %5s/%s\n' \
      "$p" "$b" "$(median "${rs[@]}")" "$(median "${ss[@]}")" "$found" "$TRIALS"
  done
done
