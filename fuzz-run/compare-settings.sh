#!/usr/bin/env bash
# Copyright (c) 2026 Harrison Goldstein. All rights reserved.
# Released under MIT license as described in the file LICENSE.
# Authors: Michael Hicks

# Compare settings of the fuzz backend by the share of campaigns that find the counterexample within a
# fixed run budget. Reproduces the tables in fuzz-run/README.md that compare settings.
#
# This is the intra-backend counterpart of compare-backends.sh. SETTINGS is the list of flag sets to
# compare, space-separated, the flags of one set joined by commas, `off` meaning no extra flag:
#
#   SETTINGS="off --truncate" fuzz-run/compare-settings.sh chain-2 chain-3 chain-4 long-16
#
# A success rate rather than a median of runs-to-failure: the distribution is heavy-tailed enough that
# repeated median passes over one binary disagree in sign, while a rate is a binomial, with error bar
# sqrt(p(1-p)/n), so two cells are comparable.
#
# Usage: fuzz-run/compare-settings.sh [property...]        (default: chain-2 chain-3 chain-4 long-16)
set -euo pipefail
cd "$(dirname "$0")/.."
PROPS=("$@")
[ ${#PROPS[@]} -gt 0 ] || PROPS=(chain-2 chain-3 chain-4 long-16)
read -r -a SETTINGS <<<"${SETTINGS:-off --truncate}"
TRIALS="${TRIALS:-300}"
JOBS="${JOBS:-4}"                   # campaigns run at once
TIMEOUT="${TIMEOUT:-180}"           # per-trial seconds; a bounded `-runs` should never reach it

BIN="${BIN:-fuzz-run/basalt-fuzz}"   # the executable measured; a copy keeps a rebuild out of a run
[ -x "$BIN" ] || { echo "build first: fuzz-run/build.sh" >&2; exit 1; }

# One length regime for every setting, set explicitly: otherwise each setting's defaults
# (`withDefaults`, Basalt/Fuzz/Runner.lean), not the setting, could decide how long an input may get.
COMMON=(-len_control=0 -max_len=65536)

# Budgets are set near each property's own median under `off`, where a shift in either direction moves
# the rate the most. A property not listed here needs `BUDGET=` given explicitly: a budget far above
# the median puts every cell at 100% and measures nothing.
budget_for() {
  if [ -n "${BUDGET:-}" ]; then echo "$BUDGET"; return; fi
  case $1 in
    chain-2) echo 500 ;;
    chain-3) echo 1000 ;;
    chain-4) echo 1200 ;;
    long-16) echo 3000 ;;
    long-32) echo 30000 ;;
    long-64) echo 120000 ;;
    *) echo "no budget known for '$1'; pass BUDGET=N" >&2; exit 1 ;;
  esac
}

# One campaign: prints 1 if it reported a counterexample, else 0. The output is captured before being
# matched rather than piped into `grep -q`: under `pipefail`, `grep -q` exits at the first match, `tr`
# dies on SIGPIPE, and the pipeline reports failure exactly when it succeeds.
found_within() { # property budget flag...
  local p=$1 budget=$2; shift 2
  local dir out
  dir=$(mktemp -d)
  out=$(perl -e "alarm $TIMEOUT; exec @ARGV" \
          "$BIN" "$p" "$@" "${COMMON[@]}" -runs="$budget" \
          -artifact_prefix="$dir/" 2>&1 | tr -d '\000' || true)
  rm -rf "$dir"
  if printf '%s' "$out" | grep -aq 'BASALT PROPERTY FAILED'; then echo 1; else echo 0; fi
}
export -f found_within
export TIMEOUT BIN
export COMMON_FLAGS="${COMMON[*]}"

printf '%-10s %-16s %9s %16s\n' property setting budget "found (±1 SE)"
printf '%.0s-' {1..54}; echo
for p in "${PROPS[@]}"; do
  budget=$(budget_for "$p")
  for setting in "${SETTINGS[@]}"; do
    flag=""; [ "$setting" = off ] || flag=${setting//,/ }
    # shellcheck disable=SC2016   # the child shell expands these, not this one
    hits=$(seq "$TRIALS" | xargs -P "$JOBS" -I{} bash -c \
             'COMMON=($COMMON_FLAGS); found_within "$0" "$1" $2' "$p" "$budget" "$flag" \
           | awk '{s += $1} END {print s + 0}')
    printf '%-10s %-16s %9s %16s\n' "$p" "$setting" "$budget" "$(python3 -c "
h,n=$hits,$TRIALS; p=h/n
print(f'{h}/{n} {p*100:.1f}% ±{(p*(1-p)/n)**.5*100:.1f}')")"
  done
done
