#!/bin/bash
# Build the opt-in `basalt-fuzz` executable: elaborate the Mathlib-free property/generator closure
# with Lake, SanitizerCoverage-instrument its C, and link it against libFuzzer with Lean owning
# `main` (which calls Fuzz.go -> fuzzer::FuzzerDriver). See FUZZING-DESIGN.md §6 / Appendix A.
#
# This is NOT part of `lake build`. Usage:  fuzz-run/build.sh   then   ./fuzz-run/basalt-fuzz <prop> ...
set -euo pipefail
cd "$(dirname "$0")/.."
ROOT=$(pwd)

TC=/local/home/mwhicks/.elan/toolchains/leanprover--lean4---v4.33.0-rc2   # Appendix A
export LEAN_CC=/home/mwhicks/.local/bin/basalt-leancc                    # system clang 11 wrapper
FUZZER_LIB=/usr/lib64/clang/11.1.0/lib/linux                             # libclang_rt.fuzzer_no_main
STDCPP=/usr/lib/gcc/x86_64-redhat-linux/7                                # libstdc++ (libFuzzer C++)
IR="$ROOT/.lake/build/ir"
OUT="$ROOT/fuzz-run/obj"; mkdir -p "$OUT"

# The exact (Mathlib-free) module closure the executable links. Instrumenting all of it realizes
# the "property + generator modules" coverage scope (none of these import Mathlib).
MODULES=(
  Basalt/RandomChoice Basalt/Gen Basalt/IO Basalt/Combinators
  Basalt/Fuzz/Core Basalt/Fuzz/Runner
  BasaltFuzz/BST            # present once Phase 3 lands; skipped gracefully if absent
  BasaltFuzzMain
)

echo "== elaborate + emit C via Lake =="
lake build Basalt.Fuzz.Runner Basalt.Combinators BasaltFuzzMain \
  ${EXTRA_LAKE_TARGETS:-} >/dev/null

echo "== compile (SanitizerCoverage on all first-party modules) + bridge =="
OBJS=()
for m in "${MODULES[@]}"; do
  c="$IR/$m.c"
  [ -f "$c" ] || { echo "  (skip $m: no IR)"; continue; }
  o="$OUT/$(echo "$m" | tr / _).o"
  /usr/bin/clang -O1 -I"$TC/include" -fsanitize=fuzzer-no-link -c "$c" -o "$o"
  OBJS+=("$o")
done
/usr/bin/clang -O1 -I"$TC/include" -c Basalt/Fuzz/native.c -o "$OUT/native.o"
OBJS+=("$OUT/native.o")

echo "== link =="
leanc "${OBJS[@]}" -o fuzz-run/basalt-fuzz \
  -fsanitize=fuzzer-no-link \
  -L"$FUZZER_LIB" -l:libclang_rt.fuzzer_no_main-x86_64.a \
  -L"$STDCPP" -lstdc++ 2>&1 | grep -viE 'unused|-Wl' || true

echo "== built: fuzz-run/basalt-fuzz =="
