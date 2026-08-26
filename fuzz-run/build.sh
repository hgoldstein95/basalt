#!/usr/bin/env bash
# Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All rights reserved.
# Released under MIT license as described in the file LICENSE.
# Authors: Michael Hicks

# Build the opt-in `basalt-fuzz` executable: elaborate the Mathlib-free property/generator closure
# with Lake, SanitizerCoverage-instrument its C, and link it against libFuzzer with Lean owning
# `main` (which calls Fuzz.go -> libFuzzer's driver). See BasaltFuzz/DESIGN.md §6.
#
# Portable across macOS (arm64) and Linux; everything platform-specific is detected below, and each
# detection can be overridden by the environment variable named in its block. `fuzz-run/env.sh`, if
# present, is sourced first — that is the place for per-machine overrides (it is git-ignored).
#
# This is NOT part of `lake build`. Usage:  fuzz-run/build.sh   then   ./fuzz-run/basalt-fuzz <prop>
set -euo pipefail
cd "$(dirname "$0")/.."
ROOT=$(pwd)

if [ -f fuzz-run/env.sh ]; then . fuzz-run/env.sh; fi

IR="$ROOT/.lake/build/ir"
DEP_IR="$ROOT/.lake/packages/plausible/.lake/build/ir"
OUT="$ROOT/fuzz-run/obj"; mkdir -p "$OUT"

# The exact (Mathlib-free) module closure the executable links. Instrumenting all of it realizes
# the "property + generator modules" coverage scope (none of these import Mathlib).
MODULES=(
  Basalt/RandomChoice Basalt/Gen Basalt/IO Basalt/Combinators Basalt/PlausibleGen
  Basalt/Fuzz/Core Basalt/Fuzz/Runner
  BasaltFuzz/BuggyBST BasaltFuzz/Staged
  BasaltFuzzMain
)

# Dependency modules the closure needs, compiled *without* SanitizerCoverage: they are the
# `--backend=plausible` PRNG, not code under test, and coverage over a PRNG's mixing steps is pure
# noise to libFuzzer's feedback. `Basalt/PlausibleGen` pulls these in for the `Gen Plausible.Gen`
# instance; nothing here imports Mathlib (verified by the link succeeding).
DEP_MODULES=(Plausible/Random Plausible/Gen)

# ---------------------------------------------------------------------------------------------
# Platform detection
# ---------------------------------------------------------------------------------------------
# `leanc` is the C compile/link driver throughout: it already knows the Lean toolchain's include
# path, clang resource headers, sysroot, and library rpaths, so using it in place of a raw `clang`
# invocation is what removes the hand-supplied paths this script used to carry. Override with CC.
: "${CC:=leanc}"
TC=$(lean --print-prefix)
UNAME=$(uname -s)

# Extra include flags for compiling `native.c`. Lean's emitted IR needs only Lean's own sysroot,
# but the bridge includes <string.h>/<stdlib.h>, and on macOS `leanc` sets `-isysroot` to the Lean
# toolchain (which has no libc headers) and suppresses the platform default. Feed it the SDK's
# include dir explicitly. Override with BRIDGE_INCLUDES.
if [ "$UNAME" = "Darwin" ] && [ -z "${BRIDGE_INCLUDES+x}" ]; then
  BRIDGE_INCLUDES="-isystem $(xcrun --show-sdk-path)/usr/include"
fi
: "${BRIDGE_INCLUDES:=}"

# The libFuzzer runtime to link, and which driver entry the bridge should call. Preference order:
#   1. FUZZER_LIB_FLAGS from the environment / env.sh (an explicit choice wins).
#   2. A toolchain-provided `libclang_rt.fuzzer_no_main-*.a` (the Linux case).
#   3. fuzz-run/vendor/libFuzzerNoMain.a, built from compiler-rt source by ./get-libfuzzer.sh
#      (the macOS case: no toolchain ships the runtime there).
# `fuzzer_no_main` (not `fuzzer`) is required: we provide LLVMFuzzerTestOneInput and call the driver
# ourselves from Lean's `main`.
if [ -z "${FUZZER_LIB_FLAGS+x}" ]; then
  found=""
  for d in ${FUZZER_LIB_SEARCH:-} \
           "$TC"/lib/clang/*/lib/linux "$TC"/lib/clang/*/lib/* \
           /usr/lib64/clang/*/lib/linux /usr/lib/clang/*/lib/linux \
           /usr/lib/llvm-*/lib/clang/*/lib/linux; do
    [ -d "$d" ] || continue
    for a in "$d"/libclang_rt.fuzzer_no_main*.a; do
      [ -f "$a" ] || continue
      found="$a"; break 2
    done
  done
  if [ -n "$found" ]; then
    FUZZER_LIB_FLAGS="$found"
  else
    [ -f fuzz-run/vendor/libFuzzerNoMain.a ] || fuzz-run/get-libfuzzer.sh
    FUZZER_LIB_FLAGS="$ROOT/fuzz-run/vendor/libFuzzerNoMain.a"
  fi
fi

# The C++ runtime libFuzzer itself needs. libc++ on macOS, libstdc++ with GNU toolchains.
# Override with CXXLIB_FLAGS (Appendix A's box needs a -L for it).
if [ -z "${CXXLIB_FLAGS+x}" ]; then
  if [ "$UNAME" = "Darwin" ]; then CXXLIB_FLAGS="-lc++"; else CXXLIB_FLAGS="-lstdc++"; fi
fi

# Which driver symbol the bridge calls. LLVM >= 12 has the stable C entry `LLVMFuzzerRunDriver`;
# clang 11 and earlier expose only the mangled `fuzzer::FuzzerDriver`. Probe the archive rather
# than parsing a version, since the archive is the thing that must contain the symbol.
if [ -z "${DRIVER_DEFINE+x}" ]; then
  DRIVER_DEFINE=""
  probe=$(printf '%s\n' $FUZZER_LIB_FLAGS | grep -E '\.a$' | head -1 || true)
  if [ -n "$probe" ] && [ -f "$probe" ]; then
    # `grep -c`, not `grep -q`: `-q` exits at the first match, so `nm` dies of SIGPIPE and
    # `set -o pipefail` reports 141 for a *successful* probe — which selected the legacy driver on
    # a toolchain that has the modern entry.
    hits=$(nm "$probe" 2>/dev/null | grep -c 'LLVMFuzzerRunDriver' || true)
    if [ "${hits:-0}" -eq 0 ]; then DRIVER_DEFINE="-DBASALT_FUZZ_LEGACY_DRIVER"; fi
  fi
fi

echo "== platform: $UNAME; cc: $CC; runtime: $FUZZER_LIB_FLAGS ${DRIVER_DEFINE:+(legacy driver)} =="

# ---------------------------------------------------------------------------------------------
echo "== elaborate + emit C via Lake =="
lake build Basalt.Fuzz.Runner Basalt.Combinators BasaltFuzzMain \
  ${EXTRA_LAKE_TARGETS:-} >/dev/null

echo "== compile (SanitizerCoverage on all first-party modules) + bridge =="
OBJS=()
for m in "${MODULES[@]}"; do
  c="$IR/$m.c"
  [ -f "$c" ] || { echo "  (skip $m: no IR)"; continue; }
  o="$OUT/$(echo "$m" | tr / _).o"
  $CC -O1 -fsanitize=fuzzer-no-link -c "$c" -o "$o"
  OBJS+=("$o")
done
for m in "${DEP_MODULES[@]}"; do
  c="$DEP_IR/$m.c"
  [ -f "$c" ] || { echo "  (skip $m: no IR)"; continue; }
  o="$OUT/$(echo "$m" | tr / _).o"
  $CC -O1 -c "$c" -o "$o"
  OBJS+=("$o")
done
$CC -O1 $BRIDGE_INCLUDES $DRIVER_DEFINE -c Basalt/Fuzz/native.c -o "$OUT/native.o"
OBJS+=("$OUT/native.o")

# `-fsanitize=fuzzer-no-link` is deliberately absent here: it is a *compile-time* instrumentation
# flag, and at link time it also pulls in a ubsan dylib that Lean's vendored clang does not ship
# (the link fails with "cannot open ... libclang_rt.ubsan_osx_dynamic.dylib"). The runtime archive
# supplies every symbol the link actually needs.
echo "== link =="
$CC "${OBJS[@]}" -o fuzz-run/basalt-fuzz \
  $FUZZER_LIB_FLAGS $CXXLIB_FLAGS 2>&1 | grep -viE 'unused|-Wl' || true

echo "== built: fuzz-run/basalt-fuzz =="
