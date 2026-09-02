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
  Basalt/PBT/Property Basalt/PBT/Campaign Basalt/PBT/Driver
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
# but the bridge includes <string.h>/<stdlib.h>, and `leanc`'s vendored clang sets `-isysroot` to
# the Lean toolchain (which has no libc headers) and suppresses the platform default, so those
# headers are not found unless fed in: the SDK's include dir on macOS, `/usr/include` on Linux.
# (The Amazon Linux 2 box did not need this because its LEAN_CC wrapper drove the *system* clang,
# whose default sysroot already carries /usr/include; a modern distro's leanc uses the vendored
# clang and does need it.) Override with BRIDGE_INCLUDES.
if [ -z "${BRIDGE_INCLUDES+x}" ]; then
  if [ "$UNAME" = "Darwin" ]; then
    BRIDGE_INCLUDES="-isystem $(xcrun --show-sdk-path)/usr/include"
  else
    BRIDGE_INCLUDES="-isystem /usr/include"
    # Debian/Ubuntu multiarch puts the arch-specific libc headers (e.g. `bits/libc-header-start.h`,
    # which `<stdint.h>` pulls in) under `/usr/include/<triple>`, not `/usr/include/bits`. So on
    # Ubuntu `-isystem /usr/include` alone fails with "bits/libc-header-start.h file not found".
    # `gcc -print-multiarch` names that triple (empty on Fedora/Amazon Linux, whose /usr/include is
    # self-contained), making this a no-op there. Override the whole thing with BRIDGE_INCLUDES.
    ma=$(gcc -print-multiarch 2>/dev/null || true)
    [ -n "$ma" ] && [ -d "/usr/include/$ma" ] && BRIDGE_INCLUDES="$BRIDGE_INCLUDES -isystem /usr/include/$ma"
  fi
fi
: "${BRIDGE_INCLUDES:=}"

# The libFuzzer runtime to link. Preference order:
#   1. FUZZER_LIB_FLAGS from the environment / env.sh (an explicit choice wins).
#   2. A toolchain `libclang_rt.fuzzer_no_main*.a` whose clang major MATCHES the instrumenting clang.
#   3. fuzz-run/vendor/libFuzzerNoMain.a, built from compiler-rt source by ./get-libfuzzer.sh, pinned
#      to Lean's clang major — so it is version-matched too (macOS; and any Linux whose only system
#      runtime is a different clang, e.g. `ubuntu-latest`'s clang 16 vs Lean's clang 22).
#   4. Last resort: a version-*mismatched* system runtime, with a warning (see below).
# `fuzzer_no_main` (not `fuzzer`) is required: we provide LLVMFuzzerTestOneInput and call the driver
# ourselves from Lean's `main`.
#
# Why the major must match: the runtime implements the SanitizerCoverage ABI that the instrumenting
# clang emits calls against. That ABI is broadly stable, but a large skew can leave an
# instrumented-but-uninstrumented-feeling binary — it links and runs, and shallow bugs still fail,
# yet coverage never reaches the runtime (BasaltFuzz/DESIGN.md Appendix A). Matching the major closes
# that gap by construction rather than by trusting cross-version stability.
if [ -z "${FUZZER_LIB_FLAGS+x}" ]; then
  arch=$(uname -m)
  # The major of the clang `leanc` actually drives — via `$CC`, so it honors LEAN_CC (on the Amazon
  # Linux 2 box this is the system clang 11, not Lean's vendored 22). $CC emits __clang_major__.
  instr_major=$(echo | $CC -dM -E - 2>/dev/null | sed -n 's/^#define __clang_major__ \([0-9][0-9]*\).*/\1/p')

  # Two runtime-dir layouts coexist: the legacy `.../lib/linux/libclang_rt.fuzzer_no_main-<arch>.a`
  # (clang <= 13, the Amazon Linux 2 box) and the per-target-triple
  # `.../lib/<triple>/libclang_rt.fuzzer_no_main.a` (clang >= 14, e.g. Amazon Linux 2023's
  # `/usr/lib/clang/22/lib/x86_64-amazon-linux-gnu/`). Search both under every prefix; the `-d`
  # guard below skips the non-directory expansions. `matched` takes the first archive whose clang
  # major equals the instrumenting one; `any_host` remembers the first host-arch archive of any
  # version, used only as a last resort.
  matched=""; any_host=""
  for d in ${FUZZER_LIB_SEARCH:-} \
           "$TC"/lib/clang/*/lib/linux "$TC"/lib/clang/*/lib/* \
           /usr/lib64/clang/*/lib/linux /usr/lib/clang/*/lib/linux \
           /usr/lib64/clang/*/lib/* /usr/lib/clang/*/lib/* \
           /usr/lib/llvm-*/lib/clang/*/lib/linux /usr/lib/llvm-*/lib/clang/*/lib/*; do
    [ -d "$d" ] || continue
    # Only the *host-arch* archive: the unsuffixed name (per-triple dirs encode the arch in the dir)
    # or the `-<arch>` legacy name. A bare `*.a` glob would also match the 32-bit `-i386` sibling
    # that ships alongside on Debian/Ubuntu and pick it by enumeration order — a 32-bit runtime then
    # fails to link into the 64-bit executable.
    for a in "$d/libclang_rt.fuzzer_no_main.a" "$d/libclang_rt.fuzzer_no_main-$arch.a"; do
      [ -f "$a" ] || continue
      [ -n "$any_host" ] || any_host="$a"
      amaj=$(printf '%s' "$a" | sed -n 's#.*/clang/\([0-9][0-9]*\).*#\1#p')
      if [ -n "$instr_major" ] && [ "$amaj" = "$instr_major" ]; then matched="$a"; break 2; fi
    done
  done

  if [ -n "$matched" ]; then
    FUZZER_LIB_FLAGS="$matched"
  elif [ -f fuzz-run/vendor/libFuzzerNoMain.a ] || FUZZ_LLVM_MAJOR="$instr_major" fuzz-run/get-libfuzzer.sh; then
    # No version-matched system runtime — build one from source (get-libfuzzer.sh targets Lean's clang
    # major, so the archive is matched and skew-free). Preferred over the mismatched `any_host`.
    FUZZER_LIB_FLAGS="$ROOT/fuzz-run/vendor/libFuzzerNoMain.a"
  elif [ -n "$any_host" ]; then
    echo "== WARNING: no libFuzzer runtime matches the instrumenting clang ${instr_major:-?} and none"
    echo "==          could be built from source; falling back to $any_host. If chain-n coverage is"
    echo "==          degraded, this skew is why — install a matching compiler-rt or set FUZZER_LIB_FLAGS. =="
    FUZZER_LIB_FLAGS="$any_host"
  else
    echo "no libFuzzer runtime found and none could be built" >&2; exit 1
  fi
fi

# The C++ runtime libFuzzer itself needs: libc++ on macOS, GNU libstdc++ with a toolchain-provided
# runtime on Linux (its symbols are the `__cxx11` GNU ABI). Two Linux wrinkles, both worked around
# by naming the newest libstdc++.so by *full path*:
#   - A bare `-lstdc++` is silently dropped: leanc's vendored clang already appends `-lc++`, so lld
#     never links a second C++ runtime by `-l`, and the archive's std:: symbols stay undefined.
#     A `.so` given by path is an unconditional input and always contributes its symbols.
#   - The runtime is built by a recent clang against a recent libstdc++, so an older one leaves
#     undefined symbols (gcc 11's lacks `std::__glibcxx_assert_fail`, added in gcc 12). Newer
#     libstdc++ is ABI-forward-compatible, so the newest installed is always the safe choice — the
#     same one the system clang that built the runtime would pick.
# Override with CXXLIB_FLAGS (Appendix A's Amazon Linux 2 box pins its own -L/-lstdc++).
if [ -z "${CXXLIB_FLAGS+x}" ]; then
  if [ "$UNAME" = "Darwin" ]; then
    CXXLIB_FLAGS="-lc++"
  else
    newest_libstdcxx=$(ls /usr/lib/gcc/*/*/libstdc++.so 2>/dev/null | grep -v '/32/' | sort -V | tail -1)
    CXXLIB_FLAGS="${newest_libstdcxx:--lstdc++}"
  fi
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

# On glibc >= 2.38 (Ubuntu 24.04, etc.) the runtime references `__isoc23_strtol`/`_strtoul` that
# leanc's older-baseline libc does not export; this shim supplies them (fuzz-run/isoc23_compat.c).
# Linux-only: its `__asm__` symbol labels assume no leading underscore, and glibc's redirect is what
# it targets. Inert where those symbols already resolve (its defs are weak).
if [ "$UNAME" != "Darwin" ]; then
  $CC -O1 -c fuzz-run/isoc23_compat.c -o "$OUT/isoc23_compat.o"
  OBJS+=("$OUT/isoc23_compat.o")
fi

# `-fsanitize=fuzzer-no-link` is deliberately absent here: it is a *compile-time* instrumentation
# flag, and at link time it also pulls in a ubsan dylib that Lean's vendored clang does not ship
# (the link fails with "cannot open ... libclang_rt.ubsan_osx_dynamic.dylib"). The runtime archive
# supplies every symbol the link actually needs.
echo "== link =="
# Capture rather than pipe: a previous `... | grep -v ... || true` swallowed the linker's exit code,
# so a *failed* link still printed "built" and left no binary — the failure only surfaced later as
# `fuzz-run/basalt-fuzz: No such file or directory`. Filter the noise for display, but fail loudly on
# a nonzero status or a missing binary.
rm -f fuzz-run/basalt-fuzz
if ! $CC "${OBJS[@]}" -o fuzz-run/basalt-fuzz $FUZZER_LIB_FLAGS $CXXLIB_FLAGS > "$OUT/link.log" 2>&1; then
  grep -viE 'unused|-Wl' "$OUT/link.log" >&2 || true
  echo "== link FAILED (runtime: $FUZZER_LIB_FLAGS; cxxlib: $CXXLIB_FLAGS) ==" >&2
  exit 1
fi
grep -viE 'unused|-Wl' "$OUT/link.log" || true
[ -x fuzz-run/basalt-fuzz ] || { echo "== link reported success but produced no binary ==" >&2; exit 1; }

echo "== built: fuzz-run/basalt-fuzz =="
