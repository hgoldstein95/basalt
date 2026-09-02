#!/usr/bin/env bash
# Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All rights reserved.
# Released under MIT license as described in the file LICENSE.
# Authors: Michael Hicks

# Build a libFuzzer runtime archive from compiler-rt source into fuzz-run/vendor/.
#
# Needed where the toolchain's clang can instrument (`-fsanitize=fuzzer-no-link`) but ships no
# runtime to link against. That is always macOS (Apple's clang has no libFuzzer at all, and Lean's
# vendored clang 22 ships only `libclang_rt.osx.a`), and any Linux without a system compiler-rt
# fuzzer archive (e.g. a runner with clang but no `libclang-rt`/`compiler-rt` runtimes package).
# compiler-rt's `lib/fuzzer` is standalone C++17 by design (it has its own `build.sh`), so building
# it needs no LLVM checkout or CMake.
#
# `build.sh` calls this automatically when it finds no runtime whose clang major matches the
# instrumenting clang (so `ubuntu-latest`, whose system runtime is a different clang, builds here too);
# run it directly only to re-fetch. The archive excludes `FuzzerMain.cpp` because Lean owns `main`
# (fuzz-run/README.md, "Platforms").
set -euo pipefail
cd "$(dirname "$0")"

LLVM_TAG="${LLVM_TAG:-llvmorg-22.1.8}"      # pinned; any >= 12 exposes LLVMFuzzerRunDriver
VENDOR="$(pwd)/vendor"
SRC="$VENDOR/fuzzer-src"
OUT="$VENDOR/libFuzzerNoMain.a"

# build.sh builds this precisely because no *version-matched* system runtime exists, so the source
# major must equal the instrumenting clang's, which build.sh passes as FUZZ_LLVM_MAJOR. LLVM's tag
# scheme changed mid-stream (`llvmorg-16.0.y` vs `llvmorg-22.1.y`), so we do not synthesize a tag
# from the major — we keep a known-good pinned LLVM_TAG and warn when it drifts, which is the signal
# to bump it (or pass LLVM_TAG explicitly). A warned build still links; it just may carry sancov skew.
tag_major=$(printf '%s' "$LLVM_TAG" | sed -n 's/^llvmorg-\([0-9][0-9]*\).*/\1/p')
if [ -n "${FUZZ_LLVM_MAJOR:-}" ] && [ -n "$tag_major" ] && [ "$FUZZ_LLVM_MAJOR" != "$tag_major" ]; then
  echo "== WARNING: building libFuzzer from LLVM $tag_major ($LLVM_TAG) but the instrumenting clang is"
  echo "==          $FUZZ_LLVM_MAJOR; set LLVM_TAG to a matching release to avoid SanitizerCoverage skew. =="
fi

# The C++ compiler that builds the runtime. libFuzzer is ordinary C++17 with no Lean involvement,
# so the platform's own clang++ is the right tool — `leanc` is a C driver for Lean's emitted code.
CXX="${FUZZ_CXX:-clang++}"

echo "== fetching compiler-rt/lib/fuzzer ($LLVM_TAG) =="
mkdir -p "$SRC"
if [ ! -f "$SRC/FuzzerLoop.cpp" ]; then
  # A sparse, no-history checkout of one directory: the full llvm-project is ~1GB, this is ~1MB.
  tmp=$(mktemp -d)
  git clone --depth 1 --filter=blob:none --sparse --branch "$LLVM_TAG" \
    https://github.com/llvm/llvm-project.git "$tmp/llvm" >/dev/null 2>&1
  git -C "$tmp/llvm" sparse-checkout set compiler-rt/lib/fuzzer >/dev/null 2>&1
  cp "$tmp/llvm/compiler-rt/lib/fuzzer"/*.cpp "$tmp/llvm/compiler-rt/lib/fuzzer"/*.h \
     "$tmp/llvm/compiler-rt/lib/fuzzer"/*.def "$SRC/"
  rm -rf "$tmp"
fi

echo "== compiling (excluding FuzzerMain.cpp: Lean owns main) =="
objs=()
for f in "$SRC"/Fuzzer*.cpp; do
  case "$(basename "$f")" in
    FuzzerMain.cpp) continue ;;
    # Platform files guard their own bodies with #if, so compiling all of them is correct and
    # cheaper than replicating compiler-rt's platform selection here.
  esac
  o="${f%.cpp}.o"
  # -fPIC is required on Linux: `leanc` links the final executable as a PIE (the modern default), and
  # a non-PIC object triggers `relocation R_X86_64_32 cannot be used against local symbol`. It is a
  # no-op on macOS (PIC by default), so it is unconditional here.
  "$CXX" -fPIC -g -O2 -fno-omit-frame-pointer -std=c++17 -c "$f" -o "$o"
  objs+=("$o")
done

rm -f "$OUT"
ar r "$OUT" "${objs[@]}" 2>/dev/null
rm -f "${objs[@]}"

echo "== built: fuzz-run/vendor/libFuzzerNoMain.a =="
