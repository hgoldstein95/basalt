#!/usr/bin/env bash
# Build a libFuzzer runtime archive from compiler-rt source into fuzz-run/vendor/.
#
# Needed where the toolchain's clang can instrument (`-fsanitize=fuzzer-no-link`) but ships no
# runtime to link against — the macOS case: Apple's clang has no libFuzzer at all, and Lean's
# vendored clang 22 ships only `libclang_rt.osx.a`. compiler-rt's `lib/fuzzer` is standalone C++17
# by design (it has its own `build.sh`), so building it needs no LLVM checkout or CMake.
#
# `build.sh` calls this automatically when it finds no runtime; run it directly only to re-fetch.
# The archive excludes `FuzzerMain.cpp` because Lean owns `main` (BasaltFuzz/DESIGN.md §5).
set -euo pipefail
cd "$(dirname "$0")"

LLVM_TAG="${LLVM_TAG:-llvmorg-22.1.8}"      # pinned; any >= 12 exposes LLVMFuzzerRunDriver
VENDOR="$(pwd)/vendor"
SRC="$VENDOR/fuzzer-src"
OUT="$VENDOR/libFuzzerNoMain.a"

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
  "$CXX" -g -O2 -fno-omit-frame-pointer -std=c++17 -c "$f" -o "$o"
  objs+=("$o")
done

rm -f "$OUT"
ar r "$OUT" "${objs[@]}" 2>/dev/null
rm -f "${objs[@]}"

echo "== built: fuzz-run/vendor/libFuzzerNoMain.a =="
