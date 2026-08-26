# Per-machine overrides for fuzz-run/build.sh. Copy to `fuzz-run/env.sh` (git-ignored) on a box
# whose toolchain the script's detection cannot handle on its own; it is sourced before detection,
# and every variable it sets suppresses the corresponding probe.
#
# Nothing here is needed on a machine where `leanc` runs and a libFuzzer runtime is either installed
# or vendored — macOS and an ordinary Linux both build with no env.sh at all.

# --- The Amazon Linux 2 / clang 11 box (BasaltFuzz/DESIGN.md Appendix A) -------------------------
# Its two problems are that Lean's vendored clang needs a newer glibc than the host provides, and
# that the C++ runtime libFuzzer wants is off the default link path.
#
# LEAN_CC redirects leanc's underlying C compiler to a wrapper around the system clang 11 that
# injects the vendored libc++/gmp/uv and their rpaths:
#
#     #!/bin/bash
#     exec /usr/bin/clang "$@" -L$TC/lib -Wl,-rpath,$TC/lib -Wl,-rpath,$TC/lib/lean
#
# (`$TC` = `lean --print-prefix`. The same wrapper is needed for `lake exe cache get`.)
#
# export LEAN_CC=$HOME/.local/bin/basalt-leancc
#
# The runtime search already covers /usr/lib64/clang/*/lib/linux, so FUZZER_LIB_FLAGS is usually
# unnecessary; set it to pin one explicitly. clang 11 has no `LLVMFuzzerRunDriver`, and the archive
# probe detects that on its own — set DRIVER_DEFINE only to override the probe.
#
# export FUZZER_LIB_FLAGS="-L/usr/lib64/clang/11.1.0/lib/linux -l:libclang_rt.fuzzer_no_main-x86_64.a"
# export DRIVER_DEFINE=-DBASALT_FUZZ_LEGACY_DRIVER
#
# libstdc++ is not on the default link path there:
# export CXXLIB_FLAGS="-L/usr/lib/gcc/x86_64-redhat-linux/7 -lstdc++"

# --- Other knobs ------------------------------------------------------------------------------
# export CC=leanc                     # the C compile/link driver
# export FUZZER_LIB_SEARCH="/opt/llvm/lib/clang/18/lib/linux"   # extra dirs searched for the runtime
# export BRIDGE_INCLUDES="-isystem /usr/include"                # libc headers for native.c
# export FUZZ_CXX=clang++             # C++ compiler get-libfuzzer.sh builds the runtime with
# export LLVM_TAG=llvmorg-22.1.8      # compiler-rt version get-libfuzzer.sh fetches
