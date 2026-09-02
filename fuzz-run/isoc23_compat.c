/*
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Michael Hicks
*/

/* glibc >= 2.38 renames the integer string-conversion functions: `<stdlib.h>` redirects `strtol`,
   `strtoul`, `strtoll`, `strtoull` (and thus `std::stol`/`stoul`/... via libstdc++'s
   string_conversions.h) to the ISO C23 symbols `__isoc23_strtol` and friends. The libFuzzer runtime
   compiled on such a host therefore references those symbols. But `leanc` links against the Lean
   toolchain's libc, which targets an older glibc baseline for portability and does not export the
   `__isoc23_*` names, so the link fails with `undefined symbol: __isoc23_strtol` on Amazon Linux
   2023 / Ubuntu 24.04 while every classic libc symbol still resolves. (glibc < 2.38 — e.g. Amazon
   Linux 2/2023's older images — neither emits nor needs these, so this file is inert there.)

   Bridge the gap: define the `__isoc23_*` conversions as thin wrappers over the classic functions,
   which are present in every glibc. The `__asm__` labels bind to the classic linker symbols
   directly, dodging the very `strtol -> __isoc23_strtol` header redirect that would otherwise make
   these wrappers call themselves. The definitions are `weak` so that if a link *does* see a libc
   that exports the real symbols, that one wins and there is no clash.

   build.sh compiles this only on Linux: on macOS C symbols carry a leading underscore, so the bare
   `__asm__("strtol")` label would not name the libc function, and glibc's redirect does not exist
   there anyway. */

extern long               basalt_c_strtol   (const char *, char **, int) __asm__("strtol");
extern unsigned long      basalt_c_strtoul  (const char *, char **, int) __asm__("strtoul");
extern long long          basalt_c_strtoll  (const char *, char **, int) __asm__("strtoll");
extern unsigned long long basalt_c_strtoull (const char *, char **, int) __asm__("strtoull");

__attribute__((weak)) long
__isoc23_strtol(const char *nptr, char **endptr, int base) {
  return basalt_c_strtol(nptr, endptr, base);
}
__attribute__((weak)) unsigned long
__isoc23_strtoul(const char *nptr, char **endptr, int base) {
  return basalt_c_strtoul(nptr, endptr, base);
}
__attribute__((weak)) long long
__isoc23_strtoll(const char *nptr, char **endptr, int base) {
  return basalt_c_strtoll(nptr, endptr, base);
}
__attribute__((weak)) unsigned long long
__isoc23_strtoull(const char *nptr, char **endptr, int base) {
  return basalt_c_strtoull(nptr, endptr, base);
}
