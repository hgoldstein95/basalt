/*
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Michael Hicks
*/
/* Lean `Nat` comparisons, made visible to `--cmp`. Force-included (`-include`) into the fuzz
   targets' C (lakefile.lean): for small values `lean_nat_eq`/`lt`/`le` compare tagged pointers, so the operands
   `trace-cmp` reports are not the values, and under `--cmp` (`basalt_nat_hook_on`, set by `native.c`;
   weak, so a binary without the bridge links and never calls it) each wrapper hands the untagged
   operands to `basalt_nat_cmp` first. Lean's generated code is unchanged: the macros below rename the
   calls it makes after its own `#include <lean/lean.h>`. */
#ifndef BASALT_NAT_HOOK_H
#define BASALT_NAT_HOOK_H
#include <lean/lean.h>

extern int basalt_nat_hook_on __attribute__((weak));
void basalt_nat_cmp(uint64_t, uint64_t) __attribute__((weak));

static inline LEAN_ALWAYS_INLINE void basalt_nat_seen(b_lean_obj_arg a, b_lean_obj_arg b) {
  if (&basalt_nat_hook_on && basalt_nat_hook_on && lean_is_scalar(a) && lean_is_scalar(b))
    basalt_nat_cmp((uint64_t)lean_unbox(a), (uint64_t)lean_unbox(b));
}
static inline LEAN_ALWAYS_INLINE bool basalt_nat_eq(b_lean_obj_arg a, b_lean_obj_arg b) {
  basalt_nat_seen(a, b); return lean_nat_eq(a, b);
}
static inline LEAN_ALWAYS_INLINE bool basalt_nat_ne(b_lean_obj_arg a, b_lean_obj_arg b) {
  basalt_nat_seen(a, b); return lean_nat_ne(a, b);
}
static inline LEAN_ALWAYS_INLINE bool basalt_nat_lt(b_lean_obj_arg a, b_lean_obj_arg b) {
  basalt_nat_seen(a, b); return lean_nat_lt(a, b);
}
static inline LEAN_ALWAYS_INLINE bool basalt_nat_le(b_lean_obj_arg a, b_lean_obj_arg b) {
  basalt_nat_seen(a, b); return lean_nat_le(a, b);
}
static inline LEAN_ALWAYS_INLINE uint8_t basalt_nat_dec_eq(b_lean_obj_arg a, b_lean_obj_arg b) {
  basalt_nat_seen(a, b); return lean_nat_dec_eq(a, b);
}
static inline LEAN_ALWAYS_INLINE uint8_t basalt_nat_dec_lt(b_lean_obj_arg a, b_lean_obj_arg b) {
  basalt_nat_seen(a, b); return lean_nat_dec_lt(a, b);
}
static inline LEAN_ALWAYS_INLINE uint8_t basalt_nat_dec_le(b_lean_obj_arg a, b_lean_obj_arg b) {
  basalt_nat_seen(a, b); return lean_nat_dec_le(a, b);
}
#define lean_nat_eq basalt_nat_eq
#define lean_nat_ne basalt_nat_ne
#define lean_nat_lt basalt_nat_lt
#define lean_nat_le basalt_nat_le
#define lean_nat_dec_eq basalt_nat_dec_eq
#define lean_nat_dec_lt basalt_nat_dec_lt
#define lean_nat_dec_le basalt_nat_dec_le
#endif
