/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
/-!
# Exactly Uniform Draws from `StdGen`

`stdChoose` is the draw shared by the interpretations that sample from a `StdGen`. It reduces by
rejection instead of core's `randNat` modulo, so every value in range is equally likely given the
generator.
-/

/-- The number of distinct values one `stdNext` returns. -/
private def stdSpan : Nat := stdRange.2 - stdRange.1 + 1

/-- Accumulate `stdNext` outputs until they span at least `k` values, rejecting any draw past the
largest multiple of `k` in that span, so the result mod `k` is exactly uniform. Diverges at `k = 0`. -/
private partial def stdBelow (k : Nat) (g : StdGen) : Nat × StdGen :=
  let rec fill (span v : Nat) (g : StdGen) : Nat × Nat × StdGen :=
    if k ≤ span then (span, v, g)
    else
      let (x, g) := stdNext g
      fill (span * stdSpan) (v * stdSpan + (x - stdRange.1)) g
  let (span, v, g) := fill 1 0 g
  if v < span / k * k then (v, g) else stdBelow k g

/-- A draw from `[lo, hi]`, exactly uniform given the generator. `randNat` reduces modulo instead,
which leaves ranges near `2^22` values up to `1/500` off uniform. -/
def stdChoose (g : StdGen) (lo hi : Nat) : Nat × StdGen :=
  let (v, g) := stdBelow (hi - lo + 1) g
  (lo + v % (hi - lo + 1), g)

/-- `stdChoose` stays in `[lo, hi]` for any generator state, so a `choose` built on it needs no
clamp. -/
theorem stdChoose_mem (g : StdGen) {lo hi : Nat} (h : lo ≤ hi) :
    lo ≤ (stdChoose g lo hi).1 ∧ (stdChoose g lo hi).1 ≤ hi := by
  have := Nat.mod_lt (stdBelow (hi - lo + 1) g).1 (show hi - lo + 1 > 0 by omega)
  simp only [stdChoose]
  omega
