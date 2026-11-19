/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Michael Hicks
-/
module

public import Basalt.Fuzz.Basic
public import SplitMix.Lemmas

/-!
# The `RecordGen` interpretation

`RecordGen` makes each choice uniformly at random, as `IO` does, and records a `FuzzGen` buffer that
decodes to the same choices: a random run that `FuzzGen` replays exactly, and so can seed a
libFuzzer corpus. A hybrid campaign's random rounds run at it (`runOneRandom`), so that a *find*, a
test that reached a new feature, can be handed to libFuzzer as a seed (`Basalt/Fuzz/Cover.lean`).
`readNat_recordDraw` proves the replay per draw (one `choose`, `Basalt/Fuzz/Basic.lean`); a whole
run's agreement is a free theorem of the generator's polymorphism, so it is pinned by
`BasaltTest/Fuzz.lean` instead.
-/

public section

namespace Basalt.Fuzz

open Basalt.PBT

/-- A `RecordGen` run's state: the PRNG it draws from and the bytes recorded so far. -/
structure RecordState where
  rng : SplitMix
  bytes : ByteArray

/-- A random interpretation of `Gen` that records, for every `choose`, bytes `FuzzGen` decodes back
to the same value. The `Option` base is `FuzzGen`'s, for the same reason. -/
abbrev RecordGen (α : Type) := StateT RecordState Option α

instance : Inhabited (RecordGen α) :=
  ⟨fun _ => none⟩

/-- One draw: `raw` is uniform over `[0, range · ⌊256ⁿ / range⌋)`, `n = bytesFor range`, and is
written as the `n` bytes `FuzzGen`'s `choose` reads, which decode to `raw % range`. That value is
uniform, as at `IO`, since the interval holds whole copies of `range`. So `raw = d + range · k` for
the value `d` and a random `k`, and a seed's bytes are about uniform. Writing the value itself
(`k = 0`) was measured to be worse: libFuzzer's byte edits shift which bytes a draw reads, and bytes
that all decode small hand every shifted draw a low value. On the BasaltBench repository's two Cedar
generators (15 hybrid campaigns each) it cost about 25 edges in 1M tests; on `fuzz-run`'s own
benchmarks it made no consistent difference. -/
def recordDraw (s : RecordState) (range : Nat) : Nat × RecordState :=
  let n := bytesFor range
  let (raw, g) := s.rng.randNat 0 (range * (256 ^ n / range) - 1)
  (raw, { rng := g, bytes := pushBE s.bytes n raw })

/-- `choose` returns exactly what `FuzzGen`'s `choose` computes from the recorded bytes. -/
instance : RandomChoice RecordGen where
  choose lo hi h := do
    let s ← get
    let range := hi - lo + 1
    let (d, s') := recordDraw s range
    set s'
    have := Nat.mod_lt d (show range > 0 by omega)
    pure (ULift.up ⟨lo + d % range, by omega⟩)

/-- `RecordGen` has everything a generator needs. -/
example : Gen RecordGen := inferInstance

/-- Run a property once at `RecordGen` from PRNG state `g`: its outcome, the `FuzzGen` buffer that
replays it, and the PRNG state for the next run. The `none` case is `runOne`'s. -/
def runRecord (T : PropM RecordGen Unit) (g : SplitMix) : TestOutcome × ByteArray × SplitMix :=
  match (runProp T).run { rng := g, bytes := ByteArray.emptyWithCapacity 64 } with
  | some (outcome, s) => (outcome, s.bytes, s.rng)
  | none              => (Except.error .discard, ByteArray.empty, g.split.2)

/-- **The decode contract, per draw.** The bytes one `RecordGen` draw appends, followed by anything,
are read back by `FuzzGen`'s `readNat` as the value it drew — so `FuzzGen`'s `choose` makes that
same choice and leaves its cursor where the next draw's bytes begin. The bytes are in the buffer,
so nothing past it is read. -/
theorem readNat_recordDraw (s : RecordState) (range : Nat) (hr : 0 < range) (post : ByteArray) :
    readNat ⟨(recordDraw s range).2.bytes ++ post, s.bytes.size⟩ (bytesFor range) =
      ((recordDraw s range).1,
       ⟨(recordDraw s range).2.bytes ++ post, s.bytes.size + bytesFor range⟩) := by
  have hpow := le_pow_bytesFor range
  have hd := SplitMix.randNat_mem s.rng
    (Nat.zero_le (range * (256 ^ bytesFor range / range) - 1))
  generalize hdg : s.rng.randNat 0 (range * (256 ^ bytesFor range / range) - 1) = dg at hd
  obtain ⟨d, g⟩ := dg
  simp only at hd
  have hm : range * (256 ^ bytesFor range / range) ≤ 256 ^ bytesFor range := by
    rw [Nat.mul_comm]; exact Nat.div_mul_le_self _ _
  have hraw : d < 256 ^ bytesFor range := by omega
  simp only [recordDraw, hdg, readNat, readBEFrom_pushBE, Nat.mod_eq_of_lt hraw]

end Basalt.Fuzz
