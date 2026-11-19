/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Michael Hicks
-/
module

/-!
# The bytes of a draw

`FuzzGen`'s byte format, both ways: how many bytes a draw of `k` outcomes reads (`bytesFor`), reading
them big-endian with `0` past the end of the input (`readBEFrom`), and writing a value's bytes
(`pushBE`). `readBEFrom_pushBE` proves that bytes written are read back as the value. Every module
that reads or writes a draw's bytes uses these.
-/

public section

namespace Basalt.Fuzz

/-- Bits needed to distinguish `k` outcomes (0 when `k ≤ 1`). -/
@[expose] def bitsFor (k : Nat) : Nat :=
  if k ≤ 1 then 0 else (k - 1).log2 + 1

/-- Bytes needed to distinguish `k` outcomes: the smallest count covering `bitsFor k`. Reading the
*fewest* bytes per range keeps a tight, mutation-friendly map from input bytes to choices. -/
@[expose] def bytesFor (k : Nat) : Nat := (bitsFor k + 7) / 8

/-- The byte at `i`, or `0` past the end: an input is zero-extended rather than exhausted, which is
what keeps `choose` total. -/
@[expose] def byteAt (buf : ByteArray) (i : Nat) : UInt8 :=
  if i < buf.size then buf.get! i else 0

/-- `n` bytes of `buf` from `off`, big-endian, onto `acc` (`byteAt`, so `0` past the end). -/
@[expose] def readBEFrom (buf : ByteArray) (acc off : Nat) : Nat → Nat
  | 0 => acc
  | n + 1 => readBEFrom buf (acc * 256 + (byteAt buf off).toNat) (off + 1) n

/-- `raw`'s low `n` bytes, big-endian, appended to `b`: what `readBEFrom` reads back
(`readBEFrom_pushBE`). -/
@[expose] def pushBE (b : ByteArray) : Nat → Nat → ByteArray
  | 0, _ => b
  | n + 1, raw => pushBE (b.push (raw / 256 ^ n % 256).toUInt8) n raw

/-! ## Facts about the format -/

theorem get!_eq (b : ByteArray) (i : Nat) (h : i < b.size) : b.get! i = b.data[i]'h := by
  cases b with | mk bs =>
  show bs[i]! = bs[i]
  exact getElem!_pos bs i h

theorem get!_push_lt (b : ByteArray) (x : UInt8) (i : Nat) (h : i < b.size) :
    (b.push x).get! i = b.get! i := by
  rw [get!_eq _ _ (by simp [ByteArray.size_push]; omega), get!_eq _ _ h]
  simp [ByteArray.push, Array.getElem_push, h]

theorem get!_push_size (b : ByteArray) (x : UInt8) : (b.push x).get! b.size = x := by
  rw [get!_eq _ _ (by simp [ByteArray.size_push])]
  simp [ByteArray.push, Array.getElem_push]

theorem get!_append_lt (a c : ByteArray) (i : Nat) (h : i < a.size) :
    (a ++ c).get! i = a.get! i := by
  rw [get!_eq _ _ (by simp [ByteArray.size_append]; omega), get!_eq _ _ h]
  have := @ByteArray.getElem_append_left i a c (by simp [ByteArray.size_append]; omega) h
  simpa [ByteArray.getElem_eq_getElem_data] using this

theorem size_pushBE (b : ByteArray) (n raw : Nat) : (pushBE b n raw).size = b.size + n := by
  induction n generalizing b with
  | zero => rfl
  | succ n ih => simp only [pushBE, ih, ByteArray.size_push]; omega

theorem get!_pushBE_lt (b : ByteArray) (n raw i : Nat) (h : i < b.size) :
    (pushBE b n raw).get! i = b.get! i := by
  induction n generalizing b with
  | zero => rfl
  | succ n ih =>
    simp only [pushBE]
    rw [ih _ (by simp [ByteArray.size_push]; omega), get!_push_lt _ _ _ h]

theorem get!_pushBE (b : ByteArray) (n raw i : Nat) (h : i < n) :
    (pushBE b n raw).get! (b.size + i) = (raw / 256 ^ (n - 1 - i) % 256).toUInt8 := by
  induction n generalizing b i with
  | zero => omega
  | succ n ih =>
    simp only [pushBE]
    cases i with
    | zero =>
      rw [get!_pushBE_lt _ _ _ _ (by simp [ByteArray.size_push]), Nat.add_zero, get!_push_size]
      simp
    | succ i =>
      have := ih (b.push (raw / 256 ^ n % 256).toUInt8) i (by omega)
      rw [ByteArray.size_push] at this
      rw [show b.size + (i + 1) = b.size + 1 + i by omega, this,
        show n + 1 - 1 - (i + 1) = n - 1 - i by omega]

/-- `n` bytes at `off` holding `raw`'s big-endian digits read as `raw`'s low `n` bytes. -/
theorem readBEFrom_digits (raw : Nat) (buf : ByteArray) : ∀ (n acc off : Nat),
    off + n ≤ buf.size →
    (∀ i < n, buf.get! (off + i) = (raw / 256 ^ (n - 1 - i) % 256).toUInt8) →
    readBEFrom buf acc off n = acc * 256 ^ n + raw % 256 ^ n
  | 0, acc, _, _, _ => by simp [readBEFrom, Nat.mod_one]
  | n + 1, acc, off, hn, hd => by
    have h0 := hd 0 (by omega)
    simp only [Nat.add_zero, Nat.add_sub_cancel, Nat.sub_zero] at h0
    have ih := readBEFrom_digits raw buf n (acc * 256 + raw / 256 ^ n % 256) (off + 1) (by omega)
      (fun i hi => by
        have := hd (i + 1) (by omega)
        rw [show off + 1 + i = off + (i + 1) by omega, this,
          show n + 1 - 1 - (i + 1) = n - 1 - i by omega])
    simp only [readBEFrom, byteAt, show off < buf.size by omega, ite_true, h0]
    have hb : ((raw / 256 ^ n % 256).toUInt8).toNat = raw / 256 ^ n % 256 := by
      simp
    rw [hb, ih]
    rw [Nat.mod_pow_succ, Nat.pow_succ, Nat.add_mul, Nat.mul_assoc, Nat.mul_comm 256 (256 ^ n),
      Nat.mul_comm (raw / 256 ^ n % 256) (256 ^ n)]
    omega

/-- **The format both ways.** The bytes `pushBE` appends to `b`, followed by anything, are read back
by `readBEFrom` as `raw`'s low `n` bytes. -/
theorem readBEFrom_pushBE (b post : ByteArray) (n raw : Nat) :
    readBEFrom (pushBE b n raw ++ post) 0 b.size n = raw % 256 ^ n := by
  rw [readBEFrom_digits raw _ n 0 b.size (by simp [ByteArray.size_append, size_pushBE])
    (fun i hi => by
      rw [get!_append_lt _ _ _ (by rw [size_pushBE]; omega), get!_pushBE _ _ _ _ hi])]
  simp

/-- `range` outcomes fit in `bytesFor range` bytes. -/
theorem le_pow_bytesFor (range : Nat) : range ≤ 256 ^ bytesFor range := by
  unfold bytesFor bitsFor
  split
  · simp; omega
  · have h1 := @Nat.lt_log2_self (range - 1)
    have h2 : 2 ^ ((range - 1).log2 + 1) ≤ 256 ^ (((range - 1).log2 + 1 + 7) / 8) := by
      rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]
      exact Nat.pow_le_pow_right (by omega) (by omega)
    omega

end Basalt.Fuzz
