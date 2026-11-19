/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Michael Hicks
-/
module

/-!
# The bytes of a draw, and a run's trace of its draws

`FuzzGen`'s byte format, both ways, and everything built on it to bridge a generator's draws to the
bytes libFuzzer mutates. Its sections:

* **A draw's bytes:** how many a draw of `k` outcomes reads (`bytesFor`); reading them big-endian
  with `0` past the end of the input (`byteAt`, `readBEFrom`); writing a value's bytes, appended
  (`pushBE`) or over an input (`writeBE`).
* **Varints**, which a `--cmp` trace is made of, both ways (`pushVarint`, `readVarint`). A varint
  (LEB128, as in DWARF and WebAssembly) writes a number seven bits to a byte, least significant
  first, with the high bit of every byte but the last set to say another follows, so a number below
  128 takes one byte.
* **A run's trace and its draws** (`--cmp`): `Draw`, and `decode`, which recovers a run's draws from
  its trace (`FuzzState.trace`) and its input.
* **Planting a value** into a draw's bytes (`plant`).
* **For the C bridge:** `decodeWords` and `plantWords`, which `native.c` calls.

The facts at the end prove that what is written is read back (`readBEFrom_pushBE`,
`readBEFrom_digits`, `readVarint_pushVarint`), that a trace decodes to the draws it holds
(`decode_encode`; `decode_drawStep`, beside `drawStep` in `Basalt/Fuzz/Basic.lean`, that a run's
trace holds its draws), and that a plant leaves the draw holding the value and every byte before it
(`plant_value`, `plant_prefix`, `plant_size`).
-/

public section

namespace Basalt.Fuzz

/-! ## A draw's bytes -/

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

/-- `raw`'s low `n` bytes, big-endian, written over `b` from position `off`. -/
def writeBE (b : ByteArray) (off : Nat) : Nat → Nat → ByteArray
  | 0, _ => b
  | n + 1, raw => writeBE (b.set! off (raw / 256 ^ n % 256).toUInt8) (off + 1) n raw

/-! ## Varints -/

/-- `x` appended to `b` as a varint (LEB128): seven bits per byte, least significant first, the high
bit set on every byte but the last. How `FuzzState.trace` stores a draw's bounds compactly. -/
@[expose] def pushVarint (b : ByteArray) (x : Nat) : ByteArray :=
  if x < 128 then b.push x.toUInt8 else pushVarint (b.push (x % 128 + 128).toUInt8) (x / 128)
termination_by x
decreasing_by omega

/-- The varint at `i` in `b`, `pushVarint`'s inverse: its value and the position after it,
reading at most `fuel` bytes. -/
def readVarint (b : ByteArray) (i : Nat) : Nat → Nat × Nat
  | 0 => (0, i)
  | fuel + 1 =>
    let c := (b.get! i).toNat
    if c < 128 then (c, i + 1)
    else
      let r := readVarint b (i + 1) fuel
      (c - 128 + 128 * r.1, r.2)

/-! ## A run's trace and its draws -/

/-- One draw of a run (`Basalt/Fuzz/Basic.lean`): its range `[lo, hi]`, where its bytes start in
the input, and the value they decode to. -/
structure Draw where
  lo : Nat
  hi : Nat
  offset : Nat
  value : Nat
  deriving Repr, BEq

/-- The value the bytes at `offset` in `buf` decode to, for a draw in `[lo, hi]`: what `choose`
returns when it reads them. -/
@[expose] def drawValue (buf : ByteArray) (lo hi offset : Nat) : Nat :=
  lo + readBEFrom buf 0 offset (bytesFor (hi - lo + 1)) % (hi - lo + 1)

/-! ## Decoding a trace -/

/-- The draws of trace `trace` from its position `i` on, the first of them at input offset `off`.
Each entry is a draw's `lo` and `hi - lo`; its bytes start where the previous draw's end. An entry
takes at least one byte, so `trace`'s size bounds the entries, and `fuel`. -/
def decodeFrom (trace buf : ByteArray) : Nat → Nat → Nat → List Draw
  | 0, _, _ => []
  | fuel + 1, i, off =>
    if i < trace.size then
      let (lo, i) := readVarint trace i trace.size
      let (span, i) := readVarint trace i trace.size
      ⟨lo, lo + span, off, drawValue buf lo (lo + span) off⟩ ::
        decodeFrom trace buf fuel i (off + bytesFor (span + 1))
    else []

/-- The draws of a run, from its trace (`FuzzState.trace`) and its input `buf`. -/
def decode (trace buf : ByteArray) : List Draw := decodeFrom trace buf trace.size 0 0

/-! ## Planting a value -/

/-- `n` zero bytes. -/
def zeros (n : Nat) : ByteArray := ⟨Array.replicate n 0⟩

/-- `buf` with the bytes of a draw in `[lo, hi]` at `offset` rewritten to decode to `v`, first
extended with zeros if it ends before them (as `byteAt` reads them); `none` if `v` is outside the
range or the draw's bytes would pass `maxSize`. -/
def plant (buf : ByteArray) (lo hi offset v maxSize : Nat) : Option ByteArray :=
  let w := bytesFor (hi - lo + 1)
  if lo ≤ v ∧ v ≤ hi ∧ offset + w ≤ maxSize then
    let b := if buf.size < offset + w then buf ++ zeros (offset + w - buf.size) else buf
    some (writeBE b offset w (v - lo))
  else none

/-! ## For the C bridge -/

/-- `x`'s low 64 bits appended to `b`, little-endian. -/
def pushLE64 (b : ByteArray) (x : Nat) : ByteArray :=
  let w := x.toUInt64
  b.push w.toUInt8 |>.push (w >>> 8).toUInt8 |>.push (w >>> 16).toUInt8 |>.push (w >>> 24).toUInt8
    |>.push (w >>> 32).toUInt8 |>.push (w >>> 40).toUInt8 |>.push (w >>> 48).toUInt8
    |>.push (w >>> 56).toUInt8

/-- A draw as the C bridge reads it, appended to `b`: four 64-bit little-endian words (`lo`, `hi`,
the value, the offset), or nothing for a draw whose range does not fit a word. -/
@[inline] def packDraw (b : ByteArray) (d : Draw) : ByteArray :=
  if d.hi < 2 ^ 64 then pushLE64 (pushLE64 (pushLE64 (pushLE64 b d.lo) d.hi) d.value) d.offset
  else b

/-- `decodeFrom`, packing each draw as it goes rather than building a list (`decodeWords_eq`). -/
def decodeWordsFrom (trace buf : ByteArray) : Nat → Nat → Nat → ByteArray → ByteArray
  | 0, _, _, acc => acc
  | fuel + 1, i, off, acc =>
    if i < trace.size then
      let (lo, i) := readVarint trace i trace.size
      let (span, i) := readVarint trace i trace.size
      decodeWordsFrom trace buf fuel i (off + bytesFor (span + 1))
        (packDraw acc ⟨lo, lo + span, off, drawValue buf lo (lo + span) off⟩)
    else acc

/-- `decode` for the C bridge: its draws packed (`packDraw`), as `decodeWords_eq` states. -/
@[export basalt_decode_draws]
def decodeWords (trace buf : ByteArray) : ByteArray :=
  decodeWordsFrom trace buf trace.size 0 0 (ByteArray.emptyWithCapacity 256)

/-- `plant` for the C bridge: the new input, or an empty array for `none`. A plant into a draw of
more than one outcome writes at least one byte, so its result is never empty. -/
@[export basalt_plant_draw]
def plantWords (buf : ByteArray) (lo hi offset v maxSize : UInt64) : ByteArray :=
  (plant buf lo.toNat hi.toNat offset.toNat v.toNat maxSize.toNat).getD .empty

/-! ## Facts: a draw's bytes and varints -/

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

theorem get!_eq_getElem! (b : ByteArray) (i : Nat) : b.get! i = b[i]! := by
  by_cases h : i < b.size
  · rw [get!_eq _ _ h, getElem!_pos b i h]; rfl
  · rw [getElem!_neg b i h]
    cases b with | mk bs =>
    show bs[i]! = default
    exact getElem!_neg bs i h

theorem get!_out (b : ByteArray) (i : Nat) (h : b.size ≤ i) : b.get! i = 0 := by
  rw [get!_eq_getElem!, getElem!_neg b i (by omega)]; rfl

theorem get!_append_right (a c : ByteArray) (i : Nat) :
    (a ++ c).get! (a.size + i) = c.get! i := by
  by_cases h : i < c.size
  · rw [get!_eq _ _ (by simp [ByteArray.size_append]; omega), get!_eq _ _ h]
    have := @ByteArray.getElem_append_right (a.size + i) a c
      (by simp [ByteArray.size_append]; omega) (by omega)
    simp only [Nat.add_sub_cancel_left] at this
    simp [ByteArray.getElem_eq_getElem_data] at this ⊢
  · rw [get!_out _ _ (by simp [ByteArray.size_append]; omega), get!_out _ _ (by omega)]

theorem get!_set!_self (b : ByteArray) (i : Nat) (x : UInt8) (h : i < b.size) :
    (b.set! i x).get! i = x := by
  rw [get!_eq_getElem!]; exact ByteArray.getElem!_set!_self b i x h

theorem get!_set!_ne (b : ByteArray) (i j : Nat) (x : UInt8) (h : i ≠ j) :
    (b.set! i x).get! j = b.get! j := by
  rw [get!_eq_getElem!, get!_eq_getElem!]; exact ByteArray.getElem!_set!_ne b i j x h

theorem append_assoc (a b c : ByteArray) : a ++ b ++ c = a ++ (b ++ c) :=
  ByteArray.ext (by simp [ByteArray.data_append, Array.append_assoc])

theorem push_append (a b : ByteArray) (x : UInt8) : (a ++ b).push x = a ++ b.push x :=
  ByteArray.ext (by simp [ByteArray.data_append, ByteArray.push])

theorem pushVarint_lt (b : ByteArray) (x : Nat) (h : x < 128) :
    pushVarint b x = b.push x.toUInt8 := by
  rw [pushVarint]; simp [h]

theorem pushVarint_ge (b : ByteArray) (x : Nat) (h : ¬ x < 128) :
    pushVarint b x = pushVarint (b.push (x % 128 + 128).toUInt8) (x / 128) := by
  rw [pushVarint]; simp [h]

theorem pushVarint_append (x : Nat) :
    ∀ (a b : ByteArray), pushVarint (a ++ b) x = a ++ pushVarint b x := by
  induction x using Nat.strongRecOn with
  | _ x ih =>
  intro a b
  by_cases h : x < 128
  · rw [pushVarint_lt _ _ h, pushVarint_lt _ _ h, push_append]
  · rw [pushVarint_ge _ _ h, pushVarint_ge _ _ h, push_append, ih (x / 128) (by omega)]

theorem pushVarint_empty (a : ByteArray) (x : Nat) :
    pushVarint a x = a ++ pushVarint .empty x := by
  rw [← pushVarint_append, ByteArray.append_empty]

theorem size_pushVarint_pos (x : Nat) : 0 < (pushVarint .empty x).size := by
  by_cases h : x < 128
  · rw [pushVarint_lt _ _ h]; simp [ByteArray.size_push]
  · rw [pushVarint_ge _ _ h, pushVarint_empty, ByteArray.size_append]; simp [ByteArray.size_push]
    omega

theorem size_pushVarint (x : Nat) (h : 128 ≤ x) :
    (pushVarint .empty x).size = 1 + (pushVarint .empty (x / 128)).size := by
  rw [pushVarint_ge _ _ (by omega), pushVarint_empty, ByteArray.size_append]
  simp [ByteArray.size_push]

theorem get!_append_size (a c : ByteArray) : (a ++ c).get! a.size = c.get! 0 := by
  simpa using get!_append_right a c 0

/-- A varint reads back as the value it encodes, whatever precedes and follows it. -/
theorem readVarint_pushVarint (x : Nat) :
    ∀ (a c : ByteArray) (fuel : Nat), (pushVarint .empty x).size ≤ fuel →
      readVarint (a ++ pushVarint .empty x ++ c) a.size fuel =
        (x, a.size + (pushVarint .empty x).size) := by
  induction x using Nat.strongRecOn with
  | _ x ih =>
  intro a c fuel hf
  obtain _ | fuel := fuel
  · have := size_pushVarint_pos x; omega
  by_cases hx : x < 128
  · have hv := pushVarint_lt ByteArray.empty x hx
    have hb : (a ++ pushVarint .empty x ++ c).get! a.size = x.toUInt8 := by
      rw [append_assoc, get!_append_size, hv, get!_append_lt _ _ _ (by simp [ByteArray.size_push])]
      simpa using get!_push_size ByteArray.empty x.toUInt8
    have hn : x.toUInt8.toNat = x := by simp; omega
    simp only [readVarint]
    rw [hb, hn, hv]
    simp [hx, ByteArray.size_push]
  · have hv : pushVarint .empty x =
        ByteArray.empty.push (x % 128 + 128).toUInt8 ++ pushVarint .empty (x / 128) := by
      rw [pushVarint_ge _ _ hx, pushVarint_empty]
    have hb : (a ++ pushVarint .empty x ++ c).get! a.size = (x % 128 + 128).toUInt8 := by
      rw [append_assoc, get!_append_size, hv, append_assoc,
        get!_append_lt _ _ _ (by simp [ByteArray.size_push])]
      simpa using get!_push_size ByteArray.empty (x % 128 + 128).toUInt8
    have hn : (x % 128 + 128).toUInt8.toNat = x % 128 + 128 := by simp; omega
    have hs := size_pushVarint x (by omega)
    have hrest := ih (x / 128) (by omega) (a ++ ByteArray.empty.push (x % 128 + 128).toUInt8) c
      fuel (by omega)
    have heq : a ++ ByteArray.empty.push (x % 128 + 128).toUInt8 ++ pushVarint .empty (x / 128) ++ c
        = a ++ pushVarint .empty x ++ c := by
      rw [hv, ← append_assoc]
    rw [heq] at hrest
    simp only [ByteArray.size_append, ByteArray.size_push, ByteArray.size_empty] at hrest
    simp only [readVarint]
    rw [hb, hn]
    simp only [show ¬ x % 128 + 128 < 128 by omega, ite_false]
    rw [show a.size + 1 = a.size + (0 + 1) by omega, hrest]
    simp only [Prod.mk.injEq]
    constructor <;> omega

theorem size_writeBE :
    ∀ (n raw off : Nat) (b : ByteArray), (writeBE b off n raw).size = b.size
  | 0, _, _, _ => rfl
  | n + 1, raw, off, b => by rw [writeBE, size_writeBE n raw, ByteArray.size_set!]

theorem get!_writeBE_lt : ∀ (n raw off : Nat) (b : ByteArray) (j : Nat), j < off →
    (writeBE b off n raw).get! j = b.get! j
  | 0, _, _, _, _, _ => rfl
  | n + 1, raw, off, b, j, hj => by
    rw [writeBE, get!_writeBE_lt n raw (off + 1) _ j (by omega), get!_set!_ne _ _ _ _ (by omega)]

theorem get!_writeBE : ∀ (n raw off : Nat) (b : ByteArray) (i : Nat), i < n →
    off + n ≤ b.size →
      (writeBE b off n raw).get! (off + i) = (raw / 256 ^ (n - 1 - i) % 256).toUInt8
  | 0, _, _, _, _, hi, _ => absurd hi (by omega)
  | n + 1, raw, off, b, i, hi, hb => by
    rw [writeBE]
    cases i with
    | zero =>
      rw [get!_writeBE_lt n raw (off + 1) _ (off + 0) (by omega), Nat.add_zero,
        get!_set!_self _ _ _ (by omega)]
      simp
    | succ i =>
      have := get!_writeBE n raw (off + 1) (b.set! off (raw / 256 ^ n % 256).toUInt8) i (by omega)
        (by rw [ByteArray.size_set!]; omega)
      rw [show off + (i + 1) = off + 1 + i by omega, this,
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

/-! ## Facts: decoding a trace, and planting

`decode_drawStep` (`Basalt/Fuzz/Basic.lean`, beside `drawStep`) shows that decoding agrees with the
run. A run's trace is the encoding of the entries of the draws it has made (`encode`), and its
cursor the sum of their widths (`offsetAfter`). Each further draw (`drawStep`, one `choose`) appends
exactly that draw to what the trace decodes to: its range, its offset (the cursor before it), and
the value `choose` returns. By induction along a run, the trace decodes to every draw of more than
one outcome the run made; the whole-run statement is a free theorem of the generator's polymorphism,
which `BasaltTest/Fuzz.lean` pins.

`plant_value` and `plant_prefix` show that a plant does what it is for: the draw then decodes to the
planted value, and no byte before it changes, so neither does any earlier draw. `plant_size` bounds
the result, so that the C bridge may copy it into libFuzzer's buffer. -/

/-- A trace holding the entries `es`, each a draw's `lo` and `hi - lo`, appended to `b`. -/
@[expose] def encode (b : ByteArray) : List (Nat × Nat) → ByteArray
  | [] => b
  | (lo, span) :: es => encode (pushVarint (pushVarint b lo) span) es

/-- The bytes the draws of entries `es` read: where the next draw's bytes start. -/
@[expose] def offsetAfter : List (Nat × Nat) → Nat
  | [] => 0
  | (_, span) :: es => bytesFor (span + 1) + offsetAfter es

/-- The draws the entries `es` describe, against input `buf`, the first at offset `off`. -/
@[expose] def specFrom (buf : ByteArray) : List (Nat × Nat) → Nat → List Draw
  | [], _ => []
  | (lo, span) :: es, off =>
    ⟨lo, lo + span, off, drawValue buf lo (lo + span) off⟩ ::
      specFrom buf es (off + bytesFor (span + 1))

private theorem encode_append (es : List (Nat × Nat)) :
    ∀ (a b : ByteArray), encode (a ++ b) es = a ++ encode b es := by
  induction es with
  | nil => intro a b; rfl
  | cons e es ih =>
    intro a b
    obtain ⟨lo, span⟩ := e
    simp only [encode]
    rw [pushVarint_append, pushVarint_append, ih]

private theorem encode_empty (a : ByteArray) (es : List (Nat × Nat)) :
    encode a es = a ++ encode .empty es := by
  rw [← encode_append, ByteArray.append_empty]

theorem encode_snoc (b : ByteArray) (es : List (Nat × Nat)) (lo span : Nat) :
    encode b (es ++ [(lo, span)]) = pushVarint (pushVarint (encode b es) lo) span := by
  induction es generalizing b with
  | nil => rfl
  | cons e es ih => obtain ⟨_, _⟩ := e; simp only [List.cons_append, encode]; exact ih _

private theorem length_le_size (es : List (Nat × Nat)) : es.length ≤ (encode .empty es).size := by
  induction es with
  | nil => simp
  | cons e es ih =>
    obtain ⟨lo, span⟩ := e
    simp only [encode, List.length_cons]
    rw [encode_empty, pushVarint_empty, ByteArray.size_append, ByteArray.size_append]
    have := size_pushVarint_pos span
    omega

/-- Decoding the entries after a prefix `pre` of the trace gives the draws they describe. -/
private theorem decodeFrom_encode (buf : ByteArray) (es : List (Nat × Nat)) :
    ∀ (pre : ByteArray) (off fuel : Nat), es.length ≤ fuel →
      decodeFrom (pre ++ encode .empty es) buf fuel pre.size off = specFrom buf es off := by
  induction es with
  | nil =>
    intro pre off fuel _
    cases fuel with
    | zero => rfl
    | succ fuel => simp [decodeFrom, encode, ByteArray.append_empty, specFrom]
  | cons e es ih =>
    intro pre off fuel hf
    obtain ⟨lo, span⟩ := e
    obtain _ | fuel := fuel
    · simp at hf
    have hrec : pre ++ encode .empty ((lo, span) :: es) =
        pre ++ pushVarint .empty lo ++ (pushVarint .empty span ++ encode .empty es) := by
      simp only [encode]
      rw [encode_empty, pushVarint_empty (pushVarint .empty lo)]
      simp only [append_assoc]
    have hsz := congrArg ByteArray.size hrec
    simp only [ByteArray.size_append] at hsz
    have hlo := size_pushVarint_pos lo
    have hspan := size_pushVarint_pos span
    have r1 := readVarint_pushVarint lo pre (pushVarint .empty span ++ encode .empty es)
      (pre ++ encode .empty ((lo, span) :: es)).size (by rw [ByteArray.size_append]; omega)
    have hrec2 : pre ++ encode .empty ((lo, span) :: es) =
        (pre ++ pushVarint .empty lo) ++ pushVarint .empty span ++ encode .empty es := by
      rw [hrec]; simp only [append_assoc]
    have r2 := readVarint_pushVarint span (pre ++ pushVarint .empty lo) (encode .empty es)
      (pre ++ encode .empty ((lo, span) :: es)).size (by rw [ByteArray.size_append]; omega)
    rw [← hrec2] at r2
    rw [← hrec] at r1
    have hnext := ih (pre ++ pushVarint .empty lo ++ pushVarint .empty span)
      (off + bytesFor (span + 1)) fuel (by simp at hf; omega)
    rw [← hrec2] at hnext
    have hlt : pre.size < (pre ++ encode .empty ((lo, span) :: es)).size := by
      rw [ByteArray.size_append]; omega
    rw [decodeFrom]
    simp only [hlt, ↓reduceIte]
    rw [r1]
    dsimp only
    have hpos : (pre ++ pushVarint .empty lo).size = pre.size + (pushVarint .empty lo).size :=
      ByteArray.size_append
    rw [hpos] at r2
    rw [r2]
    dsimp only
    simp only [specFrom, List.cons.injEq, true_and]
    simp only [ByteArray.size_append] at hnext
    exact hnext

/-- **Decoding a trace.** A trace of the entries `es` decodes to the draws they describe. -/
theorem decode_encode (es : List (Nat × Nat)) (buf : ByteArray) :
    decode (encode .empty es) buf = specFrom buf es 0 := by
  have := decodeFrom_encode buf es .empty 0 (encode .empty es).size (length_le_size es)
  simpa [decode, ByteArray.empty_append] using this

theorem specFrom_snoc (buf : ByteArray) (es : List (Nat × Nat)) (lo span : Nat) :
    ∀ off, specFrom buf (es ++ [(lo, span)]) off =
      specFrom buf es off ++ [⟨lo, lo + span, off + offsetAfter es,
        drawValue buf lo (lo + span) (off + offsetAfter es)⟩] := by
  induction es with
  | nil => intro off; simp [specFrom, offsetAfter]
  | cons e es ih =>
    intro off
    obtain ⟨_, s⟩ := e
    simp only [List.cons_append, specFrom, offsetAfter, ih, List.cons_append]
    rw [show off + bytesFor (s + 1) + offsetAfter es = off + (bytesFor (s + 1) + offsetAfter es) by
      omega]

/-- The C bridge's `decodeWords` is `decode`, packed. -/
theorem decodeWords_eq (trace buf : ByteArray) :
    decodeWords trace buf =
      (decode trace buf).foldl packDraw (ByteArray.emptyWithCapacity 256) := by
  suffices ∀ fuel i off acc, decodeWordsFrom trace buf fuel i off acc =
      (decodeFrom trace buf fuel i off).foldl packDraw acc from this _ _ _ _
  intro fuel
  induction fuel with
  | zero => intro i off acc; rfl
  | succ fuel ih =>
    intro i off acc
    simp only [decodeWordsFrom, decodeFrom]
    split
    · simp only [List.foldl_cons]; exact ih _ _ _
    · rfl

/-! ### Planting -/

private theorem size_zeros (n : Nat) : (zeros n).size = n := by simp [zeros, ByteArray.size]

private theorem get!_extended (buf : ByteArray) (m : Nat) (j : Nat) :
    (if buf.size < m then buf ++ zeros (m - buf.size) else buf).get! j = buf.get! j := by
  split
  · by_cases hj : j < buf.size
    · exact get!_append_lt _ _ _ hj
    · rw [get!_out buf j (by omega)]
      obtain ⟨k, rfl⟩ : ∃ k, j = buf.size + k := ⟨j - buf.size, by omega⟩
      rw [get!_append_right]
      by_cases hk : k < (zeros (m - buf.size)).size
      · rw [get!_eq _ _ hk]; simp [zeros]
      · exact get!_out _ _ (by omega)
  · rfl

/-- **A plant leaves the draw holding the value.** -/
theorem plant_value (buf : ByteArray) (lo hi offset v maxSize : Nat) (out : ByteArray)
    (hp : plant buf lo hi offset v maxSize = some out) : drawValue out lo hi offset = v := by
  unfold plant at hp
  dsimp only at hp
  split at hp
  · rename_i hc
    obtain ⟨hlo, hhi, _⟩ := hc
    cases hp
    have hpow := le_pow_bytesFor (hi - lo + 1)
    generalize hw : bytesFor (hi - lo + 1) = w at hpow ⊢
    generalize hbdef : (if buf.size < offset + w then buf ++ zeros (offset + w - buf.size) else buf)
      = b
    have hb : offset + w ≤ b.size := by
      rw [← hbdef]; split
      · rw [ByteArray.size_append, size_zeros]; omega
      · omega
    have hread := readBEFrom_digits (v - lo) (writeBE b offset w (v - lo)) w 0 offset
      (by rw [size_writeBE]; exact hb)
      (fun i hi' => get!_writeBE w (v - lo) offset b i hi' hb)
    simp only [drawValue, hw, hread, Nat.zero_mul, Nat.zero_add]
    have h1 : (v - lo) % 256 ^ w = v - lo := Nat.mod_eq_of_lt (by omega)
    have h2 : (v - lo) % (hi - lo + 1) = v - lo := Nat.mod_eq_of_lt (by omega)
    rw [h1, h2]
    omega
  · cases hp

/-- **A plant changes no byte before the draw**, so no earlier draw. -/
theorem plant_prefix (buf : ByteArray) (lo hi offset v maxSize : Nat) (out : ByteArray)
    (hp : plant buf lo hi offset v maxSize = some out) : ∀ j < offset, out.get! j = buf.get! j := by
  unfold plant at hp
  dsimp only at hp
  split at hp
  · cases hp
    intro j hj
    rw [get!_writeBE_lt _ _ _ _ j hj, get!_extended]
  · cases hp

/-- **A plant's size**: the input's, or the end of the draw's bytes if that is later, which is at
most `maxSize`. -/
theorem plant_size (buf : ByteArray) (lo hi offset v maxSize : Nat) (out : ByteArray)
    (hp : plant buf lo hi offset v maxSize = some out) :
    out.size = max buf.size (offset + bytesFor (hi - lo + 1)) ∧
      offset + bytesFor (hi - lo + 1) ≤ maxSize := by
  unfold plant at hp
  dsimp only at hp
  split at hp
  · rename_i hc
    cases hp
    rw [size_writeBE]
    refine ⟨?_, hc.2.2⟩
    split
    · rw [ByteArray.size_append, size_zeros]; omega
    · omega
  · cases hp

end Basalt.Fuzz
