/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt
import Batteries.Data.Char
import BasaltExamples.AniImage.Def

open RandomChoice

/-!
# ANI Images (standard definition)

`genBasicImage` generates the ANI images of `Image.WellFormed` that avoid all five of
`Image.HasEdgeCase`'s ambiguities. The image is assembled by `genImage` from one generator per
chunk, a factoring reused by the edge-case generators in `BasaltExamples/AniImage/Special`.
-/

namespace AniImage

theorem sum_map_const {α : Type} (c : Nat) (xs : List α) :
    (xs.map fun _ => c).sum = c * xs.length := by
  simp [Nat.mul_comm]

/-! ## Alphabet facts -/

theorem mem_asciiChars_iff {lo hi : Nat} (h : hi < 0xD800) {c : Char} :
    c ∈ asciiChars lo hi ↔ lo ≤ c.toNat ∧ c.toNat ≤ hi := by
  simp only [asciiChars, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi', rfl⟩
    rw [Char.toNat_ofNat, if_pos (Or.inl (by omega))]
    omega
  · rintro ⟨hlo, hhi⟩
    exact ⟨c.toNat - lo, by omega, by rw [show lo + (c.toNat - lo) = c.toNat by omega,
      Char.ofNat_toNat]⟩

theorem mem_printableChars_iff {c : Char} :
    c ∈ printableChars ↔ 0x20 ≤ c.toNat ∧ c.toNat ≤ 0x7E :=
  mem_asciiChars_iff (by norm_num)

theorem mem_nonPrintableChars_iff {c : Char} :
    c ∈ nonPrintableChars ↔ c.toNat ≤ 0x1F ∨ c.toNat = 0x7F := by
  rw [nonPrintableChars, List.mem_append, mem_asciiChars_iff (by norm_num),
    mem_asciiChars_iff (by norm_num)]
  omega

theorem mem_aniChars_iff {c : Char} : c ∈ aniChars ↔ c.toNat ≤ 0x7F := by
  rw [aniChars, List.mem_append, mem_printableChars_iff, mem_nonPrintableChars_iff]
  omega

theorem printableChars_ne_nil : printableChars ≠ [] :=
  List.ne_nil_of_mem (a := ' ') (mem_printableChars_iff.mpr (by decide))

theorem nonPrintableChars_ne_nil : nonPrintableChars ≠ [] :=
  List.ne_nil_of_mem (a := '\x00') (mem_nonPrintableChars_iff.mpr (by decide))

theorem aniChars_ne_nil : aniChars ≠ [] :=
  List.ne_nil_of_mem (a := ' ') (mem_aniChars_iff.mpr (by decide))

/-- A printable character is exactly one of the alphabet that is not non-printable. -/
theorem mem_printableChars_iff_mem_aniChars {c : Char} :
    c ∈ printableChars ↔ c ∈ aniChars ∧ c ∉ nonPrintableChars := by
  rw [mem_printableChars_iff, mem_aniChars_iff, mem_nonPrintableChars_iff]
  omega

/-! ## Chunk generators -/

/-- The field lengths the standard definition allows: a field whose subsection would declare a
size of two bytes is the `Image.InfoSizeTwo` edge case. -/
def standardLengths (overhead n : Nat) : List Nat :=
  (List.range (n + 1)).filter fun k => k + overhead != 2

theorem mem_standardLengths_iff {overhead n k : Nat} :
    k ∈ standardLengths overhead n ↔ k ≤ n ∧ k + overhead ≠ 2 := by
  simp [standardLengths, List.mem_filter]

/-- An overhead of two bytes makes the empty field the size-two one, so only then does a standard
field need room for a character. -/
theorem standardLengths_ne_nil {overhead n : Nat} (h : overhead ≠ 2 ∨ 0 < n) :
    standardLengths overhead n ≠ [] := by
  by_cases h2 : overhead = 2
  · exact List.ne_nil_of_mem (a := 1)
      (mem_standardLengths_iff.mpr ⟨Or.resolve_left h (not_not_intro h2), by omega⟩)
  · exact List.ne_nil_of_mem (a := 0) (mem_standardLengths_iff.mpr ⟨Nat.zero_le _, by omega⟩)

/-- Generates a printable character. -/
def genPrintableChar [Gen G] : G Char := elements printableChars printableChars_ne_nil

theorem genPrintableChar_mem_support {c : Char} :
    c ∈ SPMF.support (genPrintableChar : SPMF Char) ↔ c ∈ printableChars := by
  rw [genPrintableChar, SPMF.mem_support_elements_iff]

/-- Generates a printable text field of a standard length at most `n`. -/
def genStandardText [Gen G] (overhead n : Nat) (h : overhead ≠ 2 ∨ 0 < n) : G (List Char) := do
  let k ← elements (standardLengths overhead n) (standardLengths_ne_nil h)
  vectorOf k genPrintableChar

/-- Generates a `rate` subsection that does not reuse the `LIST` chunk id. -/
def genStandardRate [Gen G] (b : Bounds) : G RateEntry := do
  let jifs ← chooseNat 0 b.maxJifRate
  return ⟨"rate", jifs⟩

/-- Generates a `rate` list within bounds, none of it named `LIST`. -/
def genStandardRates [Gen G] (b : Bounds) : G (List RateEntry) :=
  listOfMaxLength b.maxCSteps (genStandardRate b)

/-- Generates between `lo` and `hi` icon frames. -/
def genIcons [Gen G] (lo hi : Nat) (h : lo ≤ hi) : G (List Icon) := do
  let n ← chooseNat lo hi h
  vectorOf n (pure Icon.icon)

/-- Generates the `seq ` chunk of an image with `steps` animation steps and `frames` icons: one
frame index per step. A `frames` of zero leaves no index to draw, and the truncated upper bound
`frames - 1` then makes the generator produce the invalid index `0`; every caller pairs it with a
`steps` of zero there, which draws nothing. -/
def genSeq [Gen G] (steps frames : Nat) : G (List Nat) :=
  vectorOf steps (chooseNat 0 (frames - 1) (Nat.zero_le _))

/-! ## Chunk supports -/

theorem genStandardText_mem_support {overhead n : Nat} {h : overhead ≠ 2 ∨ 0 < n}
    {t : List Char} :
    t ∈ SPMF.support (genStandardText overhead n h : SPMF (List Char)) ↔
      t.length ≤ n ∧ t.length + overhead ≠ 2 ∧ ∀ c ∈ t, c ∈ printableChars := by
  rw [genStandardText]
  support_simp [mem_standardLengths_iff, genPrintableChar_mem_support]
  constructor
  · rintro ⟨k, ⟨hk, hk1⟩, hlen, hc⟩
    exact ⟨by omega, by omega, hc⟩
  · rintro ⟨hle, hne, hc⟩
    exact ⟨t.length, ⟨hle, hne⟩, rfl, hc⟩

theorem genStandardRate_mem_support {b : Bounds} {r : RateEntry} :
    r ∈ SPMF.support (genStandardRate b : SPMF RateEntry) ↔
      r.WellFormed b ∧ r.name ≠ "LIST" := by
  obtain ⟨name, jifs⟩ := r
  rw [genStandardRate]
  support_simp [RateEntry.WellFormed, RateEntry.mk.injEq, rateNames]
  constructor
  · rintro ⟨j, ⟨-, hj⟩, rfl, rfl⟩
    exact ⟨⟨by simp, hj⟩, by simp⟩
  · rintro ⟨⟨hn, hj⟩, hlist⟩
    exact ⟨jifs, ⟨Nat.zero_le _, hj⟩, by simp_all, rfl⟩

theorem genStandardRates_mem_support {b : Bounds} {rs : List RateEntry} :
    rs ∈ SPMF.support (genStandardRates b : SPMF (List RateEntry)) ↔
      rs.length ≤ b.maxCSteps ∧ ∀ r ∈ rs, r.WellFormed b ∧ r.name ≠ "LIST" := by
  rw [genStandardRates]
  support_simp [genStandardRate_mem_support]

theorem genSeq_mem_support {steps frames : Nat} {sq : List Nat} :
    sq ∈ SPMF.support (genSeq steps frames : SPMF (List Nat)) ↔
      sq.length = steps ∧ ∀ i ∈ sq, i ≤ frames - 1 := by
  rw [genSeq]
  support_simp
  grind

theorem genIcons_mem_support {lo hi : Nat} {h : lo ≤ hi} {ic : List Icon} :
    ic ∈ SPMF.support (genIcons lo hi h : SPMF (List Icon)) ↔
      lo ≤ ic.length ∧ ic.length ≤ hi := by
  rw [genIcons]
  support_simp
  constructor
  · rintro ⟨n, ⟨hlo, hhi⟩, hlen, -⟩
    exact ⟨by omega, by omega⟩
  · rintro ⟨hlo, hhi⟩
    exact ⟨ic.length, ⟨hlo, hhi⟩, rfl, fun x _ => by cases x; trivial⟩

/-! ## Chunk termination and cost -/

theorem genPrintableChar.terminates : IsAlmostSurelyTerminating (genPrintableChar : SPMF Char) := by
  mass_fixpoint using SPMF.LfpIsOne.one
  simp

theorem genPrintableChar.cost_bounded : IsCostBounded genPrintableChar (fun _ => 1) := by
  cost_fixpoint
  omega

theorem genStandardText.terminates {overhead n : Nat} {h : overhead ≠ 2 ∨ 0 < n} :
    IsAlmostSurelyTerminating (genStandardText overhead n h : SPMF (List Char)) := by
  mass_fixpoint using SPMF.LfpIsOne.one
  simp

theorem genStandardText.cost_bounded {overhead n : Nat} {h : overhead ≠ 2 ∨ 0 < n} :
    IsCostBounded (genStandardText overhead n h) (fun t => 1 + t.length) := by
  cost_fixpoint
  all_goals simp only [sum_map_const] at *; omega

theorem genStandardRate.terminates {b : Bounds} :
    IsAlmostSurelyTerminating (genStandardRate b : SPMF RateEntry) := by
  mass_fixpoint using SPMF.LfpIsOne.one
  simp

theorem genStandardRate.cost_bounded {b : Bounds} :
    IsCostBounded (genStandardRate b) (fun _ => 1) := by
  cost_fixpoint
  omega

theorem genStandardRates.terminates {b : Bounds} :
    IsAlmostSurelyTerminating (genStandardRates b : SPMF (List RateEntry)) := by
  mass_fixpoint using SPMF.LfpIsOne.one
  simp

theorem genStandardRates.cost_bounded {b : Bounds} :
    IsCostBounded (genStandardRates b) (fun rs => 1 + rs.length) := by
  cost_fixpoint
  all_goals simp only [sum_map_const] at *; omega

theorem genIcons.terminates {lo hi : Nat} {h : lo ≤ hi} :
    IsAlmostSurelyTerminating (genIcons lo hi h : SPMF (List Icon)) := by
  mass_fixpoint using SPMF.LfpIsOne.one
  simp only [one_pow, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, mul_one,
    show hi + 1 - lo = hi - lo + 1 by omega]
  exact (ENNReal.div_self (by simp) (ENNReal.natCast_ne_top _)).ge

theorem genIcons.cost_bounded {lo hi : Nat} {h : lo ≤ hi} :
    IsCostBounded (genIcons lo hi h) (fun _ => 1) := by
  cost_fixpoint
  all_goals simp only [sum_map_const] at *; omega

/-! ## Assembling an image -/

/-- Assembles an image from one generator per chunk, deriving the header's counts from the chunks
they describe. The `seq ` chunk is drawn from a generator indexed by the two counts it has to agree
with, so it is the one chunk that cannot be chosen independently of the others. -/
def genImage [Gen G] (grates : G (List RateEntry)) (gicons : G (List Icon))
    (gseq : Nat → Nat → G (List Nat)) (gtitle gauthor : G (List Char)) (gjif : G Nat) :
    G Image := do
  let rates ← grates
  let icons ← gicons
  let sq ← gseq rates.length icons.length
  let title ← gtitle
  let author ← gauthor
  let jifRate ← gjif
  return { header := { cSteps := rates.length, nFrames := icons.length, jifRate := jifRate },
           info := { title := title, author := author },
           rates := rates, seq := sq, icons := icons }

theorem genImage_mem_support {grates : SPMF (List RateEntry)} {gicons : SPMF (List Icon)}
    {gseq : Nat → Nat → SPMF (List Nat)} {gtitle gauthor : SPMF (List Char)} {gjif : SPMF Nat}
    {img : Image} :
    img ∈ SPMF.support (genImage grates gicons gseq gtitle gauthor gjif) ↔
      img.header.nFrames = img.icons.length ∧
      img.header.cSteps = img.rates.length ∧
      img.rates ∈ SPMF.support grates ∧
      img.icons ∈ SPMF.support gicons ∧
      img.seq ∈ SPMF.support (gseq img.rates.length img.icons.length) ∧
      img.info.title ∈ SPMF.support gtitle ∧
      img.info.author ∈ SPMF.support gauthor ∧
      img.header.jifRate ∈ SPMF.support gjif := by
  obtain ⟨⟨cSteps, nFrames, jifRate⟩, ⟨title, author⟩, rates, sq, icons⟩ := img
  rw [genImage]
  support_simp [Image.mk.injEq, Header.mk.injEq, InfoList.mk.injEq]
  constructor
  · rintro ⟨rs, hrs, ic, hic, q, hq, t, ht, a, ha, j, hj,
      ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl⟩, rfl, rfl, rfl⟩
    exact ⟨rfl, rfl, hrs, hic, hq, ht, ha, hj⟩
  · rintro ⟨rfl, rfl, hrs, hic, hq, ht, ha, hj⟩
    exact ⟨rates, hrs, icons, hic, sq, hq, title, ht, author, ha, jifRate, hj,
      ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl⟩, rfl, rfl, rfl⟩

theorem genSeq.terminates {steps frames : Nat} :
    IsAlmostSurelyTerminating (genSeq steps frames : SPMF (List Nat)) := by
  mass_fixpoint using SPMF.LfpIsOne.one
  simp

theorem genSeq.cost_bounded {steps frames : Nat} :
    IsCostBounded (genSeq steps frames) (fun sq => sq.length) := by
  cost_fixpoint
  all_goals simp only [sum_map_const] at *; omega

/-! ## The standard generator -/

/-- Generates an ANI image within `b` that avoids every edge case. The bounds must admit one: an
image with no icons and an image with a zero frame duration are themselves edge cases, and under a
two-byte `infoSize` overhead so is an empty text field. -/
def genBasicImage [Gen G] (overhead : Nat) (b : Bounds) (hicons : 0 < b.maxIcons)
    (hjif : 0 < b.maxJifRate) (htitle : overhead ≠ 2 ∨ 0 < b.maxTitle)
    (hauthor : overhead ≠ 2 ∨ 0 < b.maxAuthor) : G Image :=
  genImage (genStandardRates b) (genIcons 1 b.maxIcons hicons) genSeq
    (genStandardText overhead b.maxTitle htitle) (genStandardText overhead b.maxAuthor hauthor)
    (chooseNat 1 b.maxJifRate hjif)

theorem genBasicImage_mem_support {overhead : Nat} {b : Bounds} {hicons : 0 < b.maxIcons}
    {hjif : 0 < b.maxJifRate} {htitle : overhead ≠ 2 ∨ 0 < b.maxTitle}
    {hauthor : overhead ≠ 2 ∨ 0 < b.maxAuthor} {img : Image} :
    img ∈ SPMF.support (genBasicImage overhead b hicons hjif htitle hauthor) ↔
      img.WellFormed b ∧ ¬ img.HasEdgeCase overhead := by
  rw [genBasicImage, genImage_mem_support]
  simp only [genStandardRates_mem_support, genIcons_mem_support, genSeq_mem_support,
    genStandardText_mem_support, SPMF.mem_support_chooseNat_iff, Image.WellFormed,
    Image.HasEdgeCase, Image.RateNamedList, Image.InfoSizeTwo, Image.NonPrintableText,
    Image.NoIcons, Image.ZeroJifRate, infoSize, mem_printableChars_iff_mem_aniChars]
  push Not
  grind

theorem genBasicImage.sound_complete (overhead : Nat) (b : Bounds) (hicons : 0 < b.maxIcons)
    (hjif : 0 < b.maxJifRate) (htitle : overhead ≠ 2 ∨ 0 < b.maxTitle)
    (hauthor : overhead ≠ 2 ∨ 0 < b.maxAuthor) :
    IsSoundAndComplete (genBasicImage overhead b hicons hjif htitle hauthor)
      (fun img => img.WellFormed b ∧ ¬ img.HasEdgeCase overhead) :=
  fun _ => genBasicImage_mem_support

theorem genBasicImage.terminates (overhead : Nat) (b : Bounds) (hicons : 0 < b.maxIcons)
    (hjif : 0 < b.maxJifRate) (htitle : overhead ≠ 2 ∨ 0 < b.maxTitle)
    (hauthor : overhead ≠ 2 ∨ 0 < b.maxAuthor) :
    IsAlmostSurelyTerminating (genBasicImage overhead b hicons hjif htitle hauthor) := by
  unfold genBasicImage genImage
  exact SPMF.IsPMF.of_one_le (by mass_bound; simp)

theorem genBasicImage.cost_bounded (overhead : Nat) (b : Bounds) (hicons : 0 < b.maxIcons)
    (hjif : 0 < b.maxJifRate) (htitle : overhead ≠ 2 ∨ 0 < b.maxTitle)
    (hauthor : overhead ≠ 2 ∨ 0 < b.maxAuthor) :
    IsCostBounded (genBasicImage overhead b hicons hjif htitle hauthor)
      (fun img => 5 + img.rates.length + img.seq.length + img.info.title.length +
        img.info.author.length) := by
  unfold genBasicImage genImage
  cost_bound
  omega

end AniImage
