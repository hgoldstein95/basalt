/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import BasaltExamples.AniImage.Basic

open RandomChoice

/-!
# ANI Images (edge cases)

`genSpecialImage` generates the ANI images of `Image.WellFormed` that contain at least one of
`Image.HasEdgeCase`'s five ambiguities. It is a `oneOf` over one generator per `Image.EdgeClass` —
the *first* ambiguity an image exhibits, with the two that can arise in either text field split by
field — so the branches have pairwise disjoint supports and every special image is drawn by
exactly one of them.
-/

namespace AniImage

/-! ## The classes of the special space -/

/-- The seven conditions the special space splits on: the five ambiguities of
`Image.HasEdgeCase`, with the two that can arise in either text field split by field. -/
def Image.EdgeCase (overhead : Nat) : Nat → Image → Prop
  | 0, img => img.NoIcons
  | 1, img => img.ZeroJifRate
  | 2, img => img.RateNamedList
  | 3, img => ∃ c ∈ img.info.title, c ∈ nonPrintableChars
  | 4, img => ∃ c ∈ img.info.author, c ∈ nonPrintableChars
  | 5, img => infoSize overhead img.info.title = 2
  | 6, img => infoSize overhead img.info.author = 2
  | _ + 7, _ => False

/-- The class a special image belongs to: the first of `Image.EdgeCase`'s conditions it meets.
`genSpecialImage` runs one generator per class, and a class carries the denial of every earlier
condition, so no image is drawn by two of them. -/
def Image.EdgeClass (overhead i : Nat) (img : Image) : Prop :=
  img.EdgeCase overhead i ∧ ∀ j < i, ¬ img.EdgeCase overhead j

theorem Image.edgeClass_unique {overhead i j : Nat} {img : Image}
    (hi : img.EdgeClass overhead i) (hj : img.EdgeClass overhead j) : i = j := by
  rcases Nat.lt_trichotomy i j with h | h | h
  · exact absurd hi.1 (hj.2 i h)
  · exact h
  · exact absurd hj.1 (hi.2 j h)

theorem Image.edgeClass_zero_iff {overhead : Nat} {img : Image} :
    img.EdgeClass overhead 0 ↔ img.NoIcons := by
  simp [Image.EdgeClass, Image.EdgeCase]

theorem Image.edgeClass_one_iff {overhead : Nat} {img : Image} :
    img.EdgeClass overhead 1 ↔
      ¬img.NoIcons ∧
      img.ZeroJifRate := by
  simp only [Image.EdgeClass, Image.EdgeCase]
  constructor
  · rintro ⟨h, hlt⟩
    exact ⟨hlt 0 (by omega), h⟩
  · rintro ⟨h0, h⟩
    refine ⟨h, fun j hj => ?_⟩
    rcases j with _ | _ | _ | _ | _ | _ | j <;>
      first
        | exact absurd hj (by omega)
        | assumption

theorem Image.edgeClass_two_iff {overhead : Nat} {img : Image} :
    img.EdgeClass overhead 2 ↔
      ¬img.NoIcons ∧
      ¬img.ZeroJifRate ∧
      img.RateNamedList := by
  simp only [Image.EdgeClass, Image.EdgeCase]
  constructor
  · rintro ⟨h, hlt⟩
    exact ⟨hlt 0 (by omega), hlt 1 (by omega), h⟩
  · rintro ⟨h0, h1, h⟩
    refine ⟨h, fun j hj => ?_⟩
    rcases j with _ | _ | _ | _ | _ | _ | j <;>
      first
        | exact absurd hj (by omega)
        | assumption

theorem Image.edgeClass_three_iff {overhead : Nat} {img : Image} :
    img.EdgeClass overhead 3 ↔
      ¬img.NoIcons ∧
      ¬img.ZeroJifRate ∧
      ¬img.RateNamedList ∧
      (∃ c ∈ img.info.title, c ∈ nonPrintableChars) := by
  simp only [Image.EdgeClass, Image.EdgeCase]
  constructor
  · rintro ⟨h, hlt⟩
    exact ⟨hlt 0 (by omega), hlt 1 (by omega), hlt 2 (by omega), h⟩
  · rintro ⟨h0, h1, h2, h⟩
    refine ⟨h, fun j hj => ?_⟩
    rcases j with _ | _ | _ | _ | _ | _ | j <;>
      first
        | exact absurd hj (by omega)
        | assumption

theorem Image.edgeClass_four_iff {overhead : Nat} {img : Image} :
    img.EdgeClass overhead 4 ↔
      ¬img.NoIcons ∧
      ¬img.ZeroJifRate ∧
      ¬img.RateNamedList ∧
      ¬(∃ c ∈ img.info.title, c ∈ nonPrintableChars) ∧
      (∃ c ∈ img.info.author, c ∈ nonPrintableChars) := by
  simp only [Image.EdgeClass, Image.EdgeCase]
  constructor
  · rintro ⟨h, hlt⟩
    exact ⟨hlt 0 (by omega), hlt 1 (by omega), hlt 2 (by omega), hlt 3 (by omega), h⟩
  · rintro ⟨h0, h1, h2, h3, h⟩
    refine ⟨h, fun j hj => ?_⟩
    rcases j with _ | _ | _ | _ | _ | _ | j <;>
      first
        | exact absurd hj (by omega)
        | assumption

theorem Image.edgeClass_five_iff {overhead : Nat} {img : Image} :
    img.EdgeClass overhead 5 ↔
      ¬img.NoIcons ∧
      ¬img.ZeroJifRate ∧
      ¬img.RateNamedList ∧
      ¬(∃ c ∈ img.info.title, c ∈ nonPrintableChars) ∧
      ¬(∃ c ∈ img.info.author, c ∈ nonPrintableChars) ∧
      infoSize overhead img.info.title = 2 := by
  simp only [Image.EdgeClass, Image.EdgeCase]
  constructor
  · rintro ⟨h, hlt⟩
    exact ⟨hlt 0 (by omega), hlt 1 (by omega), hlt 2 (by omega), hlt 3 (by omega),
      hlt 4 (by omega), h⟩
  · rintro ⟨h0, h1, h2, h3, h4, h⟩
    refine ⟨h, fun j hj => ?_⟩
    rcases j with _ | _ | _ | _ | _ | _ | j <;>
      first
        | exact absurd hj (by omega)
        | assumption

theorem Image.edgeClass_six_iff {overhead : Nat} {img : Image} :
    img.EdgeClass overhead 6 ↔
      ¬img.NoIcons ∧
      ¬img.ZeroJifRate ∧
      ¬img.RateNamedList ∧
      ¬(∃ c ∈ img.info.title, c ∈ nonPrintableChars) ∧
      ¬(∃ c ∈ img.info.author, c ∈ nonPrintableChars) ∧
      infoSize overhead img.info.title ≠ 2 ∧
      infoSize overhead img.info.author = 2 := by
  simp only [Image.EdgeClass, Image.EdgeCase]
  constructor
  · rintro ⟨h, hlt⟩
    exact ⟨hlt 0 (by omega), hlt 1 (by omega), hlt 2 (by omega), hlt 3 (by omega),
      hlt 4 (by omega), hlt 5 (by omega), h⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h⟩
    refine ⟨h, fun j hj => ?_⟩
    rcases j with _ | _ | _ | _ | _ | _ | j <;>
      first
        | exact absurd hj (by omega)
        | assumption

theorem Image.hasEdgeCase_iff_exists_edgeClass {overhead : Nat} {img : Image} :
    img.HasEdgeCase overhead ↔ ∃ i, img.EdgeClass overhead i := by
  constructor
  · intro h
    have hex : ∃ i, img.EdgeCase overhead i := by
      simp only [Image.HasEdgeCase, Image.InfoSizeTwo, Image.NonPrintableText] at h
      rcases h with h | (h | h) | (h | h) | h | h
      exacts [⟨2, h⟩, ⟨5, h⟩, ⟨6, h⟩, ⟨3, h⟩, ⟨4, h⟩, ⟨0, h⟩, ⟨1, h⟩]
    classical
    exact ⟨Nat.find hex, Nat.find_spec hex, fun j hj => Nat.find_min hex hj⟩
  · rintro ⟨i, hi, -⟩
    simp only [Image.HasEdgeCase, Image.InfoSizeTwo, Image.NonPrintableText]
    match i, hi with
    | 0, h => exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    | 1, h => exact Or.inr (Or.inr (Or.inr (Or.inr h)))
    | 2, h => exact Or.inl h
    | 3, h => exact Or.inr (Or.inr (Or.inl (Or.inl h)))
    | 4, h => exact Or.inr (Or.inr (Or.inl (Or.inr h)))
    | 5, h => exact Or.inr (Or.inl (Or.inl h))
    | 6, h => exact Or.inr (Or.inl (Or.inr h))
    | _ + 7, h => exact h.elim

/-! ## Unconstrained chunks -/

/-- Generates a character of the ANI text alphabet. -/
def genAniChar [Gen G] : G Char := elements aniChars aniChars_ne_nil

/-- Generates a text field of length at most `n` over the full ANI alphabet. -/
def genAnyText [Gen G] (n : Nat) : G (List Char) := listOfMaxLength n genAniChar

/-- Generates a `rate` subsection with either admissible chunk id. -/
def genAnyRate [Gen G] (b : Bounds) : G RateEntry := do
  let name ← elements rateNames (by decide)
  let jifs ← chooseNat 0 b.maxJifRate
  return ⟨name, jifs⟩

/-- Generates a `rate` list within bounds, with either admissible chunk id. -/
def genAnyRates [Gen G] (b : Bounds) : G (List RateEntry) :=
  listOfMaxLength b.maxCSteps (genAnyRate b)

/-- Generates any frame duration within bounds. -/
def genAnyJifRate [Gen G] (b : Bounds) : G Nat := chooseNat 0 b.maxJifRate (Nat.zero_le _)

theorem genAniChar_mem_support {c : Char} :
    c ∈ SPMF.support (genAniChar : SPMF Char) ↔ c ∈ aniChars := by
  rw [genAniChar, SPMF.mem_support_elements_iff]

theorem genAnyText_mem_support {n : Nat} {t : List Char} :
    t ∈ SPMF.support (genAnyText n : SPMF (List Char)) ↔
      t.length ≤ n ∧ ∀ c ∈ t, c ∈ aniChars := by
  rw [genAnyText]
  support_simp [genAniChar_mem_support]

theorem genAnyRate_mem_support {b : Bounds} {r : RateEntry} :
    r ∈ SPMF.support (genAnyRate b : SPMF RateEntry) ↔ r.WellFormed b := by
  obtain ⟨name, jifs⟩ := r
  rw [genAnyRate]
  support_simp [RateEntry.WellFormed, RateEntry.mk.injEq]
  constructor
  · rintro ⟨n, hn, j, ⟨-, hj⟩, rfl, rfl⟩
    exact ⟨hn, hj⟩
  · rintro ⟨hn, hj⟩
    exact ⟨name, hn, jifs, ⟨Nat.zero_le _, hj⟩, rfl, rfl⟩

theorem genAnyRates_mem_support {b : Bounds} {rs : List RateEntry} :
    rs ∈ SPMF.support (genAnyRates b : SPMF (List RateEntry)) ↔
      rs.length ≤ b.maxCSteps ∧ ∀ r ∈ rs, r.WellFormed b := by
  rw [genAnyRates]
  support_simp [genAnyRate_mem_support]

theorem genAnyJifRate_mem_support {b : Bounds} {n : Nat} :
    n ∈ SPMF.support (genAnyJifRate b : SPMF Nat) ↔ n ≤ b.maxJifRate := by
  rw [genAnyJifRate]
  simp

/-! ## Printable chunks -/

/-- Generates a printable text field of length at most `n`, of any size. -/
def genPrintableText [Gen G] (n : Nat) : G (List Char) := listOfMaxLength n genPrintableChar

/-- Generates the printable text field whose subsection declares a size of two bytes: the length
that, with `infoSize`'s overhead, adds up to two. -/
def genSizeTwoText [Gen G] (overhead : Nat) : G (List Char) :=
  vectorOf (2 - overhead) genPrintableChar

theorem genPrintableText_mem_support {n : Nat} {t : List Char} :
    t ∈ SPMF.support (genPrintableText n : SPMF (List Char)) ↔
      t.length ≤ n ∧ ∀ c ∈ t, c ∈ printableChars := by
  rw [genPrintableText]
  support_simp [genPrintableChar_mem_support]

theorem genSizeTwoText_mem_support {overhead : Nat} {t : List Char} :
    t ∈ SPMF.support (genSizeTwoText overhead : SPMF (List Char)) ↔
      t.length = 2 - overhead ∧ ∀ c ∈ t, c ∈ printableChars := by
  rw [genSizeTwoText]
  support_simp [genPrintableChar_mem_support]

/-! ## Chunks that force an edge case -/

/-- The lengths a chunk that must hold a marked element can have: one through `n`. -/
def markedLengths (n : Nat) : List Nat := List.range' 1 n

theorem mem_markedLengths_iff {n k : Nat} : k ∈ markedLengths n ↔ 0 < k ∧ k ≤ n := by
  rw [markedLengths, List.mem_range'_1]
  omega

theorem markedLengths_ne_nil {n : Nat} (h : 0 < n) : markedLengths n ≠ [] :=
  List.ne_nil_of_mem (a := 1) (mem_markedLengths_iff.mpr ⟨Nat.one_pos, h⟩)

/-- Generates a list whose length is drawn from `lengths` and whose elements all come from `g`
except one, at a uniformly chosen position, which comes from `gmark`. Drawing the length first
keeps it uniform over `lengths`, which is what lets a caller restrict it. -/
def genMarkedList [Gen G] (lengths : List Nat) (hne : lengths ≠ []) (g gmark : G α) :
    G (List α) := do
  let k ← elements lengths hne
  let p ← chooseNat 0 (k - 1) (Nat.zero_le _)
  let pre ← vectorOf p g
  let x ← gmark
  let post ← vectorOf (k - 1 - p) g
  return pre ++ x :: post

theorem genMarkedList_mem_support {lengths : List Nat} {hne : lengths ≠ []}
    (hpos : ∀ k ∈ lengths, 0 < k) {g gmark : SPMF α}
    (hsub : ∀ x ∈ SPMF.support gmark, x ∈ SPMF.support g) {xs : List α} :
    xs ∈ SPMF.support (genMarkedList lengths hne g gmark) ↔
      xs.length ∈ lengths ∧ (∀ x ∈ xs, x ∈ SPMF.support g) ∧
        ∃ x ∈ xs, x ∈ SPMF.support gmark := by
  rw [genMarkedList]
  support_simp
  constructor
  · rintro ⟨k, hk, p, ⟨-, hp⟩, pre, ⟨rfl, hpre⟩, x, hx, post, ⟨hpl, hpost⟩, rfl⟩
    have hk0 := hpos k hk
    have hlen : (pre ++ x :: post).length = k := by
      simp only [List.length_append, List.length_cons]
      omega
    refine ⟨by rw [hlen]; exact hk, ?_, x, by simp, hx⟩
    intro y hy
    simp only [List.mem_append, List.mem_cons] at hy
    rcases hy with hy | rfl | hy
    · exact hpre y hy
    · exact hsub y hx
    · exact hpost y hy
  · rintro ⟨hlen, hall, x, hxmem, hx⟩
    obtain ⟨s, t, rfl⟩ := List.append_of_mem hxmem
    refine ⟨(s ++ x :: t).length, hlen, s.length, ⟨Nat.zero_le _, ?_⟩,
      s, ⟨rfl, fun y hy => hall y (by simp [hy])⟩, x, hx, t,
      ⟨?_, fun y hy => hall y (by simp [hy])⟩, rfl⟩ <;>
      simp only [List.length_append, List.length_cons] <;> omega

/-- Generates a `rate` subsection that reuses the `LIST` chunk id. -/
def genListRate [Gen G] (b : Bounds) : G RateEntry := do
  let jifs ← chooseNat 0 b.maxJifRate
  return ⟨"LIST", jifs⟩

theorem genListRate_mem_support {b : Bounds} {r : RateEntry} :
    r ∈ SPMF.support (genListRate b : SPMF RateEntry) ↔
      r.name = "LIST" ∧ r.jifs ≤ b.maxJifRate := by
  obtain ⟨name, jifs⟩ := r
  rw [genListRate]
  support_simp [RateEntry.mk.injEq]
  constructor
  · rintro ⟨j, ⟨-, hj⟩, rfl, rfl⟩
    exact ⟨rfl, hj⟩
  · rintro ⟨rfl, hj⟩
    exact ⟨jifs, ⟨Nat.zero_le _, hj⟩, rfl, rfl⟩

/-- Generates a `rate` list within bounds, one subsection of which is named `LIST`. -/
def genRatesWithList [Gen G] (b : Bounds) (h : 0 < b.maxCSteps) : G (List RateEntry) :=
  genMarkedList (markedLengths b.maxCSteps) (markedLengths_ne_nil h) (genAnyRate b) (genListRate b)

theorem genRatesWithList_mem_support {b : Bounds} {h : 0 < b.maxCSteps} {rs : List RateEntry} :
    rs ∈ SPMF.support (genRatesWithList b h : SPMF (List RateEntry)) ↔
      rs.length ≤ b.maxCSteps ∧ (∀ r ∈ rs, r.WellFormed b) ∧
        ∃ r ∈ rs, r.name = "LIST" := by
  rw [genRatesWithList]
  rw [genMarkedList_mem_support (fun _ hk => (mem_markedLengths_iff.mp hk).1) (fun r hr => ?_)]
  · simp only [genAnyRate_mem_support, genListRate_mem_support, mem_markedLengths_iff,
      RateEntry.WellFormed]
    grind
  · rw [genListRate_mem_support] at hr
    rw [genAnyRate_mem_support, RateEntry.WellFormed, hr.1]
    exact ⟨by decide, hr.2⟩

/-- Generates a text field of length at most `n` that holds a non-printable character. -/
def genNonPrintableText [Gen G] (n : Nat) (h : 0 < n) : G (List Char) :=
  genMarkedList (markedLengths n) (markedLengths_ne_nil h) genAniChar
    (elements nonPrintableChars nonPrintableChars_ne_nil)

theorem genNonPrintableText_mem_support {n : Nat} {h : 0 < n} {t : List Char} :
    t ∈ SPMF.support (genNonPrintableText n h : SPMF (List Char)) ↔
      t.length ≤ n ∧ (∀ c ∈ t, c ∈ aniChars) ∧
        ∃ c ∈ t, c ∈ nonPrintableChars := by
  rw [genNonPrintableText]
  rw [genMarkedList_mem_support (fun _ hk => (mem_markedLengths_iff.mp hk).1) (fun c hc => ?_)]
  · simp only [genAniChar_mem_support, SPMF.mem_support_elements_iff, mem_markedLengths_iff]
    grind
  · rw [SPMF.mem_support_elements_iff] at hc
    rw [genAniChar_mem_support, aniChars]
    exact List.mem_append_right _ hc

/-! ## Chunk termination and cost -/

theorem genAniChar.terminates : IsAlmostSurelyTerminating (genAniChar : SPMF Char) := by
  mass_fixpoint using SPMF.LfpIsOne.one
  simp

theorem genAniChar.cost_bounded : IsCostBounded genAniChar (fun _ => 1) := by
  cost_fixpoint
  omega

theorem genAnyText.terminates {n : Nat} :
    IsAlmostSurelyTerminating (genAnyText n : SPMF (List Char)) := by
  mass_fixpoint using SPMF.LfpIsOne.one
  simp

theorem genAnyText.cost_bounded {n : Nat} :
    IsCostBounded (genAnyText n) (fun t => 1 + t.length) := by
  cost_fixpoint
  all_goals simp only [sum_map_const] at *; omega

theorem genPrintableText.terminates {n : Nat} :
    IsAlmostSurelyTerminating (genPrintableText n : SPMF (List Char)) := by
  mass_fixpoint using SPMF.LfpIsOne.one
  simp

theorem genPrintableText.cost_bounded {n : Nat} :
    IsCostBounded (genPrintableText n) (fun t => 1 + t.length) := by
  cost_fixpoint
  all_goals simp only [sum_map_const] at *; omega

theorem genSizeTwoText.terminates {overhead : Nat} :
    IsAlmostSurelyTerminating (genSizeTwoText overhead : SPMF (List Char)) := by
  mass_fixpoint using SPMF.LfpIsOne.one
  simp

theorem genSizeTwoText.cost_bounded {overhead : Nat} :
    IsCostBounded (genSizeTwoText overhead) (fun t => t.length) := by
  cost_fixpoint
  all_goals simp only [sum_map_const] at *; omega

theorem genAnyRate.terminates {b : Bounds} :
    IsAlmostSurelyTerminating (genAnyRate b : SPMF RateEntry) := by
  mass_fixpoint using SPMF.LfpIsOne.one
  simp

theorem genAnyRate.cost_bounded {b : Bounds} : IsCostBounded (genAnyRate b) (fun _ => 2) := by
  cost_fixpoint
  omega

theorem genAnyRates.terminates {b : Bounds} :
    IsAlmostSurelyTerminating (genAnyRates b : SPMF (List RateEntry)) := by
  mass_fixpoint using SPMF.LfpIsOne.one
  simp

theorem genAnyRates.cost_bounded {b : Bounds} :
    IsCostBounded (genAnyRates b) (fun rs => 1 + 2 * rs.length) := by
  cost_fixpoint
  all_goals simp only [sum_map_const] at *; omega

theorem genAnyJifRate.terminates {b : Bounds} :
    IsAlmostSurelyTerminating (genAnyJifRate b : SPMF Nat) := by
  mass_fixpoint using SPMF.LfpIsOne.one
  simp

theorem genAnyJifRate.cost_bounded {b : Bounds} : IsCostBounded (genAnyJifRate b) (fun _ => 1) := by
  cost_fixpoint
  omega

theorem genListRate.terminates {b : Bounds} :
    IsAlmostSurelyTerminating (genListRate b : SPMF RateEntry) := by
  mass_fixpoint using SPMF.LfpIsOne.one
  simp

theorem genListRate.cost_bounded {b : Bounds} : IsCostBounded (genListRate b) (fun _ => 1) := by
  cost_fixpoint
  omega

theorem genMarkedList.terminates {lengths : List Nat} {hne : lengths ≠ []} {g gmark : SPMF α}
    (hg : SPMF.IsPMF g) (hm : SPMF.IsPMF gmark) :
    IsAlmostSurelyTerminating (genMarkedList lengths hne g gmark) := by
  mass_fixpoint [hg, hm] using SPMF.LfpIsOne.one
  simp only [le_iInf_iff, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one, one_mul,
    Nat.card_Icc, Nat.sub_zero]
  exact fun _ => (ENNReal.div_self (by simp) (ENNReal.natCast_ne_top _)).ge

theorem genMarkedList.cost_bounded {lengths : List Nat} {hne : lengths ≠ []}
    {g gmark : SPMF.Cost α} {cg cm : Nat} (hcg : 0 < cg)
    (hg : IsBounded g fun _ => cg) (hm : IsBounded gmark fun _ => cm) :
    IsCostBounded (genMarkedList lengths hne g gmark) (fun xs => 1 + cm + cg * xs.length) := by
  cost_fixpoint [hg, hm]
  simp only [sum_map_const, List.length_append, List.length_cons] at *
  rw [Nat.mul_add, Nat.mul_add, Nat.mul_one]
  omega

theorem genRatesWithList.terminates {b : Bounds} {h : 0 < b.maxCSteps} :
    IsAlmostSurelyTerminating (genRatesWithList b h : SPMF (List RateEntry)) := by
  rw [genRatesWithList]
  exact genMarkedList.terminates genAnyRate.terminates genListRate.terminates

theorem genRatesWithList.cost_bounded {b : Bounds} {h : 0 < b.maxCSteps} :
    IsCostBounded (genRatesWithList b h) (fun rs => 2 + 2 * rs.length) := by
  rw [genRatesWithList]
  exact IsBounded_mono
    (genMarkedList.cost_bounded (by omega) genAnyRate.cost_bounded genListRate.cost_bounded)
    fun rs => by omega

theorem genNonPrintableText.terminates {n : Nat} {h : 0 < n} :
    IsAlmostSurelyTerminating (genNonPrintableText n h : SPMF (List Char)) := by
  rw [genNonPrintableText]
  exact genMarkedList.terminates genAniChar.terminates
    (SPMF.IsPMF.of_one_le (by mass_bound; simp))

theorem genNonPrintableText.cost_bounded {n : Nat} {h : 0 < n} :
    IsCostBounded (genNonPrintableText n h) (fun t => 2 + t.length) := by
  rw [genNonPrintableText]
  exact IsBounded_mono
    (genMarkedList.cost_bounded (cm := 1) (by omega) genAniChar.cost_bounded (by cost_bound; omega))
    fun t => by omega

/-! ## One generator per class -/

/-- Class 0: the image declares no icons. With no frame to index, the `seq ` chunk is empty and
the animation-step count — and so the `rate` list — is empty with it. -/
def genEdgeNoIcons [Gen G] (b : Bounds) : G Image :=
  genImage (pure []) (pure []) (fun _ _ => pure []) (genAnyText b.maxTitle)
    (genAnyText b.maxAuthor) (genAnyJifRate b)

/-- Class 1: the image has icons but a zero frame duration. -/
def genEdgeZeroJifRate [Gen G] (b : Bounds) (hicons : 0 < b.maxIcons) : G Image :=
  genImage (genAnyRates b) (genIcons 1 b.maxIcons hicons) genSeq (genAnyText b.maxTitle)
    (genAnyText b.maxAuthor) (pure 0)

/-- Class 2: a `rate` subsection reuses the `LIST` chunk id. -/
def genEdgeRateNamedList [Gen G] (b : Bounds) (hicons : 0 < b.maxIcons) (hjif : 0 < b.maxJifRate)
    (hsteps : 0 < b.maxCSteps) : G Image :=
  genImage (genRatesWithList b hsteps) (genIcons 1 b.maxIcons hicons) genSeq
    (genAnyText b.maxTitle) (genAnyText b.maxAuthor) (chooseNat 1 b.maxJifRate hjif)

/-- Class 3: the title holds a non-printable character. -/
def genEdgeTitleNonPrintable [Gen G] (b : Bounds) (hicons : 0 < b.maxIcons)
    (hjif : 0 < b.maxJifRate) (htitle : 0 < b.maxTitle) : G Image :=
  genImage (genStandardRates b) (genIcons 1 b.maxIcons hicons) genSeq
    (genNonPrintableText b.maxTitle htitle) (genAnyText b.maxAuthor)
    (chooseNat 1 b.maxJifRate hjif)

/-- Class 4: the title is printable and the author holds a non-printable character. -/
def genEdgeAuthorNonPrintable [Gen G] (b : Bounds) (hicons : 0 < b.maxIcons)
    (hjif : 0 < b.maxJifRate) (hauthor : 0 < b.maxAuthor) : G Image :=
  genImage (genStandardRates b) (genIcons 1 b.maxIcons hicons) genSeq
    (genPrintableText b.maxTitle) (genNonPrintableText b.maxAuthor hauthor)
    (chooseNat 1 b.maxJifRate hjif)

/-- Class 5: both fields are printable and the title's subsection declares a size of two bytes. -/
def genEdgeTitleSizeTwo [Gen G] (overhead : Nat) (b : Bounds) (hicons : 0 < b.maxIcons)
    (hjif : 0 < b.maxJifRate) : G Image :=
  genImage (genStandardRates b) (genIcons 1 b.maxIcons hicons) genSeq (genSizeTwoText overhead)
    (genPrintableText b.maxAuthor) (chooseNat 1 b.maxJifRate hjif)

/-- Class 6: both fields are printable, the title's subsection is not of size two, and the
author's is. -/
def genEdgeAuthorSizeTwo [Gen G] (overhead : Nat) (b : Bounds) (hicons : 0 < b.maxIcons)
    (hjif : 0 < b.maxJifRate) (htitle : overhead ≠ 2 ∨ 0 < b.maxTitle) : G Image :=
  genImage (genStandardRates b) (genIcons 1 b.maxIcons hicons) genSeq
    (genStandardText overhead b.maxTitle htitle) (genSizeTwoText overhead)
    (chooseNat 1 b.maxJifRate hjif)

theorem genEdgeNoIcons_mem_support {overhead : Nat} {b : Bounds} {img : Image} :
    img ∈ SPMF.support (genEdgeNoIcons b) ↔
      img.WellFormed b ∧ img.EdgeClass overhead 0 := by
  rw [genEdgeNoIcons, genImage_mem_support]
  simp only [genAnyText_mem_support, genAnyJifRate_mem_support, SPMF.mem_support_pure_iff,
    Image.WellFormed, Image.edgeClass_zero_iff, Image.NoIcons]
  constructor
  · grind
  · rintro ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩, h0⟩
    have hlen : img.icons.length = 0 := by omega
    have hicons : img.icons = [] := List.length_eq_zero_iff.mp hlen
    have hseq : img.seq = [] :=
      List.eq_nil_iff_forall_not_mem.mpr fun i hi => by have := h4 i hi; omega
    have hslen : img.seq.length = 0 := by rw [hseq]; rfl
    exact ⟨by omega, by omega, List.length_eq_zero_iff.mp (by omega), hicons, hseq,
      ⟨h9, h11⟩, ⟨h10, h12⟩, h8⟩

theorem genEdgeZeroJifRate_mem_support {overhead : Nat} {b : Bounds} {hicons : 0 < b.maxIcons}
    {img : Image} :
    img ∈ SPMF.support (genEdgeZeroJifRate b hicons) ↔
      img.WellFormed b ∧ img.EdgeClass overhead 1 := by
  rw [genEdgeZeroJifRate, genImage_mem_support]
  simp only [genAnyRates_mem_support, genIcons_mem_support, genSeq_mem_support,
    genAnyText_mem_support,
    SPMF.mem_support_pure_iff, Image.WellFormed, Image.edgeClass_one_iff, Image.NoIcons,
    Image.ZeroJifRate]
  grind

theorem genEdgeRateNamedList_mem_support {overhead : Nat} {b : Bounds} {hicons : 0 < b.maxIcons}
    {hjif : 0 < b.maxJifRate} {hsteps : 0 < b.maxCSteps} {img : Image} :
    img ∈ SPMF.support (genEdgeRateNamedList b hicons hjif hsteps) ↔
      img.WellFormed b ∧ img.EdgeClass overhead 2 := by
  rw [genEdgeRateNamedList, genImage_mem_support]
  simp only [genRatesWithList_mem_support, genIcons_mem_support, genSeq_mem_support,
    genAnyText_mem_support,
    SPMF.mem_support_chooseNat_iff, Image.WellFormed, Image.edgeClass_two_iff,
    Image.NoIcons, Image.ZeroJifRate, Image.RateNamedList]
  grind

theorem genEdgeTitleNonPrintable_mem_support {overhead : Nat} {b : Bounds} {hicons : 0 < b.maxIcons}
    {hjif : 0 < b.maxJifRate} {htitle : 0 < b.maxTitle} {img : Image} :
    img ∈ SPMF.support (genEdgeTitleNonPrintable b hicons hjif htitle) ↔
      img.WellFormed b ∧ img.EdgeClass overhead 3 := by
  rw [genEdgeTitleNonPrintable, genImage_mem_support]
  simp only [genStandardRates_mem_support, genIcons_mem_support, genSeq_mem_support,
    genNonPrintableText_mem_support,
    genAnyText_mem_support, SPMF.mem_support_chooseNat_iff, Image.WellFormed,
    Image.edgeClass_three_iff, Image.NoIcons, Image.ZeroJifRate, Image.RateNamedList]
  grind

theorem genEdgeAuthorNonPrintable_mem_support {overhead : Nat} {b : Bounds}
    {hicons : 0 < b.maxIcons} {hjif : 0 < b.maxJifRate} {hauthor : 0 < b.maxAuthor} {img : Image} :
    img ∈ SPMF.support (genEdgeAuthorNonPrintable b hicons hjif hauthor) ↔
      img.WellFormed b ∧ img.EdgeClass overhead 4 := by
  rw [genEdgeAuthorNonPrintable, genImage_mem_support]
  simp only [genStandardRates_mem_support, genIcons_mem_support, genSeq_mem_support,
    genPrintableText_mem_support,
    genNonPrintableText_mem_support, SPMF.mem_support_chooseNat_iff, Image.WellFormed,
    Image.edgeClass_four_iff, Image.NoIcons, Image.ZeroJifRate, Image.RateNamedList,
    mem_printableChars_iff_mem_aniChars]
  grind

theorem genEdgeTitleSizeTwo_mem_support {overhead : Nat} {b : Bounds} (hover : overhead ≤ 2)
    (hsize : 2 - overhead ≤ b.maxTitle) {hicons : 0 < b.maxIcons} {hjif : 0 < b.maxJifRate}
    {img : Image} :
    img ∈ SPMF.support (genEdgeTitleSizeTwo overhead b hicons hjif) ↔
      img.WellFormed b ∧ img.EdgeClass overhead 5 := by
  rw [genEdgeTitleSizeTwo, genImage_mem_support]
  simp only [genStandardRates_mem_support, genIcons_mem_support, genSeq_mem_support,
    genSizeTwoText_mem_support,
    genPrintableText_mem_support, SPMF.mem_support_chooseNat_iff, Image.WellFormed,
    Image.edgeClass_five_iff, Image.NoIcons, Image.ZeroJifRate, Image.RateNamedList,
    infoSize, mem_printableChars_iff_mem_aniChars]
  grind

theorem genEdgeAuthorSizeTwo_mem_support {overhead : Nat} {b : Bounds} (hover : overhead ≤ 2)
    (hsize : 2 - overhead ≤ b.maxAuthor) {hicons : 0 < b.maxIcons} {hjif : 0 < b.maxJifRate}
    {htitle : overhead ≠ 2 ∨ 0 < b.maxTitle} {img : Image} :
    img ∈ SPMF.support (genEdgeAuthorSizeTwo overhead b hicons hjif htitle) ↔
      img.WellFormed b ∧ img.EdgeClass overhead 6 := by
  rw [genEdgeAuthorSizeTwo, genImage_mem_support]
  simp only [genStandardRates_mem_support, genIcons_mem_support, genSeq_mem_support,
    genStandardText_mem_support,
    genSizeTwoText_mem_support, SPMF.mem_support_chooseNat_iff, Image.WellFormed,
    Image.edgeClass_six_iff, Image.NoIcons, Image.ZeroJifRate, Image.RateNamedList,
    infoSize, mem_printableChars_iff_mem_aniChars]
  grind

/-! ## The edge-case generator -/

/-- Generates an ANI image within `b` that contains at least one edge case, by drawing one of the
seven `Image.EdgeClass`es uniformly and then an image of that class. The bounds must admit every
class: each denies the ambiguities that precede it, so an image with no icons, a zero frame
duration, no `rate` subsections, or a text field too short to hold a character or a size-two
subsection would leave one of the seven empty. -/
def genSpecialImage [Gen G] (overhead : Nat) (b : Bounds) (_hover : overhead ≤ 2)
    (hicons : 0 < b.maxIcons) (hjif : 0 < b.maxJifRate) (hsteps : 0 < b.maxCSteps)
    (htitle : 0 < b.maxTitle) (hauthor : 0 < b.maxAuthor)
    (_hsizeTitle : 2 - overhead ≤ b.maxTitle) (_hsizeAuthor : 2 - overhead ≤ b.maxAuthor) :
    G Image :=
  oneOf [
    fun () => genEdgeNoIcons b,
    fun () => genEdgeZeroJifRate b hicons,
    fun () => genEdgeRateNamedList b hicons hjif hsteps,
    fun () => genEdgeTitleNonPrintable b hicons hjif htitle,
    fun () => genEdgeAuthorNonPrintable b hicons hjif hauthor,
    fun () => genEdgeTitleSizeTwo overhead b hicons hjif,
    fun () => genEdgeAuthorSizeTwo overhead b hicons hjif (Or.inr htitle)
  ] (by simp)

theorem genSpecialImage.sound_complete (overhead : Nat) (b : Bounds) (hover : overhead ≤ 2)
    (hicons : 0 < b.maxIcons) (hjif : 0 < b.maxJifRate) (hsteps : 0 < b.maxCSteps)
    (htitle : 0 < b.maxTitle) (hauthor : 0 < b.maxAuthor)
    (hsizeTitle : 2 - overhead ≤ b.maxTitle) (hsizeAuthor : 2 - overhead ≤ b.maxAuthor) :
    IsSoundAndComplete
        (genSpecialImage overhead b hover hicons hjif hsteps htitle hauthor hsizeTitle hsizeAuthor)
      (fun img => img.WellFormed b ∧ img.HasEdgeCase overhead) := by
  intro img
  rw [genSpecialImage]
  simp only [SPMF.mem_support_oneOf_iff, List.mem_cons, List.not_mem_nil, or_false,
    exists_eq_or_imp, exists_eq_left, genEdgeNoIcons_mem_support (overhead := overhead),
    genEdgeZeroJifRate_mem_support (overhead := overhead),
    genEdgeRateNamedList_mem_support (overhead := overhead),
    genEdgeTitleNonPrintable_mem_support (overhead := overhead),
    genEdgeAuthorNonPrintable_mem_support (overhead := overhead),
    genEdgeTitleSizeTwo_mem_support hover hsizeTitle,
    genEdgeAuthorSizeTwo_mem_support hover hsizeAuthor,
    Image.hasEdgeCase_iff_exists_edgeClass]
  constructor
  · rintro (⟨hw, h⟩ | ⟨hw, h⟩ | ⟨hw, h⟩ | ⟨hw, h⟩ | ⟨hw, h⟩ |
      ⟨hw, h⟩ | ⟨hw, h⟩) <;>
      exact ⟨hw, _, h⟩
  · rintro ⟨hw, i, hi⟩
    match i, hi with
    | 0, h => exact Or.inl ⟨hw, h⟩
    | 1, h => exact Or.inr (Or.inl ⟨hw, h⟩)
    | 2, h => exact Or.inr (Or.inr (Or.inl ⟨hw, h⟩))
    | 3, h => exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hw, h⟩)))
    | 4, h => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hw, h⟩))))
    | 5, h => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hw, h⟩)))))
    | 6, h => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hw, h⟩)))))
    | _ + 7, h => exact h.1.elim

theorem genSpecialImage.terminates (overhead : Nat) (b : Bounds) (hover : overhead ≤ 2)
    (hicons : 0 < b.maxIcons) (hjif : 0 < b.maxJifRate) (hsteps : 0 < b.maxCSteps)
    (htitle : 0 < b.maxTitle) (hauthor : 0 < b.maxAuthor)
    (hsizeTitle : 2 - overhead ≤ b.maxTitle) (hsizeAuthor : 2 - overhead ≤ b.maxAuthor) :
    IsAlmostSurelyTerminating
      (genSpecialImage overhead b hover hicons hjif hsteps htitle hauthor hsizeTitle
        hsizeAuthor) := by
  unfold genSpecialImage genEdgeNoIcons genEdgeZeroJifRate genEdgeRateNamedList
    genEdgeTitleNonPrintable genEdgeAuthorNonPrintable genEdgeTitleSizeTwo genEdgeAuthorSizeTwo
    genImage
  exact SPMF.IsPMF.of_one_le (by mass_bound; norm_num [ENNReal.div_self])

theorem genSpecialImage.cost_bounded (overhead : Nat) (b : Bounds) (hover : overhead ≤ 2)
    (hicons : 0 < b.maxIcons) (hjif : 0 < b.maxJifRate) (hsteps : 0 < b.maxCSteps)
    (htitle : 0 < b.maxTitle) (hauthor : 0 < b.maxAuthor)
    (hsizeTitle : 2 - overhead ≤ b.maxTitle) (hsizeAuthor : 2 - overhead ≤ b.maxAuthor) :
    IsCostBounded
      (genSpecialImage overhead b hover hicons hjif hsteps htitle hauthor hsizeTitle hsizeAuthor)
      (fun img => 7 + 2 * img.rates.length + img.seq.length + img.info.title.length +
        img.info.author.length) := by
  unfold genSpecialImage genEdgeNoIcons genEdgeZeroJifRate genEdgeRateNamedList
    genEdgeTitleNonPrintable genEdgeAuthorNonPrintable genEdgeTitleSizeTwo genEdgeAuthorSizeTwo
    genImage
  cost_bound
  all_goals simp only [List.length_nil, Nat.add_zero] at *; omega

end AniImage
