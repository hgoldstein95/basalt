/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Batteries.Data.Char

/-!
# ANI Images (definitions)

An abstraction of the context-sensitive ANI (animated cursor) grammar: the `anih` header, the
`LIST INFO` title and author subsections, the `rate` and `seq ` subsections, and the icon frames,
together with the header counts that must agree with the chunks they describe and the animation
sequence that must index a frame that exists. Chunk ids and icon contents are modelled
symbolically rather than as bytes, and the `seq ` chunk is taken to be present, which is what
frees the animation-step count from the frame count. `Image.WellFormed` is the standard definition
of the format and `Image.HasEdgeCase` collects the five ambiguities of Dewey, Nichols &
Hardekopf's (ICSE 2015, §V) additional property, which a standard image avoids.
-/

namespace AniImage

/-- The chunk ids a `rate` subsection may declare: its own, and the `LIST` id that also introduces
the info and frame chunks. Reusing `LIST` is the `Image.RateNamedList` ambiguity, so it has to stay
inside the standard definition; any other id is not an ambiguity but a malformed image. -/
def rateNames : List String := ["rate", "LIST"]

/-- The characters whose code points run from `lo` through `hi`. -/
def asciiChars (lo hi : Nat) : List Char :=
  (List.range (hi + 1 - lo)).map fun i => Char.ofNat (lo + i)

/-- The printable ASCII characters, space through tilde. -/
def printableChars : List Char := asciiChars 0x20 0x7E

/-- The non-printable characters a text field may hold: the C0 controls and `DEL`. -/
def nonPrintableChars : List Char := asciiChars 0x00 0x1F ++ asciiChars 0x7F 0x7F

/-- The alphabet of the `title` and `author` fields: the ASCII range, printable and not. -/
def aniChars : List Char := printableChars ++ nonPrintableChars

/-- The size an `InfoList` subsection declares for `text`: the text plus `overhead` bytes.

The overhead is a parameter because the format does not fix it and `Image.InfoSizeTwo` names a
size rather than a length: `overhead = 0` counts the text alone, `overhead = 1` adds the NUL
terminator of a RIFF `INFO` string, `overhead = 2` also counts the pad byte that keeps a subsection
word-aligned. The choice decides which fields the edge case selects — the two-character ones, the
one-character ones, or the empty one — so the generators take it rather than assume it. -/
def infoSize (overhead : Nat) (text : List Char) : Nat := text.length + overhead

/-- An icon frame. The format bounds how many icons an image has, not what they contain, so the
abstraction keeps only their presence. -/
inductive Icon where
  | icon
  deriving Repr

/-- A `rate` subsection: the chunk id it declares and the duration, in jiffies, of the animation
step it governs. -/
structure RateEntry where
  name : String
  jifs : Nat
  deriving Repr

/-- The `LIST INFO` chunk: the two text subsections ANI defines. -/
structure InfoList where
  title : List Char
  author : List Char
  deriving Repr

/-- The `anih` header: the number of animation steps, the number of icon frames, and the default
frame duration in jiffies. -/
structure Header where
  cSteps : Nat
  nFrames : Nat
  jifRate : Nat
  deriving Repr

/-- An ANI image. `seq` is the `seq ` chunk: one frame index per animation step. -/
structure Image where
  header : Header
  info : InfoList
  rates : List RateEntry
  seq : List Nat
  icons : List Icon
  deriving Repr

/-- The bounds a bounded-exhaustive search fixes before enumerating images. -/
structure Bounds where
  maxIcons : Nat
  maxTitle : Nat
  maxAuthor : Nat
  maxCSteps : Nat
  maxJifRate : Nat

/-- A `rate` subsection is well-formed when it declares a known chunk id and an in-bounds duration. -/
def RateEntry.WellFormed (b : Bounds) (r : RateEntry) : Prop :=
  r.name ∈ rateNames ∧ r.jifs ≤ b.maxJifRate

/-- An ANI image is well-formed within `b` when the header's counts agree with the chunks they
describe and every field is within bounds. -/
def Image.WellFormed (b : Bounds) (img : Image) : Prop :=
  img.header.nFrames = img.icons.length ∧
  img.header.cSteps = img.rates.length ∧
  img.seq.length = img.header.cSteps ∧
  (∀ i ∈ img.seq, i < img.icons.length) ∧
  img.icons.length ≤ b.maxIcons ∧
  img.rates.length ≤ b.maxCSteps ∧
  (∀ r ∈ img.rates, r.WellFormed b) ∧
  img.header.jifRate ≤ b.maxJifRate ∧
  img.info.title.length ≤ b.maxTitle ∧
  img.info.author.length ≤ b.maxAuthor ∧
  (∀ c ∈ img.info.title, c ∈ aniChars) ∧
  (∀ c ∈ img.info.author, c ∈ aniChars)

/-- A `rate` subsection is named `LIST`, which a parser cannot tell apart from the `LIST` chunk
carrying the info and frame data. -/
def Image.RateNamedList (img : Image) : Prop :=
  ∃ r ∈ img.rates, r.name = "LIST"

/-- An `InfoList` subsection declares a size of two bytes, which valid data does not produce. -/
def Image.InfoSizeTwo (overhead : Nat) (img : Image) : Prop :=
  infoSize overhead img.info.title = 2 ∨ infoSize overhead img.info.author = 2

/-- The title or author holds a non-printable character. -/
def Image.NonPrintableText (img : Image) : Prop :=
  (∃ c ∈ img.info.title, c ∈ nonPrintableChars) ∨
    (∃ c ∈ img.info.author, c ∈ nonPrintableChars)

/-- The image declares no icons, though icons are its core content. -/
def Image.NoIcons (img : Image) : Prop :=
  img.header.nFrames = 0

/-- The header's frame duration is zero: an animation that would run infinitely fast. -/
def Image.ZeroJifRate (img : Image) : Prop :=
  img.header.jifRate = 0

/-- The five edge cases the standard definition avoids. -/
def Image.HasEdgeCase (overhead : Nat) (img : Image) : Prop :=
  img.RateNamedList ∨ img.InfoSizeTwo overhead ∨ img.NonPrintableText ∨ img.NoIcons ∨
    img.ZeroJifRate

end AniImage
