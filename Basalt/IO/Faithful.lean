/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt.IO.Approx
import Basalt.IO.Laws
import Basalt.IO.Stream

/-!
# From `IO` to `SPMF`

A generator is proved correct at `SPMF` and run at `IO`. `idealized_faithful` is the chain between
the two: what the library proves of it, and the premises it takes.
-/

open Lean.Order

/-- A faithful generator runs at `IO` as it does at `IOModel`, which draws SplitMix's words, and
drawing ideal words instead it has the distribution we work with at `SPMF`. This is what the
library proves and assumes between `SPMF` and an `IO` run; every other mention points here.

Proved, per generator:

- `h_faithful`: the generator runs at `IO` as at `IOModel` wherever that terminates, and on any
  ideal source has its `SPMF` distribution. It would be a free theorem of the generator's
  polymorphism, but Lean's classical logic gives none, so it is the `IsFaithful` law.

Assumed:

- `h_ioGen`: `ioGen` agrees with the SplitMix specification (`IOModel.IOGenLaws`, which says what
  this reads `IO`'s world as, and why Lean decides nothing about it). True if (1) the C code is
  faithful to the Lean specification, which `BasaltTest/IO.lean` checks by running the two against
  each other, and (2) no other thread uses `ioGen` during the run.
- SplitMix's words are ideal: `IOModel`, which is `WordModel SplitMix`, is read as `WordModel` on an
  ideal source, `WordStream.ideal`. This is a model, in the sense of the random-oracle model, not a
  hypothesis: no statement that a freshly seeded SplitMix is close to ideal holds on every event,
  since it has `2 ^ 64` seeds and `mix64` is invertible. The justification is that SplitMix is
  designed to be indistinguishable from ideal by statistical tests, and passes BigCrush. -/
theorem idealized_faithful {α : Type} {gen : {G : Type → Type} → [Gen G] → G α}
    (h_faithful : IsFaithful gen)
    (h_ioGen : IOModel.IOGenLaws) :
    (gen (G := IOModel)).toIO ⊑ gen (G := IO) ∧
      WordStream.ideal.dist (gen (G := WordModel WordStream)) = gen (G := SPMF) :=
  ⟨h_faithful.approx h_ioGen, h_faithful.wordStream⟩
