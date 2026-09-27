/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt.IO.Approx
import Basalt.IO.Ideal
import Basalt.Laws

/-!
# The Law Relating `IO` to `SPMF`

`IsFaithful`, the one law that relates two interpretations of a generator rather than constraining
one. The others are `Basalt/Laws.lean`'s.
-/

/-- A generator `gen` `IsFaithful` if, run on any ideal source of words, it has its `SPMF`
distribution (`IsFaithful.dist`), and at `IO` it does what it does at `IOModel` wherever that
terminates (`approx`). Unlike the other laws it takes the polymorphic generator, since it relates
two of its interpretations. What it leaves between `SPMF` and an `IO` run is `idealized_faithful`
(`Basalt/IO/Faithful.lean`).

`below` is a field rather than the distribution it gives because it composes through binds and the
distribution does not; `terminates` turns one into the other. `faithful_fixpoint` proves all
three. -/
structure IsFaithful (gen : {G : Type → Type} → [Gen G] → G α) : Prop where
  terminates : IsAlmostSurelyTerminating (gen (G := SPMF))
  below : ∀ (σ : Type) [WordSource σ] (src : IdealSource σ), src.Below gen gen
  approx : IOModel.Approx gen gen

/-- A faithful generator, run on an ideal source, has its `SPMF` distribution. -/
theorem IsFaithful.dist {gen : {G : Type → Type} → [Gen G] → G α} (h : IsFaithful gen)
    {σ : Type} [WordSource σ] (src : IdealSource σ) :
    src.dist (gen (G := WordModel σ)) = gen (G := SPMF) :=
  src.dist_eq (h.below σ src) h.terminates
