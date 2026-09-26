/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt.GenRel
import Basalt.IO.Choose
import Basalt.IO.Ideal
import Basalt.Walk.Attr

/-!
# Walking the Ideal Source

The rules by which `walk` relates a generator at `SPMF` to the same generator at `WordModel σ`,
`src.Below (gen …) (gen …)`: each combinator's is `GenRel`'s.
-/

namespace IdealSource

variable {σ : Type} [WordSource σ] (src : IdealSource σ)

theorem genRel : GenRel SPMF (WordModel σ) (@IdealSource.Below σ _ src) where
  pure := src.below_pure
  bind := src.below_bind
  map := src.below_map
  default := src.below_default
  choose := src.below_choose
  admissible := IdealSource.Below.admissible src

@[gen_rule]
theorem below_elements (xs : List α) (hne : xs ≠ []) :
    src.Below (elements xs hne) (elements xs hne) :=
  src.genRel.elements xs hne

@[gen_rule]
theorem below_vectorOf {g' : SPMF α} {g : WordModel σ α} (n : Nat) (hg : src.Below g' g) :
    src.Below (vectorOf n g') (vectorOf n g) :=
  src.genRel.vectorOf n hg

@[gen_rule]
theorem below_listOf {g' : SPMF α} {g : WordModel σ α} (hg : src.Below g' g) :
    src.Below (listOf g') (listOf g) :=
  src.genRel.listOf hg

@[gen_rule]
theorem below_nonEmptyListOf {g' : SPMF α} {g : WordModel σ α} (hg : src.Below g' g) :
    src.Below (nonEmptyListOf g') (nonEmptyListOf g) :=
  src.genRel.nonEmptyListOf hg

@[gen_rule]
theorem below_permutationOf (xs : List α) : src.Below (permutationOf xs) (permutationOf xs) :=
  src.genRel.permutationOf xs

@[gen_rule]
theorem below_oneOf {gs' : List (Unit → SPMF α)} {gs : List (Unit → WordModel σ α)}
    {hne' : gs' ≠ []} {hne : gs ≠ []}
    (h : List.Forall₂ (fun g' g => src.Below (g' ()) (g ())) gs' gs) :
    src.Below (oneOf gs' hne') (oneOf gs hne) :=
  src.genRel.oneOf h

@[gen_rule]
theorem below_frequency {gs' : List (Nat × (Unit → SPMF α))}
    {gs : List (Nat × (Unit → WordModel σ α))} {h' : 0 < (gs'.map Prod.fst).sum}
    {h : 0 < (gs.map Prod.fst).sum} (hgs : GenRel.Weighted (@IdealSource.Below σ _ src) gs' gs) :
    src.Below (frequency gs' h') (frequency gs h) :=
  src.genRel.frequency hgs

end IdealSource
