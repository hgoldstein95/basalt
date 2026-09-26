/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Mathlib.Data.List.Forall2
import Basalt.GenRel
import Basalt.IO.Approx
import Basalt.Walk.Attr

/-!
# Walking `IO` Against `IOModel`

The rules by which `walk` relates a generator at `IOModel` to the same generator at `IO`,
`IOModel.Approx (gen …) (gen …)`: each combinator's is `GenRel`'s.
-/

namespace IOModel

theorem genRel : GenRel IOModel IO @Approx where
  pure := approx_pure
  bind := approx_bind
  map := approx_map
  default := approx_default
  choose := approx_choose
  admissible := Approx.admissible

@[gen_rule]
theorem approx_elements (xs : List α) (hne : xs ≠ []) :
    Approx (elements xs hne) (elements xs hne) :=
  genRel.elements xs hne

@[gen_rule]
theorem approx_vectorOf {g' : IOModel α} {g : IO α} (n : Nat) (hg : Approx g' g) :
    Approx (vectorOf n g') (vectorOf n g) :=
  genRel.vectorOf n hg

@[gen_rule]
theorem approx_listOf {g' : IOModel α} {g : IO α} (hg : Approx g' g) :
    Approx (listOf g') (listOf g) :=
  genRel.listOf hg

@[gen_rule]
theorem approx_nonEmptyListOf {g' : IOModel α} {g : IO α} (hg : Approx g' g) :
    Approx (nonEmptyListOf g') (nonEmptyListOf g) :=
  genRel.nonEmptyListOf hg

@[gen_rule]
theorem approx_permutationOf (xs : List α) : Approx (permutationOf xs) (permutationOf xs) :=
  genRel.permutationOf xs

@[gen_rule]
theorem approx_oneOf {gs' : List (Unit → IOModel α)} {gs : List (Unit → IO α)}
    {hne' : gs' ≠ []} {hne : gs ≠ []}
    (h : List.Forall₂ (fun g' g => Approx (g' ()) (g ())) gs' gs) :
    Approx (oneOf gs' hne') (oneOf gs hne) :=
  genRel.oneOf h

@[gen_rule]
theorem approx_frequency {gs' : List (Nat × (Unit → IOModel α))}
    {gs : List (Nat × (Unit → IO α))} {h' : 0 < (gs'.map Prod.fst).sum}
    {h : 0 < (gs.map Prod.fst).sum} (hgs : GenRel.Weighted @Approx gs' gs) :
    Approx (frequency gs' h') (frequency gs h) :=
  genRel.frequency hgs

end IOModel
