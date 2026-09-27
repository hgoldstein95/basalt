/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt.GenRel
import Basalt.SPMF.CostErasure
import Basalt.Walk.Attr

/-!
# Walking Cost Erasure

The rules by which `walk` relates a generator at `SPMF.Cost` to the same generator at `SPMF`, in
each direction, `ErasedLe (gen …) (gen …)` and `LeErased (gen …) (gen …)`: each combinator's is
`GenRel`'s.
-/

namespace SPMF.Cost

variable {α : Type}

theorem genRel_erasedLe : GenRel SPMF.Cost SPMF @ErasedLe where
  pure := erasedLe_pure
  bind := erasedLe_bind
  map := erasedLe_map
  default := erasedLe_default
  choose := erasedLe_choose
  admissible := ErasedLe.admissible

theorem genRel_leErased : GenRel SPMF SPMF.Cost @LeErased where
  pure := leErased_pure
  bind := leErased_bind
  map := leErased_map
  default := leErased_default
  choose := leErased_choose
  admissible := LeErased.admissible

section erasedLe

@[gen_rule]
theorem erasedLe_elements (xs : List α) (hne : xs ≠ []) :
    ErasedLe (elements xs hne) (elements xs hne) :=
  genRel_erasedLe.elements xs hne

@[gen_rule]
theorem erasedLe_vectorOf {g' : SPMF.Cost α} {g : SPMF α} (n : Nat) (hg : ErasedLe g' g) :
    ErasedLe (vectorOf n g') (vectorOf n g) :=
  genRel_erasedLe.vectorOf n hg

@[gen_rule]
theorem erasedLe_listOf {g' : SPMF.Cost α} {g : SPMF α} (hg : ErasedLe g' g) :
    ErasedLe (listOf g') (listOf g) :=
  genRel_erasedLe.listOf hg

@[gen_rule]
theorem erasedLe_nonEmptyListOf {g' : SPMF.Cost α} {g : SPMF α} (hg : ErasedLe g' g) :
    ErasedLe (nonEmptyListOf g') (nonEmptyListOf g) :=
  genRel_erasedLe.nonEmptyListOf hg

@[gen_rule]
theorem erasedLe_suchThat {g' : SPMF.Cost α} {g : SPMF α} (p : α → Bool) (hg : ErasedLe g' g) :
    ErasedLe (suchThat g' p) (suchThat g p) :=
  genRel_erasedLe.suchThat p hg

@[gen_rule]
theorem erasedLe_permutationOf (xs : List α) : ErasedLe (permutationOf xs) (permutationOf xs) :=
  genRel_erasedLe.permutationOf xs

@[gen_rule]
theorem erasedLe_oneOf {gs' : List (Unit → SPMF.Cost α)} {gs : List (Unit → SPMF α)}
    {hne' : gs' ≠ []} {hne : gs ≠ []}
    (h : List.Forall₂ (fun g' g => ErasedLe (g' ()) (g ())) gs' gs) :
    ErasedLe (oneOf gs' hne') (oneOf gs hne) :=
  genRel_erasedLe.oneOf h

@[gen_rule]
theorem erasedLe_frequency {gs' : List (Nat × (Unit → SPMF.Cost α))}
    {gs : List (Nat × (Unit → SPMF α))} {h' : 0 < (gs'.map Prod.fst).sum}
    {h : 0 < (gs.map Prod.fst).sum} (hgs : GenRel.Weighted @ErasedLe gs' gs) :
    ErasedLe (frequency gs' h') (frequency gs h) :=
  genRel_erasedLe.frequency hgs

end erasedLe

section leErased

@[gen_rule]
theorem leErased_elements (xs : List α) (hne : xs ≠ []) :
    LeErased (elements xs hne) (elements xs hne) :=
  genRel_leErased.elements xs hne

@[gen_rule]
theorem leErased_vectorOf {g' : SPMF α} {g : SPMF.Cost α} (n : Nat) (hg : LeErased g' g) :
    LeErased (vectorOf n g') (vectorOf n g) :=
  genRel_leErased.vectorOf n hg

@[gen_rule]
theorem leErased_listOf {g' : SPMF α} {g : SPMF.Cost α} (hg : LeErased g' g) :
    LeErased (listOf g') (listOf g) :=
  genRel_leErased.listOf hg

@[gen_rule]
theorem leErased_nonEmptyListOf {g' : SPMF α} {g : SPMF.Cost α} (hg : LeErased g' g) :
    LeErased (nonEmptyListOf g') (nonEmptyListOf g) :=
  genRel_leErased.nonEmptyListOf hg

@[gen_rule]
theorem leErased_suchThat {g' : SPMF α} {g : SPMF.Cost α} (p : α → Bool) (hg : LeErased g' g) :
    LeErased (suchThat g' p) (suchThat g p) :=
  genRel_leErased.suchThat p hg

@[gen_rule]
theorem leErased_permutationOf (xs : List α) : LeErased (permutationOf xs) (permutationOf xs) :=
  genRel_leErased.permutationOf xs

@[gen_rule]
theorem leErased_oneOf {gs' : List (Unit → SPMF α)} {gs : List (Unit → SPMF.Cost α)}
    {hne' : gs' ≠ []} {hne : gs ≠ []}
    (h : List.Forall₂ (fun g' g => LeErased (g' ()) (g ())) gs' gs) :
    LeErased (oneOf gs' hne') (oneOf gs hne) :=
  genRel_leErased.oneOf h

@[gen_rule]
theorem leErased_frequency {gs' : List (Nat × (Unit → SPMF α))}
    {gs : List (Nat × (Unit → SPMF.Cost α))} {h' : 0 < (gs'.map Prod.fst).sum}
    {h : 0 < (gs.map Prod.fst).sum} (hgs : GenRel.Weighted @LeErased gs' gs) :
    LeErased (frequency gs' h') (frequency gs h) :=
  genRel_leErased.frequency hgs

end leErased

end SPMF.Cost
