/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt.SPMF.Cost

/-!
# Proof-Recipe Tactics

Packaged `simp only` sets for support inversion: `support_simp` at the `SPMF` interpretation,
`cost_support_simp` at `SPMF.Cost`. Both accept extra simp lemmas and an optional location,
like `simp only`.
-/

open Lean.Parser.Tactic

/-- `simp only` with the standard `SPMF` support-inversion set (`mem_support_*_iff`), plus any
extra lemmas given. -/
syntax "support_simp" (" [" simpArg,* "]")? (location)? : tactic

macro_rules
  | `(tactic| support_simp $[$loc:location]?) => `(tactic| support_simp [] $[$loc]?)
  | `(tactic| support_simp [$args,*] $[$loc:location]?) =>
    `(tactic| simp only [SPMF.mem_support_pick_iff, SPMF.mem_support_bind_iff,
        SPMF.mem_support_pure_iff, SPMF.mem_support_map_iff, SPMF.mem_support_choose_iff,
        SPMF.mem_support_chooseNat_iff, SPMF.mem_support_chooseInt_iff, SPMF.mem_support_ite_iff, SPMF.mem_support_dite_iff,
        SPMF.mem_support_elements_iff, SPMF.mem_support_oneOf_iff,
        SPMF.mem_support_frequency_iff, SPMF.mem_support_vectorOf_iff,
        SPMF.mem_support_listOfMaxLength_iff, SPMF.mem_support_listOf, Set.mem_ofPred_eq,
        $args,*] $[$loc]?)

/-- `simp only` with the standard `SPMF.Cost` support-inversion set
(`SPMF.Cost.mem_support_*_iff`), plus any extra lemmas given. -/
syntax "cost_support_simp" (" [" simpArg,* "]")? (location)? : tactic

macro_rules
  | `(tactic| cost_support_simp $[$loc:location]?) => `(tactic| cost_support_simp [] $[$loc]?)
  | `(tactic| cost_support_simp [$args,*] $[$loc:location]?) =>
    `(tactic| simp only [SPMF.Cost.mem_support_pick_iff, SPMF.Cost.mem_support_bind_iff,
        SPMF.Cost.mem_support_pure_iff, SPMF.Cost.mem_support_map_iff,
        SPMF.Cost.mem_support_choose_iff, SPMF.Cost.mem_support_chooseNat_iff,
        SPMF.Cost.mem_support_chooseInt_iff,
        SPMF.mem_support_ite_iff, SPMF.mem_support_dite_iff,
        $args,*] $[$loc]?)
