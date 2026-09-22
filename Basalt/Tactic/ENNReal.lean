/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.ENNReal.Inv
import Mathlib.Tactic.Finiteness
import Mathlib.Tactic.Bound
import Mathlib.Tactic.Positivity

open scoped ENNReal NNReal

/-!
# ENNReal proof automation

`ℝ≥0∞` has no `ring`/`linarith`-style automation, so arithmetic goals are transferred to `ℝ`:

1. `finiteness` rule-set extensions for the shapes the stock rules miss: `x ≠ ⊤` from
   `x ≤ 1` (every mass is `≤ 1`), and `x⁻¹ ≠ ⊤` from `x ≠ 0`.
2. `ennreal_to_real`, moving a `≤`/`=` goal (or hypothesis, via `at h`) across `.toReal`,
   with side conditions discharged by the extended `finiteness`. Finish with
   `norm_num` / `linarith` / `nlinarith` / `field_simp`.
-/

/-! ## `finiteness` extensions -/

theorem ENNReal.ne_top_of_le_one' {x : ℝ≥0∞} (h : x ≤ 1) : x ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top h

theorem ENNReal.inv_ne_top' {x : ℝ≥0∞} (h : x ≠ 0) : x⁻¹ ≠ ⊤ :=
  ENNReal.inv_ne_top.mpr h

attribute [aesop unsafe 90% apply (rule_sets := [finiteness])]
  ENNReal.ne_top_of_le_one' ENNReal.inv_ne_top'

/-! ## The transfer macro

Caveats:
- transfer a hypothesis *before* the ENNReal facts it needs for finiteness are themselves
  transferred (or `have` a copy);
- one location per invocation;
- an atom with no `≠ ⊤` evidence needs `rcases eq_or_ne t ⊤ with rfl | htop` first
  (the `⊤` case is usually `simp`). -/

macro "ennreal_to_real" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic|
    ((try rw [ge_iff_le] $[$loc]?);
     (try rw [← ENNReal.toReal_le_toReal (by finiteness) (by finiteness)] $[$loc]?);
     (try rw [← ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)] $[$loc]?);
     repeat
       (first
         | rw [ENNReal.toReal_add (by finiteness) (by finiteness)] $[$loc]?
         | rw [ENNReal.toReal_sub_of_le
             (by first | assumption | bound | simp [ENNReal.div_le_iff] <;> norm_num)
             (by finiteness)] $[$loc]?
         | simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_div,
             ENNReal.toReal_inv, ENNReal.toReal_ofNat, ENNReal.toReal_one,
             ENNReal.toReal_natCast] $[$loc]?)))
