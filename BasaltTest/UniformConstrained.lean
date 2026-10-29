/-
Copyright (c) 2026 Harrison Goldstein & Ernest Ng. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Ernest Ng
-/
module

public import BasaltExamples.UniformConstrained.Examples
public import BasaltExamples.UniformConstrained.Uniformity

/-!
# The numbers of Claessen–Duregård–Pałka, Sections 3.2 and 4.1

The cardinalities and indices the paper's walk-throughs compute, checked against the spaces of
`BasaltExamples.UniformConstrained`.
-/

@[expose] public section

namespace UniformConstrained

open scoped Space

/-! ## Section 3.2 -/

namespace Examples


/-- The number of terms of each size `1 … 12`. -/
theorem card_sized_spTerm :
    ((List.range' 1 12).map fun k => (Space.sized (spTerm k) k).card)
      = [0, 1, 2, 3, 5, 10, 21, 44, 94, 207, 465, 1056] := by
  decide

/-- "The number of lambda terms of size 11 can be computed from the definition of the space …, and
for our space it is `c = 465`." -/
theorem card_sized_spTerm_11 {n : Nat} (h : 11 ≤ n) : (Space.sized (spTerm n) 11).card = 465 := by
  rw [sized_spTerm_of_le h]
  decide

/-- "For size 11, the cardinalities are 257, 207 and 1 respectively": the split of `spTerm` at size
11 into `Pay spAp`, `Pay spLam` and `Pay spVar`. -/
theorem split_spTerm_11 :
    (Space.sized (spAp 10) 10).card = 257 ∧ (Space.sized (spLam 10) 10).card = 207 ∧
      (Space.sized (spVar 10) 10).card = 1 := by
  decide

/-- The split one level down, at the residual index 150: 112, 94 and 1, so `150 ∈ [112, 206)`
selects `spLam` again. -/
theorem split_spTerm_10 :
    (Space.sized (spAp 9) 9).card = 112 ∧ (Space.sized (spLam 9) 9).card = 94 ∧
      (Space.sized (spVar 9) 9).card = 1 := by
  decide

/-- "Since `257 ⩽ 407 ⩽ 257 + 207`, we choose the second space, and obtain a residual index of
`407 − 257 = 150`", and then "Lambda is chosen again": index 407 at size 11 is a term with two head
lambdas, namely index `150 - 112 = 38` of the terms of size 9 under `Lam ∘ Lam`. The paper's upper
bound should be strict: index `257 + 207 = 464` is the one `spVar` term. -/
theorem indexSet_spTerm_407 :
    (Space.sized (spTerm 11) 11).indexSet 407
      = ((Space.sized (spTerm 9) 9).indexSet 38).map (fun t => Term.Lam (Term.Lam t)) := by
  rfl

/-- The paper's residual space after discarding the terms with two head lambdas:
`Pay (spAp :+: spVar) :+: Pay 2 (Lam :$: (spAp :+: spVar))`, at unfolding `n`. -/
def residual (n : Nat) : Space Term :=
  .pay (spAp n :+: spVar n) :+: .pay (.pay (Term.Lam :$: (spAp n :+: spVar n)))

/-- "The cardinality of this new space is 371": the 465 terms of size 11 less the 94 with two head
lambdas, which are `Lam (Lam t)` for the 94 terms `t` of size 9. -/
theorem card_sized_residual_11 :
    (Space.sized (residual 11) 11).card = 371 ∧
      (Space.sized (spTerm 11) 11).card - (Space.sized (spTerm 9) 9).card = 371 := by
  decide

end Examples

/-! ## Section 4.1 -/

/-- The two orders index `spacePairB` at size 3 as in the paper's table:
`(F,F) (F,T) (T,F) (T,T)` forcing the first component first, `(F,F) (T,F) (F,T) (T,T)` forcing the
second first. -/
theorem index_spacePairB :
    ((List.range 4).map fun i =>
        ((sizedP (orderOracle true) 17 nonDetB spacePairB 3).bind (·.indexSet i)).bind
          Sum.getLeft?)
      = [some (false, false), some (false, true), some (true, false), some (true, true)] ∧
    ((List.range 4).map fun i =>
        ((sizedP (orderOracle false) 17 nonDetB spacePairB 3).bind (·.indexSet i)).bind
          Sum.getLeft?)
      = [some (false, false), some (true, false), some (false, true), some (true, true)] := by
  decide

end UniformConstrained
