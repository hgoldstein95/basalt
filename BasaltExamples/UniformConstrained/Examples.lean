/-
Copyright (c) 2026 Harrison Goldstein & Ernest Ng. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Ernest Ng
-/
module

public import BasaltExamples.UniformConstrained.Space

/-!
# The lambda-term example (Section 3.2)

The paper's `spNat` and `spTerm`, as families of finite unfoldings (`sized_spNat_of_le`,
`sized_spTerm_of_le`: the values of size `k` are fixed from the `k`-th unfolding on), and the numbers
its Section 3.2 walk-through computes from them.
-/

@[expose] public section

namespace UniformConstrained.Examples

open scoped Space

/-- The paper's `data Term = Ap (Term, Term) | Lam Term | Var Nat`: lambda terms with de Bruijn
indices. Lean's `Nat` stands in for the paper's `data Nat = Zr | Sc Nat`. -/
inductive Term where
  | Ap : Term × Term → Term
  | Lam : Term → Term
  | Var : Nat → Term

/-- The `n`-th unfolding of the paper's `spNat = Pay (Pure Zr :+: (Sc :$: spNat))`. -/
def spNat : Nat → Space Nat
  | 0 => .empty
  | n + 1 => .pay (.pure 0 :+: (Nat.succ :$: spNat n))

/-- The `n`-th unfolding of the paper's `spTerm = Pay (spAp :+: spLam :+: spVar)`, with `spAp`,
`spLam` and `spVar` (below) inlined so that the recursion is structural. -/
def spTerm : Nat → Space Term
  | 0 => .empty
  | n + 1 => .pay ((Term.Ap :$: (spTerm n :*: spTerm n)) :+: (Term.Lam :$: spTerm n) :+:
      (Term.Var :$: spNat n))

/-- The paper's `spAp = Ap :$: (spTerm :*: spTerm)`, inside the `(n + 1)`-th unfolding. -/
def spAp (n : Nat) : Space Term := Term.Ap :$: (spTerm n :*: spTerm n)

/-- The paper's `spLam = Lam :$: spTerm`. -/
def spLam (n : Nat) : Space Term := Term.Lam :$: spTerm n

/-- The paper's `spVar = Var :$: spNat`. -/
def spVar (n : Nat) : Space Term := Term.Var :$: spNat n

theorem spTerm_succ (n : Nat) : spTerm (n + 1) = .pay (spAp n :+: spLam n :+: spVar n) := rfl

/-! ## The `k`-sized values are fixed by the `k`-th unfolding -/

/-- `sizedProd` reads `fa` and `fb` only below the size it splits. -/
theorem sizedProd_congr {α β : Type} {fa fa' : Nat → FinSet α} {fb fb' : Nat → FinSet β} :
    ∀ (n k₁ : Nat), (∀ j < k₁ + n, fa j = fa' j) → (∀ j < n, fb j = fb' j) →
      Space.sizedProd fa fb k₁ n = Space.sizedProd fa' fb' k₁ n := by
  intro n
  induction n with
  | zero => intros; rfl
  | succ n ih =>
    intro k₁ ha hb
    simp only [Space.sizedProd]
    rw [ha k₁ (by omega), hb n (by omega),
      ih (k₁ + 1) (fun j hj => ha j (by omega)) (fun j hj => hb j (by omega))]

theorem sized_spNat_eq : ∀ (k n m : Nat), k ≤ n → k ≤ m →
    Space.sized (spNat n) k = Space.sized (spNat m) k := by
  intro k
  induction k with
  | zero => intro n m _ _; cases n <;> cases m <;> rfl
  | succ k ih =>
    intro n m hn hm
    obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    simp only [spNat, Space.sized_pay_succ, Space.sized_union, Space.sized_fmap,
      ih n m (by omega) (by omega)]

/-- **The values of size `k` of `spNat` are those of its `k`-th unfolding.** -/
theorem sized_spNat_of_le {k n : Nat} (h : k ≤ n) :
    Space.sized (spNat n) k = Space.sized (spNat k) k :=
  sized_spNat_eq k n k h le_rfl

theorem sized_spTerm_eq : ∀ (k n m : Nat), k ≤ n → k ≤ m →
    Space.sized (spTerm n) k = Space.sized (spTerm m) k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro n m hn hm
  cases k with
  | zero => cases n <;> cases m <;> rfl
  | succ k =>
    obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    simp only [spTerm, Space.sized_pay_succ, Space.sized_union,
      Space.sized_fmap, Space.sized_prod, ih k (by omega) n m (by omega) (by omega),
      sized_spNat_eq k n m (by omega) (by omega)]
    rw [sizedProd_congr (k + 1) 0 (fun j hj => ih j (by omega) n m (by omega) (by omega))
      (fun j hj => ih j (by omega) n m (by omega) (by omega))]

/-- **The values of size `k` of `spTerm` are those of its `k`-th unfolding.** -/
theorem sized_spTerm_of_le {k n : Nat} (h : k ≤ n) :
    Space.sized (spTerm n) k = Space.sized (spTerm k) k :=
  sized_spTerm_eq k n k h le_rfl

/-! ## The numbers of Section 3.2 -/

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

end UniformConstrained.Examples
