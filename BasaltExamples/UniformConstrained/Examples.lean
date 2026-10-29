/-
Copyright (c) 2026 Harrison Goldstein & Ernest Ng. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Ernest Ng
-/
module

public import BasaltExamples.UniformConstrained.Space

/-!
# The lambda-term spaces of Section 3.2

The paper's recursive spaces `spNat` and `spTerm` are cyclic Haskell values; here they are families
of finite unfoldings, and `sized_spNat_of_le` / `sized_spTerm_of_le` show that the values of size `k`
are fixed from the `k`-th unfolding on, so nothing is lost.
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

/-- **The values of size `k` of `spNat` are those of its `k`-th unfolding.** This is the paper's
rule that "all recursion is guarded by at least one `Pay`": `sized s k` looks under at most `k`
nested `Pay`s. -/
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

end UniformConstrained.Examples
