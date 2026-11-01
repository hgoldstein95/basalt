/-
Copyright (c) 2026 Ernest Ng. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Ernest Ng
-/
module

public import Basalt
public import BasaltExamples.Boltzmann.DuchonEtAlBoltzmann

/-!
# Boltzmann Samplers' Construction Rules

The rules of Duchon, Flajolet, Louchard and Schaeffer (2004, §3, Table 3) that assemble a Boltzmann
sampler from its parts — union, product, sequence — each proved to give every object `γ` the mass
`x ^ |γ| / C(x)`, and the law of the retry loop under their ceiled rejection sampler (§7).
-/

@[expose] public section

open RandomChoice SPMF
open scoped ENNReal

namespace Boltzmann

section model

variable {α β : Type}

/-- **The ordinary Boltzmann model** of parameter `x` (§2): each object `γ` of a class with size
function `size` and generating function value `C = C(x)` has mass `x ^ |γ| / C`. -/
def IsBoltzmann (μ : SPMF α) (size : α → ℕ) (x C : ℝ≥0∞) : Prop :=
  ∀ a, μ a = x ^ size a / C

/-- Uniform within each size, the model's point. -/
theorem IsBoltzmann.uniform {μ : SPMF α} {size : α → ℕ} {x C : ℝ≥0∞} (h : IsBoltzmann μ size x C)
    {a b : α} (hab : size a = size b) : μ a = μ b := by
  rw [h, h, hab]

/-- (2.3): the probability of a size is the number of objects of that size times `x ^ n / C`. -/
theorem IsBoltzmann.prob_size {μ : SPMF α} {size : α → ℕ} {x C : ℝ≥0∞}
    (h : IsBoltzmann μ size x C) (n : ℕ) :
    prob μ {a | size a = n} = (∑' a, if size a = n then 1 else 0) * (x ^ n / C) := by
  classical
  rw [prob_eq_tsum_ite, ← ENNReal.tsum_mul_right]
  refine tsum_congr fun a => ?_
  by_cases ha : size a = n <;> simp [ha, h a]

/-- The model is a distribution exactly when `C` is the generating function's value. -/
theorem IsBoltzmann.mass_eq {μ : SPMF α} {size : α → ℕ} {x C : ℝ≥0∞}
    (h : IsBoltzmann μ size x C) : μ.mass = (∑' a, x ^ size a) / C := by
  rw [mass]
  rw [tsum_congr fun a => h a]
  simp_rw [div_eq_mul_inv]
  rw [ENNReal.tsum_mul_right]

end model

section rules

variable {α β : Type}

/-- **Singletons**: a class of one object of size `n` is drawn deterministically. -/
theorem isBoltzmann_pure {x : ℝ≥0∞} (hx0 : x ≠ 0) (hxtop : x ≠ ⊤) (n : ℕ) :
    IsBoltzmann (Pure.pure () : SPMF Unit) (fun _ => n) x (x ^ n) := fun _ => by
  simp only [pure_apply, ↓reduceIte]
  rw [ENNReal.div_self (pow_ne_zero _ hx0) (ENNReal.pow_ne_top hxtop)]

/-- `C = A + B`: a Bernoulli switch of parameter `A(x) / C(x)` between the two samplers (3.2). -/
def union [Gen G] (p : Rat) (ga : G α) (gb : G β) : G (α ⊕ β) := do
  if ← coin p then return .inl (← ga) else return .inr (← gb)

theorem union_inl (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (ga : SPMF α) (gb : SPMF β) (a : α) :
    (union p ga gb : SPMF (α ⊕ β)) (.inl a) = pr p * ga a := by
  rw [union, bind_apply, tsum_bool]
  simp only [Bool.false_eq_true, ↓reduceIte, coin_false hp0 hp1, coin_true hp0 hp1]
  rw [bind_pure_apply_of_ne gb (fun b => Sum.inr_ne_inl), bind_pure_apply_of_injective
    Sum.inl_injective, mul_zero, zero_add]

theorem union_inr (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (ga : SPMF α) (gb : SPMF β) (b : β) :
    (union p ga gb : SPMF (α ⊕ β)) (.inr b) = (1 - pr p) * gb b := by
  rw [union, bind_apply, tsum_bool]
  simp only [Bool.false_eq_true, ↓reduceIte, coin_false hp0 hp1, coin_true hp0 hp1]
  rw [bind_pure_apply_of_ne ga (fun a => Sum.inl_ne_inr), bind_pure_apply_of_injective
    Sum.inr_injective, mul_zero, add_zero]

/-- The two branches' shares of `C = A + B`. -/
private theorem union_shares {A B : ℝ≥0∞} (hA : A ≠ ⊤) (hB : B ≠ ⊤) (hAB : A + B ≠ 0) :
    1 - A / (A + B) = B / (A + B) := by
  have htop : A + B ≠ ⊤ := ENNReal.add_ne_top.2 ⟨hA, hB⟩
  refine ENNReal.sub_eq_of_eq_add (ENNReal.div_ne_top hA hAB) ?_
  rw [ENNReal.div_add_div_same, add_comm B, ENNReal.div_self hAB htop]

/-- **Union**: switching with probability `A(x) / (A(x) + B(x))` gives the model of `A + B`. -/
theorem isBoltzmann_union (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {ga : SPMF α} {gb : SPMF β}
    {sa : α → ℕ} {sb : β → ℕ} {x A B : ℝ≥0∞} (ha : IsBoltzmann ga sa x A)
    (hb : IsBoltzmann gb sb x B) (hA0 : A ≠ 0) (hA : A ≠ ⊤) (hB0 : B ≠ 0) (hB : B ≠ ⊤)
    (hpA : pr p = A / (A + B)) :
    IsBoltzmann (union p ga gb : SPMF (α ⊕ β)) (Sum.elim sa sb) x (A + B) := by
  have hAB : A + B ≠ 0 := by simp [hA0]
  rintro (a | b)
  · rw [union_inl hp0 hp1, hpA, ha, Sum.elim_inl, mul_comm, ENNReal.div_mul_div_cancel hA0 hA]
  · rw [union_inr hp0 hp1, hpA, union_shares hA hB hAB, hb, Sum.elim_inr, mul_comm,
      ENNReal.div_mul_div_cancel hB0 hB]

/-- `C = A × B`: a pair of independent draws (3.5). -/
def product [Gen G] (ga : G α) (gb : G β) : G (α × β) := do
  return (← ga, ← gb)

/-- **Product**: independent draws give the model of `A × B`, sizes adding. -/
theorem isBoltzmann_product {ga : SPMF α} {gb : SPMF β} {sa : α → ℕ} {sb : β → ℕ}
    {x A B : ℝ≥0∞} (ha : IsBoltzmann ga sa x A) (hb : IsBoltzmann gb sb x B) (hA : A ≠ ⊤)
    (hB : B ≠ ⊤) :
    IsBoltzmann (product ga gb : SPMF (α × β)) (fun c => sa c.1 + sb c.2) x (A * B) := by
  rintro ⟨a, b⟩
  rw [product, bind_bind_pure_apply_of_injective (f := Prod.mk) (fun _ _ _ _ h => Prod.mk.inj h),
    ha, hb, div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, ENNReal.mul_inv (.inr hB) (.inl hA),
    pow_add]
  ring

/-- `C = S(A)`: the recursive sampler (§3, design (i)), which adds a component with probability
`A(x)`. -/
def seq [Gen G] (q : Rat) (ga : G α) : G (List α) := do
  if ← coin q then return (← ga) :: (← seq q ga) else return []
partial_fixpoint

theorem seq_apply (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (ga : SPMF α) (l : List α) :
    (seq q ga : SPMF (List α)) l = pr q ^ l.length * (l.map ga).prod * (1 - pr q) := by
  induction l with
  | nil =>
    rw [seq, bind_apply, tsum_bool]
    simp only [Bool.false_eq_true, ↓reduceIte, coin_false hq0 hq1, coin_true hq0 hq1]
    rw [bind_bind_pure_apply_of_ne (f := List.cons) _ _ fun _ _ => List.cons_ne_nil _ _]
    simp
  | cons a l ih =>
    rw [seq, bind_apply, tsum_bool]
    simp only [Bool.false_eq_true, ↓reduceIte, coin_false hq0 hq1, coin_true hq0 hq1]
    rw [bind_bind_pure_apply_of_injective (f := List.cons) fun _ _ _ _ h => List.cons.inj h, ih]
    simp only [pure_apply, reduceCtorEq, ↓reduceIte, mul_zero, zero_add, List.length_cons,
      List.map_cons, List.prod_cons]
    ring

/-- **Sequence**: continuing with probability `A(x)` gives the model of `S(A)`, `C = 1 / (1 - A)`.
The number of components is geometric, as the paper says; nothing about the recursion's least fixed
point is needed for the point masses. -/
theorem isBoltzmann_seq (hq0 : 0 ≤ q) (hq1 : q ≤ 1) {ga : SPMF α} {sa : α → ℕ} {x A : ℝ≥0∞}
    (ha : IsBoltzmann ga sa x A) (hA0 : A ≠ 0) (hA : A ≠ ⊤) (hqA : pr q = A) :
    IsBoltzmann (seq q ga : SPMF (List α)) (fun l => (l.map sa).sum) x (1 - A)⁻¹ := by
  intro l
  rw [seq_apply hq0 hq1, hqA, div_eq_mul_inv, inv_inv]
  congr 1
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.length_cons, List.map_cons, List.prod_cons, List.sum_cons, pow_succ, pow_add,
      ← ih, ha a, div_eq_mul_inv]
    calc A ^ l.length * A * (x ^ sa a * A⁻¹ * (List.map ga l).prod)
        = x ^ sa a * (A * A⁻¹) * (A ^ l.length * (List.map ga l).prod) := by ring
      _ = _ := by rw [ENNReal.mul_inv_cancel hA0 hA, mul_one]

theorem seq_terminates (hq0 : 0 ≤ q) (hq1 : q < 1) {ga : SPMF α}
    (hg : IsAlmostSurelyTerminating ga) : IsAlmostSurelyTerminating (seq q ga : SPMF (List α)) := by
  have hx1 : pr q < 1 := by
    rw [pr_eq_ofReal hq0]; exact ENNReal.ofReal_lt_one.2 (by exact_mod_cast hq1)
  mass_fixpoint [hg.obs] using SPMF.LfpIsOne.affine (m := pr q) hx1
  coin_goals q hq0 hq1.le
  rw [mul_one, add_comm]

end rules

section reject

variable {α : Type}

/-- Retrying a round that may fail (`none`) until it succeeds, as rejection sampling: its law is the
round's, renormalized by the rounds that fail. -/
theorem getD_suchThat_isSome_apply (h : SPMF (Option α)) (d a : α) :
    ((fun o => o.getD d) <$> suchThat h Option.isSome : SPMF α) a = h (some a) / (1 - h none) := by
  classical
  have hrej : prob h {o | o.isSome = false} = h none := by
    rw [show {o : Option α | o.isSome = false} = {none} by ext o; cases o <;> simp, prob_singleton]
  rw [map_eq_pure_bind, bind_apply, tsum_option, suchThat_apply, hrej,
    tsum_eq_single a fun b hb => by simp [Ne.symm hb]]
  simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, zero_mul, zero_add,
    Option.getD_some, pure_apply, mul_one]
  rw [suchThat_apply, hrej]
  simp

end reject

end Boltzmann
