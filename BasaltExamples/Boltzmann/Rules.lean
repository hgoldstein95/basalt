/-
Copyright (c) 2026 Ernest Ng. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Ernest Ng
-/
module

public import Basalt
public import BasaltExamples.Boltzmann

/-!
# Boltzmann Samplers' Construction Rules

The rules of Duchon, Flajolet, Louchard and Schaeffer (2004, §3, Table 3) that assemble a Boltzmann
sampler from its parts — union, product, sequence — each proved to give every object `γ` the mass
`x ^ |γ| / C(x)`, and the retry loop of their rejection samplers (§6.1, §7) with its law and its
geometric number of trials; and Example 2's critical sampler for unbalanced 2–3 trees.
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

/-- **The probability of the second branch is `B(x) / C(x)`.** The paper prints
`ℙ_{C,x}(γ ∈ B) = A(x) / C(x)` (p. 585), a typo: the two differ whenever `A(x) ≠ B(x)`. -/
theorem prob_union_inr (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {ga : SPMF α} {gb : SPMF β}
    {A B : ℝ≥0∞} (hA : A ≠ ⊤) (hB : B ≠ ⊤) (hAB : A + B ≠ 0) (hpA : pr p = A / (A + B))
    (hgb : gb.mass = 1) :
    prob (union p ga gb : SPMF (α ⊕ β)) (Set.range Sum.inr) = B / (A + B) := by
  classical
  rw [prob_eq_tsum_ite, Summable.tsum_sum ENNReal.summable ENNReal.summable]
  simp only [Set.mem_range, reduceCtorEq, exists_false, ↓reduceIte, tsum_zero, Sum.inr.injEq,
    exists_eq, zero_add]
  simp_rw [union_inr hp0 hp1]
  rw [ENNReal.tsum_mul_left, ← mass, hgb, mul_one, hpA, union_shares hA hB hAB]

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

section retry

variable {α : Type}

/-- The loop under every rejection sampler of §6.1 and §7: draw from `h` until it does not fail. -/
def retry [Gen G] (h : G (Option α)) : G α := do
  match ← h with
  | some a => return a
  | none => retry h
partial_fixpoint

/-- One round of `retry`, with `z` for the retry. -/
theorem retry_round (h : SPMF (Option α)) (z : SPMF α) (a : α) :
    (h >>= fun o => match o with | some a => Pure.pure a | none => z) a
      = h (some a) + h none * z a := by
  rw [bind_apply, tsum_option, add_comm, tsum_eq_single a fun b hb => by simp [Ne.symm hb]]
  simp

/-- **The law of a retry loop**, for every `h`: the value of a round that succeeds, renormalized
by the rounds that fail. -/
theorem retry_apply (h : SPMF (Option α)) (a : α) :
    (retry h : SPMF α) a = h (some a) / (1 - h none) := by
  refine rejection_loop_apply (A := fun b => h (some b)) (R := h none) (fun b => ?_) (fun b => ?_)
    (fun c hc => ?_) a
  · calc h (some b) + h none ≤ ∑' o, h o := by
          rw [tsum_option, add_comm]; gcongr; exact ENNReal.le_tsum (f := fun a => h (some a)) b
      _ ≤ 1 := mass_le_one h
  · conv_lhs => rw [retry]
    exact retry_round h _ b
  · refine retry.fixpoint_induct (G := SPMF) h _ (admissible_apply_le c) fun z hz b => ?_
    rw [retry_round]
    exact le_trans (by gcongr; exact hz b) (hc b)

/-- **Anticipated rejection is rejection.** A sampler `h` that gives up early, but gives each object
it keeps the mass `g` gives it, and keeps exactly those satisfying `P`, retried, is `suchThat g P`
whenever `h` and `g` both terminate. -/
theorem retry_eq_suchThat {h : SPMF (Option α)} {g : SPMF α} {P : α → Bool}
    (hh : ∀ a, h (some a) = if P a then g a else 0) (hm : h.mass = 1) (hg : g.mass = 1) :
    (retry h : SPMF α) = suchThat g P := by
  classical
  have hsum : h none + prob g {a | P a = true} = 1 := by
    rw [← hm, mass, tsum_option, prob_eq_tsum_ite]
    congr 1
    exact tsum_congr fun a => by rw [hh]; rfl
  have hD : 1 - h none = prob g {a | P a = true} :=
    by rw [← hsum, ENNReal.add_sub_cancel_left (apply_ne_top _ _)]
  ext a
  rw [retry_apply, suchThat_apply_of_mass _ _ hg, hD, hh]
  split <;> simp

/-- `retry`, counting its rounds. -/
def retryCount [Gen G] (h : G (Option α)) : G (α × Nat) := do
  match ← h with
  | some a => return (a, 1)
  | none => do
    let r ← retryCount h
    return (r.1, r.2 + 1)
partial_fixpoint

private theorem shift_injective : (fun r : α × Nat => (r.1, r.2 + 1)).Injective := fun r s h => by
  simp only [Prod.mk.injEq, Nat.add_right_cancel_iff] at h; exact Prod.ext h.1 h.2

/-- One round of `retryCount`, with `z` for the retry. -/
theorem retryCount_round (h : SPMF (Option α)) (z : SPMF (α × Nat)) (a : α) (n : Nat) :
    (h >>= fun o => match o with
      | some a => Pure.pure (a, 1)
      | none => z >>= fun r => Pure.pure (r.1, r.2 + 1)) (a, n + 1)
      = (if n = 0 then h (some a) else 0) + h none * z (a, n) := by
  rw [bind_apply, tsum_option, add_comm]
  congr 1
  · rw [tsum_eq_single a fun b hb => by simp [Ne.symm hb]]
    by_cases hn : n = 0 <;> simp [hn]
  · exact congrArg _ (bind_pure_apply_of_injective shift_injective z (a, n))

theorem retryCount_zero (h : SPMF (Option α)) (a : α) :
    (retryCount h : SPMF (α × Nat)) (a, 0) = 0 := by
  rw [retryCount, bind_apply, tsum_option,
    bind_pure_apply_of_ne (f := fun r : α × Nat => (r.1, r.2 + 1)) _ fun r h => by
      simp only [Prod.mk.injEq, Nat.add_eq_zero_iff, one_ne_zero, and_false] at h]
  simp

/-- **The number of trials is geometric** (§6.1): success on round `n + 1` means `n` failures. -/
theorem retryCount_apply (h : SPMF (Option α)) (a : α) (n : Nat) :
    (retryCount h : SPMF (α × Nat)) (a, n + 1) = h none ^ n * h (some a) := by
  induction n with
  | zero =>
    conv_lhs => rw [retryCount]
    rw [retryCount_round, retryCount_zero]
    simp
  | succ n ih =>
    conv_lhs => rw [retryCount]
    rw [retryCount_round, ih]
    simp only [Nat.add_one_ne_zero, ↓reduceIte, zero_add]
    ring

theorem tsum_succ_mul_pow (r : ℝ≥0∞) :
    ∑' n : ℕ, ((n + 1 : ℕ) : ℝ≥0∞) * r ^ n = ((1 - r)⁻¹) ^ 2 := by
  rw [sq, ← ENNReal.tsum_geometric, ← ENNReal.tsum_mul_right]
  simp_rw [← ENNReal.tsum_mul_left, ← pow_add]
  rw [← ENNReal.tsum_prod, ← (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd).tsum_eq,
    ENNReal.tsum_sigma']
  refine tsum_congr fun n => ?_
  rw [tsum_fintype]
  simp only [Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd, Equiv.coe_fn_mk]
  rw [Finset.sum_coe_sort (Finset.HasAntidiagonal.antidiagonal n)
    (fun x : ℕ × ℕ => r ^ (x.1 + x.2))]
  rw [Finset.sum_congr rfl fun p hp => by rw [Finset.HasAntidiagonal.mem_antidiagonal.1 hp]]
  simp

/-- **The expected number of trials** is the inverse of the probability that a round succeeds. -/
theorem expect_retryCount_trials (h : SPMF (Option α)) (hm : h.mass = 1) (hR : h none < 1) :
    expect (retryCount h : SPMF (α × Nat)) (fun r => (r.2 : ℝ≥0∞)) = (1 - h none)⁻¹ := by
  have hq : ∑' a, h (some a) = 1 - h none := by
    rw [← hm, mass, tsum_option, ENNReal.add_sub_cancel_left (apply_ne_top _ _)]
  have hD0 : 1 - h none ≠ 0 := (tsub_pos_of_lt hR).ne'
  have hDtop : 1 - h none ≠ ⊤ := ENNReal.sub_ne_top ENNReal.one_ne_top
  unfold expect
  rw [ENNReal.tsum_prod' (f := fun r => (retryCount h : SPMF (α × Nat)) r * (r.2 : ℝ≥0∞))]
  have hin : ∀ a, ∑' n : ℕ, (retryCount h : SPMF (α × Nat)) (a, n) * (n : ℝ≥0∞)
      = h (some a) * ((1 - h none)⁻¹) ^ 2 := fun a => by
    have hs := retryCount_apply h a
    generalize (retryCount h : SPMF (α × Nat)) = μ at hs
    rw [tsum_eq_zero_add' ENNReal.summable, ← tsum_succ_mul_pow, ← ENNReal.tsum_mul_left]
    simp only [CharP.cast_eq_zero, mul_zero, zero_add, hs]
    exact tsum_congr fun n => by ring
  rw [tsum_congr hin, ENNReal.tsum_mul_right, hq, sq, ← mul_assoc,
    ENNReal.mul_inv_cancel hD0 hDtop, one_mul]

end retry

section twoThree

/-! ## Unbalanced 2–3 trees (Example 2)

`U = Z + U² + U³`, only leaves counting, sampled at the critical `ρ_U = 5/27`, where `U(ρ) = 1/3`
and the branching probabilities are `5/9`, `1/3`, `1/9`. -/

/-- Unbalanced 2–3 trees. -/
inductive Tree23 where
  | leaf
  | two (a b : Tree23)
  | three (a b c : Tree23)

/-- The size: leaves only. -/
def Tree23.size : Tree23 → Nat
  | .leaf => 1
  | .two a b => a.size + b.size
  | .three a b c => a.size + b.size + c.size

def Tree23.twos : Tree23 → Nat
  | .leaf => 0
  | .two a b => a.twos + b.twos + 1
  | .three a b c => a.twos + b.twos + c.twos

def Tree23.threes : Tree23 → Nat
  | .leaf => 0
  | .two a b => a.threes + b.threes
  | .three a b c => a.threes + b.threes + c.threes + 1

theorem Tree23.size_eq (t : Tree23) : t.size = 1 + t.twos + 2 * t.threes := by
  induction t <;> simp only [Tree23.size, Tree23.twos, Tree23.threes, *] <;> omega

/-- The critical sampler: branching probabilities `5/9`, `3/9`, `1/9`. -/
def gen23 [Gen G] : G Tree23 :=
  frequency! [
    (5, fun _ => pure .leaf),
    (3, fun _ => do return .two (← gen23) (← gen23)),
    (1, fun _ => do return .three (← gen23) (← gen23) (← gen23))] (by simp)
partial_fixpoint

theorem gen23_apply (t : Tree23) :
    (gen23 : SPMF Tree23) t = (5 / 9) ^ t.size * (3 / 9) ^ t.twos * (1 / 9) ^ t.threes := by
  induction t with
  | leaf =>
    rw [gen23, frequencyWith_eq, frequency_apply]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, pure_apply, ↓reduceIte]
    rw [bind_bind_pure_apply_of_ne (f := Tree23.two) _ _ fun _ _ => Tree23.noConfusion,
      bind3_pure_apply_of_ne (f := Tree23.three) _ _ _ fun _ _ _ => Tree23.noConfusion]
    simp only [Tree23.size, Tree23.twos, Tree23.threes]
    norm_num [ENNReal.div_eq_inv_mul]
  | two a b iha ihb =>
    rw [gen23, frequencyWith_eq, frequency_apply]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, pure_apply, reduceCtorEq,
      ↓reduceIte]
    rw [bind_bind_pure_apply_of_injective (f := Tree23.two) fun _ _ _ _ h => Tree23.two.inj h,
      bind3_pure_apply_of_ne (f := Tree23.three) _ _ _ fun _ _ _ => Tree23.noConfusion, iha, ihb]
    simp only [Tree23.size, Tree23.twos, Tree23.threes, pow_add, pow_one]
    norm_num [ENNReal.div_eq_inv_mul]
    ring
  | three a b c iha ihb ihc =>
    rw [gen23, frequencyWith_eq, frequency_apply]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, pure_apply, reduceCtorEq,
      ↓reduceIte]
    rw [bind_bind_pure_apply_of_ne (f := Tree23.two) _ _ fun _ _ => Tree23.noConfusion,
      bind3_pure_apply_of_injective (f := Tree23.three) fun _ _ _ _ _ _ h => Tree23.three.inj h,
      iha, ihb, ihc]
    simp only [Tree23.size, Tree23.twos, Tree23.threes, pow_add, pow_one]
    norm_num [ENNReal.div_eq_inv_mul]
    ring

/-- **The Boltzmann form at `ρ_U = 5/27`**: a tree with `n` leaves has mass `ρ ^ n / U(ρ)`. -/
theorem gen23_boltzmann : IsBoltzmann (gen23 : SPMF Tree23) Tree23.size (5 / 27) (1 / 3) := by
  intro t
  have c1 : (3 / 9 : ℝ≥0∞) = 3⁻¹ := by
    rw [← ENNReal.toReal_eq_toReal_iff' (by simp [ENNReal.div_eq_top]) (by simp)]; simp; norm_num
  have c2 : (1 / 9 : ℝ≥0∞) = 3⁻¹ ^ 2 := by
    rw [← ENNReal.toReal_eq_toReal_iff' (by simp) (by simp)]; simp; norm_num
  have c3 : (5 / 27 : ℝ≥0∞) = 5 / 9 * 3⁻¹ := by
    rw [← ENNReal.toReal_eq_toReal_iff' (by simp [ENNReal.div_eq_top])
      (by simp [ENNReal.div_eq_top, ENNReal.mul_eq_top])]; simp; norm_num
  have h3 : (3⁻¹ : ℝ≥0∞) * 3⁻¹⁻¹ = 1 := ENNReal.mul_inv_cancel (by simp) (by simp)
  rw [gen23_apply, Tree23.size_eq, c1, c2, c3, one_div, div_eq_mul_inv (b := (3 : ℝ≥0∞)⁻¹)]
  generalize (5 / 9 : ℝ≥0∞) = x
  generalize (3⁻¹ : ℝ≥0∞) = y at h3 ⊢
  calc x ^ (1 + t.twos + 2 * t.threes) * y ^ t.twos * (y ^ 2) ^ t.threes
      = x ^ (1 + t.twos + 2 * t.threes) * y ^ t.twos * (y ^ 2) ^ t.threes * (y * y⁻¹) := by
        rw [h3, mul_one]
    _ = _ := by rw [mul_pow, pow_add, pow_add, pow_mul]; ring

/-- "Branching probabilities for a nullary, binary, and ternary node are found to be,
respectively, `5/9`, `1/3`, `1/9`": mean offspring `2/3 + 1/3 = 1`, so the sampler is critical and
terminates almost surely. -/
theorem gen23_terminates : IsAlmostSurelyTerminating (gen23 : SPMF Tree23) := by
  mass_fixpoint using SPMF.LfpIsOne.cubic (a := 5 / 9) (b := 0) (d := 3 / 9) (e := 1 / 9)
  norm_num [sq, ENNReal.div_eq_inv_mul, mul_add, pow_succ]
  exact le_of_eq (by ring)

end twoThree

end Boltzmann
