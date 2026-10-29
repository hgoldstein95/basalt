/-
Copyright (c) 2026 Ernest Ng. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Ernest Ng
-/
module

import Mathlib.Tactic.Basify
public import Basalt
public import BasaltExamples.Boltzmann.CanouDarrasse

/-!
# A Boltzmann Sampler for λ-Terms

The Boltzmann sampler for de Bruijn λ-terms of Bendkowski, Grygiel and Tarau, "Random generation of
closed simply typed λ-terms" (TLP 2018, §§2.1, 3.1, 4), with its branching probabilities as
parameters, and its anticipated rejection of open terms (`pickIndex`'s list of binders): retried, it
is rejection sampling of closed terms, so uniform among closed terms of a size. Typability's
interleaved unification is not modelled; `retry_eq_suchThat` is the statement it would need.
-/

@[expose] public section

open RandomChoice SPMF
open scoped ENNReal

namespace Boltzmann.Lambda

/-- De Bruijn terms, `L = D | λL | L L` with `D = 0 | S(D)` (§3.1). -/
inductive Term where
  | var (n : Nat)
  | lam (t : Term)
  | app (t u : Term)
deriving DecidableEq

/-- §2.1's size: each constructor weighs its arity, so the index `sⁿ(0)` weighs `n`, an abstraction
`1`, an application `2`. `ranTypable` reports this plus one ("Size is Size0+1"), the natural size
of Bendkowski et al. (2016). -/
def Term.size : Term → Nat
  | .var n => n
  | .lam t => t.size + 1
  | .app t u => t.size + u.size + 2

def Term.vars : Term → Nat
  | .var _ => 1
  | .lam t => t.vars
  | .app t u => t.vars + u.vars

def Term.succs : Term → Nat
  | .var n => n
  | .lam t => t.succs
  | .app t u => t.succs + u.succs

def Term.lams : Term → Nat
  | .var _ => 0
  | .lam t => t.lams + 1
  | .app t u => t.lams + u.lams

def Term.apps : Term → Nat
  | .var _ => 0
  | .lam t => t.apps
  | .app t u => t.apps + u.apps + 1

theorem Term.vars_eq (t : Term) : t.vars = t.apps + 1 := by
  induction t <;> simp only [Term.vars, Term.apps, *]; omega

theorem Term.size_eq (t : Term) : t.size = t.succs + t.lams + 2 * t.apps := by
  induction t <;> simp only [Term.size, Term.succs, Term.lams, Term.apps, *] <;> omega

/-- Whether every index is bound by one of the `n` enclosing abstractions or one of the term's own. -/
def Term.closedUnder : Nat → Term → Bool
  | n, .var k => decide (k < n)
  | n, .lam t => t.closedUnder (n + 1)
  | n, .app t u => t.closedUnder n && u.closedUnder n

/-- A de Bruijn index: `0` with probability `pz`, else a successor (`pickIndex`'s
`boltzmann_leaf`). -/
def genIdx [Gen G] (pz : Rat) : G Nat := do
  if ← coin pz then return 0 else return (← genIdx pz) + 1
partial_fixpoint

/-- The plain-term sampler (§4.1's `ranTypable` without its constraints): an index, an abstraction,
or an application, with weights `wi`, `wl`, `wa`. -/
def genLam [Gen G] (wi wl wa : Nat) (h : 0 < wi + wl + wa) (pz : Rat) : G Term :=
  frequency! [
    (wi, fun _ => do return .var (← genIdx pz)),
    (wl, fun _ => do return .lam (← genLam wi wl wa h pz)),
    (wa, fun _ => do return .app (← genLam wi wl wa h pz) (← genLam wi wl wa h pz))]
    (by simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; omega)
partial_fixpoint

theorem genIdx_apply (hp0 : 0 ≤ pz) (hp1 : pz ≤ 1) (n : Nat) :
    (genIdx pz : SPMF Nat) n = pr pz * (1 - pr pz) ^ n := by
  induction n with
  | zero =>
    rw [genIdx, bind_apply, tsum_bool]
    simp only [Bool.false_eq_true, ↓reduceIte, coin_false hp0 hp1, coin_true hp0 hp1]
    rw [bind_pure_apply_of_ne _ fun _ => Nat.succ_ne_zero _]
    simp
  | succ n ih =>
    rw [genIdx, bind_apply, tsum_bool]
    simp only [Bool.false_eq_true, ↓reduceIte, coin_false hp0 hp1, coin_true hp0 hp1]
    rw [bind_pure_apply_of_injective (f := (· + 1)) (fun _ _ h => Nat.succ.inj h), ih]
    simp only [pure_apply, Nat.add_one_ne_zero, ↓reduceIte, mul_zero, add_zero, pow_succ]
    ring

theorem genLam_apply (h : 0 < wi + wl + wa) (hp0 : 0 ≤ pz) (hp1 : pz ≤ 1) (t : Term) :
    (genLam wi wl wa h pz : SPMF Term) t
      = (wi / (wi + wl + wa : ℝ≥0∞) * pr pz) ^ t.vars * (1 - pr pz) ^ t.succs
        * (wl / (wi + wl + wa : ℝ≥0∞)) ^ t.lams * (wa / (wi + wl + wa : ℝ≥0∞)) ^ t.apps := by
  induction t with
  | var n =>
    rw [genLam, frequencyWith_eq, frequency_apply]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    rw [bind_pure_apply_of_injective (fun _ _ h => Term.var.inj h), genIdx_apply hp0 hp1,
      bind_pure_apply_of_ne _ fun _ => Term.noConfusion,
      bind_bind_pure_apply_of_ne (f := Term.app) _ _ fun _ _ => Term.noConfusion]
    simp only [Term.vars, Term.succs, Term.lams, Term.apps, ENNReal.div_eq_inv_mul, Nat.cast_add,
      ← add_assoc, mul_zero, add_zero, pow_one, pow_zero, mul_one]
    ring
  | lam t ih =>
    rw [genLam, frequencyWith_eq, frequency_apply]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    rw [bind_pure_apply_of_ne _ fun _ => Term.noConfusion,
      bind_pure_apply_of_injective (fun _ _ h => Term.lam.inj h), ih,
      bind_bind_pure_apply_of_ne (f := Term.app) _ _ fun _ _ => Term.noConfusion]
    simp only [Term.vars, Term.succs, Term.lams, Term.apps, ENNReal.div_eq_inv_mul, Nat.cast_add,
      ← add_assoc, mul_zero, add_zero, zero_add, pow_succ]
    ring
  | app t u iht ihu =>
    rw [genLam, frequencyWith_eq, frequency_apply]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    rw [bind_pure_apply_of_ne _ fun _ => Term.noConfusion,
      bind_pure_apply_of_ne _ fun _ => Term.noConfusion,
      bind_bind_pure_apply_of_injective (f := Term.app) fun _ _ _ _ h => Term.app.inj h, iht, ihu]
    simp only [Term.vars, Term.succs, Term.lams, Term.apps, ENNReal.div_eq_inv_mul, Nat.cast_add,
      ← add_assoc, mul_zero, zero_add, pow_succ, pow_add]
    ring

/-- **The Boltzmann form** (§3.3–3.4): with an abstraction's probability `x`, a successor's `x`, an
index's `D(x) / L(x)` (so an index `0`'s, `D(x) / L(x) · (1 - x)`, is `1 / L(x)`), and an
application's `x² L(x)`, each term gets `x ^ |t| / L(x)`. Only these point relations matter, not
the equation `L = D + x L + x² L²`. -/
theorem genLam_boltzmann {wi wl wa : ℕ} (h : 0 < wi + wl + wa) (hp0 : 0 ≤ pz) (hp1 : pz ≤ 1) {x L : ℝ≥0∞}
    (hL0 : L ≠ 0) (hLtop : L ≠ ⊤) (hi : wi / (wi + wl + wa : ℝ≥0∞) * pr pz = L⁻¹)
    (hz : 1 - pr pz = x) (hl : wl / (wi + wl + wa : ℝ≥0∞) = x)
    (ha : wa / (wi + wl + wa : ℝ≥0∞) = x ^ 2 * L) :
    IsBoltzmann (genLam wi wl wa h pz : SPMF Term) Term.size x L := by
  intro t
  rw [genLam_apply h hp0 hp1, hi, hz, hl, ha, Term.vars_eq, Term.size_eq, div_eq_mul_inv]
  have hLL : L⁻¹ * L = 1 := ENNReal.inv_mul_cancel hL0 hLtop
  calc L⁻¹ ^ (t.apps + 1) * x ^ t.succs * x ^ t.lams * (x ^ 2 * L) ^ t.apps
      = x ^ (t.succs + t.lams + 2 * t.apps) * L⁻¹ * (L⁻¹ * L) ^ t.apps := by ring
    _ = _ := by rw [hLL, one_pow, mul_one]

theorem genIdx_terminates (hp0 : 0 < pz) (hp1 : pz ≤ 1) :
    IsAlmostSurelyTerminating (genIdx pz : SPMF Nat) := by
  have hx : pr pz ≠ 0 := by
    rw [pr_eq_ofReal hp0.le]; exact (ENNReal.ofReal_pos.2 (by exact_mod_cast hp0)).ne'
  mass_fixpoint using SPMF.LfpIsOne.affine (m := 1 - pr pz)
    (ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hx)
  all_goals first
    | exact pz.den_pos
    | exact (coin_num_bounds hp0.le hp1).1
    | exact (coin_num_bounds hp0.le hp1).2
    | rw [pr_compl, show ((pz.num.toNat : ℕ) : ℝ≥0∞) / pz.den = pr pz from rfl,
        ENNReal.sub_sub_cancel ENNReal.one_ne_top (pr_le_one hp0.le hp1), mul_one, add_comm]

/-- The printed sampler of §4.1: `boltzmann_index` `R < 0.35700035696434995`, `boltzmann_lambda`
`R < 0.6525813160382378`, `boltzmann_leaf` `R < 0.7044190409261122`, the decimals read exactly. -/
def paperSampler [Gen G] : G Term :=
  genLam 35700035696434995 29558095907388785 34741868396176220 (by norm_num)
    (7044190409261122 / 10 ^ 16)

/-- **The printed constants are not exactly uniform.** `λλλ.2` and `λλλλλ.0`, both closed and
simply typed of size `5`, differ in probability: uniformity needs a successor's probability,
`1 - 0.7044190409261122`, to equal an abstraction's, `0.6525813160382378 - 0.35700035696434995`, and
the two decimals differ in the 17th digit. Duchon et al. (§5) anticipate this: truncated constants
"must deviate (slightly) from uniformity". -/
theorem paperSampler_not_uniform :
    (paperSampler : SPMF Term) (.lam (.lam (.lam (.var 2))))
      < (paperSampler : SPMF Term) (.lam (.lam (.lam (.lam (.lam (.var 0)))))) := by
  rw [paperSampler, genLam_apply _ (by norm_num) (by norm_num),
    genLam_apply _ (by norm_num) (by norm_num)]
  simp only [Term.vars, Term.succs, Term.lams, Term.apps, pow_one, pow_zero, mul_one]
  rw [show pr (7044190409261122 / 10 ^ 16) = 3522095204630561 / 5000000000000000 by
    rw [pr]; norm_num]
  norm_num
  have hq : (1 - 3522095204630561 / 5000000000000000 : ℝ≥0∞)
      < 29558095907388785 / 100000000000000000 := by
    rw [← ENNReal.toReal_lt_toReal (by finiteness) (by finiteness),
      ENNReal.toReal_sub_of_le (ENNReal.div_le_of_le_mul (by norm_num)) (by simp)]
    simp
    norm_num
  have hA0 : (35700035696434995 / 100000000000000000 * (3522095204630561 / 5000000000000000)
      : ℝ≥0∞) ≠ 0 := by simp
  have hAt : (35700035696434995 / 100000000000000000 * (3522095204630561 / 5000000000000000)
      : ℝ≥0∞) ≠ ⊤ := by finiteness
  have hw0 : (29558095907388785 / 100000000000000000 : ℝ≥0∞) ≠ 0 := by simp
  have hwt : (29558095907388785 / 100000000000000000 : ℝ≥0∞) ≠ ⊤ := by finiteness
  generalize (1 - 3522095204630561 / 5000000000000000 : ℝ≥0∞) = q at hq ⊢
  generalize (29558095907388785 / 100000000000000000 : ℝ≥0∞) = w at hq hw0 hwt ⊢
  generalize (35700035696434995 / 100000000000000000 * (3522095204630561 / 5000000000000000)
    : ℝ≥0∞) = A at hA0 hAt ⊢
  rw [mul_assoc, show w ^ 5 = w ^ 2 * w ^ 3 by ring]
  exact ENNReal.mul_lt_mul_right hA0 hAt (ENNReal.mul_lt_mul_left (pow_ne_zero _ hw0)
    (ENNReal.pow_ne_top hwt) (ENNReal.pow_lt_pow_left two_ne_zero hq))

/-! ## Anticipated rejection of open terms

`pickIndex` walks the list of binders above it and fails when it runs out; `ranTypable` then restarts
from scratch. -/

/-- `pickIndex` with `n` binders left: `0` with probability `pz`, else one binder further out. -/
def genIdxC [Gen G] (pz : Rat) : Nat → G (Option Nat)
  | 0 => return none
  | n + 1 => do
    if ← coin pz then return some 0 else return (← genIdxC pz n).map (· + 1)

/-- `ranTypable` without types: `genLam` under `n` binders, giving up on an unbound index. -/
def genClosed [Gen G] (wi wl wa : Nat) (h : 0 < wi + wl + wa) (pz : Rat) (n : Nat) :
    G (Option Term) :=
  frequency! [
    (wi, fun _ => do return (← genIdxC pz n).map .var),
    (wl, fun _ => do return (← genClosed wi wl wa h pz (n + 1)).map .lam),
    (wa, fun _ => do
      match ← genClosed wi wl wa h pz n with
      | none => return none
      | some t => return (← genClosed wi wl wa h pz n).map (.app t))]
    (by simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; omega)
partial_fixpoint

section option

variable {α β : Type}

theorem bind_map_apply {x : SPMF (Option α)} {f : α → β} (hf : f.Injective) (a : α) :
    (x >>= fun o => Pure.pure (o.map f)) (some (f a)) = x (some a) := by
  rw [bind_apply, tsum_option, tsum_eq_single a fun b hb => by simp [hf.ne hb, Ne.symm]]
  simp

theorem bind_map_apply_of_ne {x : SPMF (Option α)} {f : α → β} {b : β} (hb : ∀ a, f a ≠ b) :
    (x >>= fun o => Pure.pure (o.map f)) (some b) = 0 := by
  rw [bind_apply, tsum_option]
  simp [fun a => Ne.symm (hb a)]

end option

theorem genIdxC_apply (hp0 : 0 ≤ pz) (hp1 : pz ≤ 1) :
    ∀ n k, (genIdxC pz n : SPMF (Option Nat)) (some k)
      = if k < n then (genIdx pz : SPMF Nat) k else 0
  | 0, k => by simp [genIdxC]
  | n + 1, k => by
    rw [genIdxC, bind_apply, tsum_bool]
    simp only [Bool.false_eq_true, ↓reduceIte, coin_false hp0 hp1, coin_true hp0 hp1]
    rcases k with _ | k
    · rw [bind_map_apply_of_ne fun _ => Nat.succ_ne_zero _, genIdx_apply hp0 hp1]
      simp
    · rw [bind_map_apply (f := (· + 1)) (fun _ _ h => Nat.succ.inj h), genIdxC_apply hp0 hp1 n k,
        genIdx_apply hp0 hp1, genIdx_apply hp0 hp1]
      simp only [pure_apply, Option.some.injEq, Nat.add_one_ne_zero, ↓reduceIte, mul_zero,
        add_zero, Nat.add_lt_add_iff_right]
      split_ifs <;> ring

section option

variable {α β : Type}

theorem bind_option_bind_apply {x y : SPMF (Option α)} {f : Option α → SPMF (Option β)}
    {g : α → α → β} (hg : ∀ a b a' b', g a b = g a' b' → a = a' ∧ b = b')
    (hnone : f none = Pure.pure none)
    (hsome : ∀ a, f (some a) = y >>= fun o => Pure.pure (o.map (g a))) (a b : α) :
    (x >>= f) (some (g a b)) = x (some a) * y (some b) := by
  rw [bind_apply, tsum_option, hnone, tsum_eq_single a fun a' ha' => by
    rw [hsome, bind_map_apply_of_ne fun b' h => ha' (hg _ _ _ _ h).1, mul_zero]]
  rw [hsome, bind_map_apply fun _ _ h => (hg _ _ _ _ h).2]
  simp

theorem bind_option_bind_apply_of_ne {x y : SPMF (Option α)} {f : Option α → SPMF (Option β)}
    {g : α → α → β} (hnone : f none = Pure.pure none)
    (hsome : ∀ a, f (some a) = y >>= fun o => Pure.pure (o.map (g a))) {c : β}
    (hc : ∀ a b, g a b ≠ c) : (x >>= f) (some c) = 0 := by
  rw [bind_apply, tsum_option, hnone]
  simp only [pure_apply, reduceCtorEq, ↓reduceIte, mul_zero, zero_add]
  exact ENNReal.tsum_eq_zero.2 fun a => by rw [hsome, bind_map_apply_of_ne (hc a), mul_zero]

end option

/-- **Anticipated rejection keeps the point masses**: the early-failing sampler gives each term it
returns exactly `genLam`'s mass, and returns exactly the closed ones. -/
theorem genClosed_apply (h : 0 < wi + wl + wa) (hp0 : 0 ≤ pz) (hp1 : pz ≤ 1) (t : Term) :
    ∀ n, (genClosed wi wl wa h pz n : SPMF (Option Term)) (some t)
      = if t.closedUnder n then (genLam wi wl wa h pz : SPMF Term) t else 0 := by
  have hS : ((wi + wl + wa : ℕ) : ℝ≥0∞) = wi + wl + wa := by push_cast; ring
  induction t with
  | var k =>
    intro n
    rw [genClosed, frequencyWith_eq, frequency_apply]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    rw [bind_map_apply (fun _ _ h => Term.var.inj h), genIdxC_apply hp0 hp1,
      bind_map_apply_of_ne fun _ => Term.noConfusion,
      bind_option_bind_apply_of_ne (g := Term.app) (by rfl) (by intros; rfl)
        (by intros; exact Term.noConfusion), genLam_apply h hp0 hp1, genIdx_apply hp0 hp1]
    simp only [Term.closedUnder, decide_eq_true_eq, Term.vars, Term.succs, Term.lams, Term.apps,
      pow_one, pow_zero, mul_one, mul_zero, add_zero, Nat.cast_add, ← add_assoc]
    split_ifs <;> simp only [mul_zero, div_eq_mul_inv] <;> ring
  | lam t ih =>
    intro n
    rw [genClosed, frequencyWith_eq, frequency_apply]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    rw [bind_map_apply_of_ne fun _ => Term.noConfusion,
      bind_map_apply (fun _ _ h => Term.lam.inj h), ih,
      bind_option_bind_apply_of_ne (g := Term.app) (by rfl) (by intros; rfl)
        (by intros; exact Term.noConfusion), genLam_apply h hp0 hp1, genLam_apply h hp0 hp1]
    simp only [Term.closedUnder, Term.vars, Term.succs, Term.lams, Term.apps, mul_zero, add_zero,
      zero_add, Nat.cast_add, ← add_assoc, pow_succ]
    split_ifs <;> simp only [mul_zero, div_eq_mul_inv] <;> ring
  | app t u iht ihu =>
    intro n
    rw [genClosed, frequencyWith_eq, frequency_apply]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    rw [bind_map_apply_of_ne fun _ => Term.noConfusion,
      bind_map_apply_of_ne fun _ => Term.noConfusion,
      bind_option_bind_apply (g := Term.app) (fun _ _ _ _ h => Term.app.inj h) (by rfl)
        (by intros; rfl), iht, ihu, genLam_apply h hp0 hp1, genLam_apply h hp0 hp1,
      genLam_apply h hp0 hp1]
    simp only [Term.closedUnder, Bool.and_eq_true, Term.vars, Term.succs, Term.lams, Term.apps,
      mul_zero, zero_add, Nat.cast_add, ← add_assoc, pow_succ, pow_add]
    by_cases ht : t.closedUnder n <;> by_cases hu : u.closedUnder n <;>
      simp only [ht, hu, and_self, and_true, ↓reduceIte, Bool.false_eq_true, and_false,
        mul_zero, zero_mul, div_eq_mul_inv]
    ring

/-- Subcritical when an application is no likelier than an index (mean offspring
`(wl + 2 wa) / (wi + wl + wa) ≤ 1`), critical case included. -/
theorem genLam_terminates (h : 0 < wi + wl + wa) (hwi : 0 < wi) (hwa : wa ≤ wi) (hp0 : 0 < pz)
    (hp1 : pz ≤ 1) : IsAlmostSurelyTerminating (genLam wi wl wa h pz : SPMF Term) := by
  have hS0 : (wi + wl + wa : ℝ≥0∞) ≠ 0 := by simp; omega
  have hStop : (wi + wl + wa : ℝ≥0∞) ≠ ⊤ := by simp
  have hidx := genIdx_terminates hp0 hp1
  mass_fixpoint [hidx.obs] using SPMF.LfpIsOne.quadratic (a := wi / (wi + wl + wa : ℝ≥0∞))
    (b := wl / (wi + wl + wa : ℝ≥0∞)) (d := wa / (wi + wl + wa : ℝ≥0∞))
    (by rw [ENNReal.div_add_div_same, ENNReal.div_add_div_same, ENNReal.div_self hS0 hStop])
    (by
      rw [← mul_div_assoc, ENNReal.div_add_div_same]
      exact ENNReal.div_le_of_le_mul (by rw [one_mul]; exact_mod_cast (by omega : wl + 2 * wa ≤ wi + wl + wa)))
    (ENNReal.div_pos (by exact_mod_cast hwi.ne') hStop)
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, mul_one,
    Nat.cast_add, ← add_assoc, ENNReal.add_div, sq]
  simp only [div_eq_mul_inv]
  exact le_of_eq (by ring)

theorem genIdxC_terminates (hp0 : 0 ≤ pz) (hp1 : pz ≤ 1) :
    ∀ n, IsAlmostSurelyTerminating (genIdxC pz n : SPMF (Option Nat))
  | 0 => by simp [IsAlmostSurelyTerminating, genIdxC]
  | n + 1 => by
    have ih := genIdxC_terminates hp0 hp1 n
    unfold IsAlmostSurelyTerminating at *
    rw [genIdxC, mass_bind_tsum, tsum_bool]
    simp only [Bool.false_eq_true, ↓reduceIte, coin_false hp0 hp1, coin_true hp0 hp1, mass_pure,
      mass_bind_pure, ih, mul_one]
    exact tsub_add_cancel_of_le (pr_le_one hp0 hp1)

/-- The early-failing sampler halts whenever `genLam` does: giving up only stops sooner. -/
theorem genClosed_terminates (h : 0 < wi + wl + wa) (hwi : 0 < wi) (hwa : wa ≤ wi) (hp0 : 0 ≤ pz)
    (hp1 : pz ≤ 1) (n : Nat) :
    IsAlmostSurelyTerminating (genClosed wi wl wa h pz n : SPMF (Option Term)) := by
  have hS0 : (wi + wl + wa : ℝ≥0∞) ≠ 0 := by simp; omega
  have hStop : (wi + wl + wa : ℝ≥0∞) ≠ ⊤ := by simp
  have hidx := fun n => (genIdxC_terminates hp0 hp1 n).obs
  mass_fixpoint [hidx] using SPMF.LfpIsOne.quadratic (a := wi / (wi + wl + wa : ℝ≥0∞))
    (b := wl / (wi + wl + wa : ℝ≥0∞)) (d := wa / (wi + wl + wa : ℝ≥0∞))
    (by rw [ENNReal.div_add_div_same, ENNReal.div_add_div_same, ENNReal.div_self hS0 hStop])
    (by
      rw [← mul_div_assoc, ENNReal.div_add_div_same]
      exact ENNReal.div_le_of_le_mul (by rw [one_mul]; exact_mod_cast (by omega : wl + 2 * wa ≤ wi + wl + wa)))
    (ENNReal.div_pos (by exact_mod_cast hwi.ne') hStop)
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, mul_one,
    Nat.cast_add, ← add_assoc]
  have hinf : c ≤ ⨅ a : Option Term, (match a with | none => 1 | some _ => c : ℝ≥0∞) :=
    le_iInf fun a => by cases a <;> simp [hc1]
  calc _ = ((wi : ℝ≥0∞) + wl * c + wa * (c * c)) / (wi + wl + wa) := by
        simp only [sq, div_eq_mul_inv]; ring
    _ ≤ _ := by gcongr

/-- **Anticipated rejection is rejection** (§4): restarting the early-failing sampler from scratch
is drawing plain terms until one is closed. -/
theorem retry_genClosed (h : 0 < wi + wl + wa) (hwi : 0 < wi) (hwa : wa ≤ wi) (hp0 : 0 < pz)
    (hp1 : pz ≤ 1) :
    (retry (genClosed wi wl wa h pz 0) : SPMF Term)
      = suchThat (genLam wi wl wa h pz) (Term.closedUnder 0) :=
  retry_eq_suchThat (fun t => genClosed_apply h hp0.le hp1 t 0)
    (genClosed_terminates h hwi hwa hp0.le hp1 0) (genLam_terminates h hwi hwa hp0 hp1)

/-- **Uniform among closed terms of a size**, under the Boltzmann relations, whether or not the
sampler terminates. -/
theorem retry_genClosed_uniform (h : 0 < wi + wl + wa) (hp0 : 0 ≤ pz) (hp1 : pz ≤ 1) {x L : ℝ≥0∞}
    (hB : IsBoltzmann (genLam wi wl wa h pz : SPMF Term) Term.size x L) {s t : Term}
    (hs : s.closedUnder 0) (ht : t.closedUnder 0) (hst : s.size = t.size) :
    (retry (genClosed wi wl wa h pz 0) : SPMF Term) s
      = (retry (genClosed wi wl wa h pz 0) : SPMF Term) t := by
  rw [retry_apply, retry_apply, genClosed_apply h hp0 hp1, genClosed_apply h hp0 hp1]
  simp only [hs, ht, ↓reduceIte, hB.uniform hst]

/-- The printed sampler is subcritical (mean offspring `≈ 0.9904`), so it and its anticipated
rejection both terminate, and they agree. -/
theorem paperSampler_retry :
    (retry (genClosed 35700035696434995 29558095907388785 34741868396176220 (by norm_num)
        (7044190409261122 / 10 ^ 16) 0) : SPMF Term)
      = suchThat (paperSampler : SPMF Term) (Term.closedUnder 0) :=
  retry_genClosed _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end Boltzmann.Lambda
