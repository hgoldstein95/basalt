/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
module

public import Basalt.Laws
public import Basalt.SPMF.Cost
public import Basalt.SPMF.Expect.Combinators
public import Basalt.Walk.Average

/-!
# Walking Expected-Cost Bounds

What the walk needs of a bound on `SPMF.Cost.expectObs.spec g f`, on which
`IsExpectedCostBounded g B` is the upper bound at `f = fun _ n => n`: how a fact about a
sub-generator closes a leaf in either direction, the rules of the list combinators and of
`suchThat`, and the admissibility `walk fixpoint` inducts with for an upper bound. `suchThat`'s
expected-cost laws, in both directions, live here too.
-/

@[expose] public section

open ENNReal RandomChoice

namespace SPMF.Cost

open Lean.Order in
theorem expectObs.admissible_le (f : α → Nat → ℝ≥0∞) (B : ℝ≥0∞) :
    admissible fun x : SPMF.Cost α => expectObs.spec x f ≤ B :=
  SPMF.admissible_expect_le (fun p : α × Nat => f p.1 p.2) B

/-! ## Leaves

A fact bounds a sub-generator's expectation under its own postexpectation `h`; the walk arrives with
`k + h`, `k` the choices made before it, and the missing mass only helps. -/

@[obs_leaf]
theorem expect_le_add_of_le {x : SPMF.Cost α} {h p : α → Nat → ℝ≥0∞} {k B : ℝ≥0∞}
    (hx : expectObs.spec x h ≤ B) (hp : ∀ a n, p a n = k + h a n) :
    expectObs.spec x p ≤ k + B := by
  show SPMF.expect x (fun q => p q.1 q.2) ≤ k + B
  rw [funext fun q : α × Nat => hp q.1 q.2, SPMF.expect_add, SPMF.expect_const]
  exact add_le_add (mul_le_of_le_one_left' (SPMF.mass_le_one x)) hx

/-! ## Lower bounds

The generator that never returns costs nothing, so no fixpoint induction proves a lower bound on an
expected cost. One is had by unfolding a generator once, since that is an equation, and passing its
own expected cost as the fact about its recursive calls. The walk meets them under `k + h`, which
the fact bounds only when the mass is `1`: `le_expect_add` states it that way. -/

/-- A lower bound `B` on `x`'s expectation of `h`, for use under any `k + h`, from `x`'s mass. -/
theorem le_expect_add {x : SPMF.Cost α} {h : α → Nat → ℝ≥0∞} {B : ℝ≥0∞}
    (hm : 1 ≤ expectObs.spec x fun _ _ => 1) (hx : B ≤ expectObs.spec x h) (k : ℝ≥0∞) :
    k + B ≤ expectObs.spec x fun a n => k + h a n := by
  show _ ≤ SPMF.expect x fun q => k + h q.1 q.2
  rw [SPMF.expect_add, SPMF.expect_const]
  exact add_le_add (le_mul_of_one_le_left' (hm.trans_eq (SPMF.expect_one x))) hx

@[obs_leaf]
theorem le_expect_of_add_le {x : SPMF.Cost α} {h p : α → Nat → ℝ≥0∞} {k B : ℝ≥0∞}
    (hx : ∀ k, k + B ≤ expectObs.spec x fun a n => k + h a n) (hp : ∀ a n, p a n = k + h a n) :
    k + B ≤ expectObs.spec x p := by
  have : p = fun a n => k + h a n := funext fun a => funext fun n => hp a n
  subst this
  exact hx k

/-! ## The list combinators

As for `SPMF.expectObs` (`Basalt/Walk/Expect.lean`), a list combinator is bounded using only its
mass: exactly when the postexpectation is constant, and otherwise at its worst case over every value
and cost. -/

/-- What the missing mass buys: an expectation is at most its postexpectation's largest value,
whatever the generator. -/
theorem expect_le_of_const {x : SPMF.Cost α} {p : α → Nat → ℝ≥0∞} {d : ℝ≥0∞}
    (hp : ∀ a n, p a n = d) : expectObs.spec x p ≤ d :=
  SPMF.expect_le_of_support fun q _ => (hp q.1 q.2).le

@[inherit_doc expect_le_of_const]
theorem expect_le_iSup {x : SPMF.Cost α} {p : α → Nat → ℝ≥0∞} :
    expectObs.spec x p ≤ ⨆ a, ⨆ n, p a n :=
  SPMF.expect_le_of_support fun q _ => le_iSup₂ (f := p) q.1 q.2

section listCombinators

variable {α : Type} {g : SPMF.Cost α} {p : List α → Nat → ℝ≥0∞} {d : ℝ≥0∞}

@[gen_rule] theorem expect_vectorOf_le_const {n : Nat} (hp : ∀ a n, p a n = d) :
    expectObs.spec (vectorOf n g) p ≤ d := expect_le_of_const hp

@[gen_rule] theorem expect_vectorOf_le_iSup {n : Nat} :
    expectObs.spec (vectorOf n g) p ≤ ⨆ a, ⨆ n, p a n := expect_le_iSup

@[gen_rule] theorem expect_listOfMaxLength_le_const {n : Nat} (hp : ∀ a n, p a n = d) :
    expectObs.spec (listOfMaxLength n g) p ≤ d := expect_le_of_const hp

@[gen_rule] theorem expect_listOfMaxLength_le_iSup {n : Nat} :
    expectObs.spec (listOfMaxLength n g) p ≤ ⨆ a, ⨆ n, p a n := expect_le_iSup

@[gen_rule] theorem expect_listOf_le_const (hp : ∀ a n, p a n = d) :
    expectObs.spec (listOf g) p ≤ d := expect_le_of_const hp

@[gen_rule] theorem expect_listOf_le_iSup : expectObs.spec (listOf g) p ≤ ⨆ a, ⨆ n, p a n :=
  expect_le_iSup

@[gen_rule] theorem expect_nonEmptyListOf_le_const (hp : ∀ a n, p a n = d) :
    expectObs.spec (nonEmptyListOf g) p ≤ d := expect_le_of_const hp

@[gen_rule] theorem expect_nonEmptyListOf_le_iSup :
    expectObs.spec (nonEmptyListOf g) p ≤ ⨆ a, ⨆ n, p a n := expect_le_iSup

end listCombinators

/-! ## Rejection sampling

`suchThat g p` is bounded exactly, from `g`'s expected cost `C` and a bound `r` on how often it
rejects: each draw pays its own cost, and a rejected one pays for starting over, so the expected
cost `B` satisfies `B ≤ C + r * B`, whose least solution is `C / (1 - r)`. -/

section suchThat

variable {α : Type} {g : SPMF.Cost α} {p : α → Bool} {C r : ℝ≥0∞}

private theorem expect_retry_le (hg : expectObs.spec g (fun _ n => (n : ℝ≥0∞)) ≤ C)
    (hr : expectObs.spec g (fun a _ => if p a then 0 else 1) ≤ r) (B : ℝ≥0∞) :
    expectObs.spec g (fun a n => if p a then (n : ℝ≥0∞) else n + B) ≤ C + r * B := by
  have hsplit : (fun q : α × Nat => if p q.1 then (q.2 : ℝ≥0∞) else q.2 + B)
      = fun q => (q.2 : ℝ≥0∞) + B * if p q.1 then 0 else 1 := by
    funext q; split <;> simp
  show SPMF.expect g _ ≤ _
  rw [hsplit, SPMF.expect_add, SPMF.expect_mul_left, mul_comm B]
  exact add_le_add hg (mul_le_mul_left hr B)

private theorem add_mul_div_one_sub_le (C r : ℝ≥0∞) : C + r * (C / (1 - r)) ≤ C / (1 - r) := by
  rcases lt_or_ge r 1 with hr | hr
  · refine le_of_eq ?_
    calc C + r * (C / (1 - r)) = (1 - r) * (C / (1 - r)) + r * (C / (1 - r)) := by
          rw [ENNReal.mul_div_cancel (tsub_pos_of_lt hr).ne'
            (ENNReal.sub_ne_top ENNReal.one_ne_top)]
      _ = C / (1 - r) := by rw [← add_mul, tsub_add_cancel_of_le hr.le, one_mul]
  · rw [tsub_eq_zero_of_le hr]
    rcases eq_or_ne C 0 with rfl | hC
    · simp
    · rw [ENNReal.div_zero hC]; exact le_top

theorem expect_suchThat_cost_le (hg : expectObs.spec g (fun _ n => (n : ℝ≥0∞)) ≤ C)
    (hr : expectObs.spec g (fun a _ => if p a then 0 else 1) ≤ r) :
    expectObs.spec (suchThat g p) (fun _ n => (n : ℝ≥0∞)) ≤ C / (1 - r) := by
  refine suchThat.fixpoint_induct g p
    (fun x => expectObs.spec x (fun _ n => (n : ℝ≥0∞)) ≤ C / (1 - r))
    (expectObs.admissible_le _ _) fun z ih => ?_
  have hstep : ∀ a n, expectObs.spec (if p a then Pure.pure a else z)
      (fun _ n' => ((n + n' : Nat) : ℝ≥0∞)) ≤ if p a then (n : ℝ≥0∞) else n + C / (1 - r) := by
    intro a n
    split
    · exact (congrFun (expectObs.map_pure a) _).le.trans (by simp [WPC.pure_apply])
    · exact expect_le_add_of_le ih fun _ _ => by push_cast; rfl
  exact (congrFun (expectObs.map_bind g _) _).le.trans ((Obs.MonotoneC.spec_mono g hstep).trans
    ((expect_retry_le hg hr _).trans (add_mul_div_one_sub_le C r)))

/-- A bound `B` on `C / (1 - r)` from one step of the loop, the form the arithmetic of a
`suchThat` bound is easiest in. -/
theorem div_one_sub_le {B : ℝ≥0∞} (hB : B ≠ ⊤) (h : C + r * B ≤ B) : C / (1 - r) ≤ B := by
  refine ENNReal.div_le_of_le_mul' ?_
  rw [ENNReal.sub_mul fun _ _ => hB, one_mul]
  exact ENNReal.le_sub_of_add_le_right (ne_top_of_le_ne_top hB (le_add_self.trans h)) h

@[gen_rule]
theorem expect_suchThat_le {post : α → Nat → ℝ≥0∞} {k : ℝ≥0∞}
    (hg : expectObs.spec g (fun _ n => (n : ℝ≥0∞)) ≤ C)
    (hr : expectObs.spec g (fun a _ => if p a then 0 else 1) ≤ r)
    (hpost : ∀ a n, post a n = k + n) :
    expectObs.spec (suchThat g p) post ≤ k + C / (1 - r) :=
  expect_le_add_of_le (expect_suchThat_cost_le hg hr) hpost

/-- The first draw alone costs `g`'s expected cost whenever the loop goes on to return, which it
does with chance at least `a`, any bound on how often `g` accepts. -/
theorem mul_expect_le_expect_suchThat {a : ℝ≥0∞}
    (ha : a ≤ expectObs.spec g fun x _ => if p x then 1 else 0) :
    a * expectObs.spec g (fun _ n => (n : ℝ≥0∞))
      ≤ expectObs.spec (suchThat g p) fun _ n => (n : ℝ≥0∞) := by
  set M := expectObs.spec (suchThat g p) fun _ _ => (1 : ℝ≥0∞) with hM
  have hM1 : M ≤ 1 := (SPMF.expect_one _).trans_le (SPMF.mass_le_one _)
  have haM : a ≤ M := by
    refine ha.trans ?_
    rw [hM]
    conv_rhs => rw [suchThat]
    refine le_of_le_of_eq (Obs.MonotoneC.spec_mono g fun x n => ?_)
      (congrFun (expectObs.map_bind g _) _).symm
    by_cases h : p x
    · simp only [h, ite_true]
      rw [congrFun (expectObs.map_pure x) _, WPC.pure_apply]
    · simp only [h]
      exact zero_le
  have hk : ∀ x (n : Nat), M * n ≤ expectObs.spec (if p x then Pure.pure x else suchThat g p)
      fun _ m => ((n + m : Nat) : ℝ≥0∞) := by
    intro x n
    by_cases h : p x
    · simp only [h, ite_true]
      rw [congrFun (expectObs.map_pure x) _, WPC.pure_apply]
      simpa using mul_le_of_le_one_left' hM1
    · simp only [h]
      calc M * n = SPMF.expect (suchThat (G := SPMF.Cost) g p) fun _ => (n : ℝ≥0∞) := by
            rw [hM, SPMF.expect_const]
            exact congrArg (· * (n : ℝ≥0∞)) (SPMF.expect_one _)
        _ ≤ _ := SPMF.expect_mono fun q => by push_cast; exact le_self_add
  conv_rhs => rw [suchThat]
  refine le_of_le_of_eq ?_ (congrFun (expectObs.map_bind g _) _).symm
  calc a * expectObs.spec g (fun _ n => (n : ℝ≥0∞))
      ≤ M * expectObs.spec g (fun _ n => (n : ℝ≥0∞)) := mul_le_mul_left haM _
    _ = expectObs.spec g (fun _ n => M * n) := (SPMF.expect_mul_left _ _ _).symm
    _ ≤ _ := Obs.MonotoneC.spec_mono g hk

end suchThat


@[gen_rule] theorem expect_permutationOf_le_const {xs : List α}
    {p : { ys // xs.Perm ys } → Nat → ℝ≥0∞} {d : ℝ≥0∞} (hp : ∀ a n, p a n = d) :
    expectObs.spec (permutationOf xs) p ≤ d := expect_le_of_const hp

@[gen_rule] theorem expect_permutationOf_le_iSup {xs : List α}
    {p : { ys // xs.Perm ys } → Nat → ℝ≥0∞} :
    expectObs.spec (permutationOf xs) p ≤ ⨆ a, ⨆ n, p a n :=
  expect_le_iSup

end SPMF.Cost

section suchThat

variable {α : Type} {gen : {G : Type → Type} → [Gen G] → G α} {p : α → Bool}

/-- Rejection sampling costs `g`'s expected cost over the chance of acceptance, from a bound `r` on
how often `g` rejects: each rejected draw costs what an accepted one does, and starts over. -/
theorem IsExpectedCostBounded.suchThat (hf : IsCostFaithful gen) {B r : ℝ≥0∞}
    (hg : IsExpectedCostBounded (gen (G := SPMF.Cost)) B)
    (hr : SPMF.prob (gen (G := SPMF)) {a | p a = false} ≤ r) :
    IsExpectedCostBounded (_root_.suchThat (gen (G := SPMF.Cost)) p) (B / (1 - r)) :=
  SPMF.Cost.expect_suchThat_cost_le hg
    ((hf.expect_eq _).trans_le ((SPMF.prob_reject_eq_expect _ p).symm.trans_le hr))

/-- The converse: a bound on rejection sampling bounds `g`'s expected cost, over any positive `a`
below the chance that `g` accepts. -/
theorem IsExpectedCostBounded.of_suchThat (hf : IsCostFaithful gen) {a B : ℝ≥0∞} (ha : a ≠ 0)
    (hacc : a ≤ SPMF.prob (gen (G := SPMF)) {x | p x = true})
    (h : IsExpectedCostBounded (_root_.suchThat (gen (G := SPMF.Cost)) p) B) :
    IsExpectedCostBounded (gen (G := SPMF.Cost)) (B / a) := by
  have ha1 : a ≠ ⊤ := ne_top_of_le_ne_top one_ne_top (hacc.trans (SPMF.prob_le_one _ _))
  rw [iff_obs, ENNReal.le_div_iff_mul_le (Or.inl ha) (Or.inl ha1), mul_comm]
  refine (SPMF.Cost.mul_expect_le_expect_suchThat ?_).trans h
  exact hacc.trans ((SPMF.prob_accept_eq_expect _ p).trans (hf.expect_eq _).symm).le

/-- Rejection sampling from a generator with no finite expected-cost bound has none either, as long
as `g` accepts at all; a `g` that never accepts gives a loop that never returns, which costs
nothing. -/
theorem IsExpectedCostBounded.not_suchThat (hf : IsCostFaithful gen)
    (hacc : 0 < SPMF.prob (gen (G := SPMF)) {x | p x = true})
    (hg : ∀ B, B ≠ ⊤ → ¬ IsExpectedCostBounded (gen (G := SPMF.Cost)) B) {B : ℝ≥0∞}
    (hB : B ≠ ⊤) : ¬ IsExpectedCostBounded (_root_.suchThat (gen (G := SPMF.Cost)) p) B :=
  fun h => hg _ (ENNReal.div_ne_top hB hacc.ne') (h.of_suchThat hf hacc.ne' le_rfl)

end suchThat
