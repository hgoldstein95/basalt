/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt.SPMF.Cost
import Basalt.Walk.Average

/-!
# Walking Expected-Cost Bounds

What the walk needs of a bound on `SPMF.Cost.expectObs.spec g f`, on which
`IsExpectedCostBounded g B` is the upper bound at `f = fun _ n => n`: how a fact about a
sub-generator closes a leaf in either direction, the rules of the list combinators and of
`suchThat`, and the admissibility `walk fixpoint` inducts with for an upper bound.
-/

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

end suchThat

/-! ## QuickCheck's combinators

`trySizes` pays for each draw it makes, at most one per size it tries. The retry loop
`suchThatFrom` is bounded as `suchThat` is, each draw at a size from its first on: a round that
returns nothing starts the loop over, one size later. -/

section quickCheck

open QuickCheck

variable {α β : Type} {gs : Nat → SPMF.Cost α} {f : α → Option β} {C r : ℝ≥0∞}

/-- A generator of expected cost `C` followed by continuations of expected cost at most `D`. -/
private theorem expect_bind_le_add {x : SPMF.Cost α} {k : α → SPMF.Cost β} {D : ℝ≥0∞}
    (hx : expectObs.spec x (fun _ n => (n : ℝ≥0∞)) ≤ C)
    (hk : ∀ a, expectObs.spec (k a) (fun _ n => (n : ℝ≥0∞)) ≤ D) :
    expectObs.spec (x >>= k) (fun _ n => (n : ℝ≥0∞)) ≤ C + D := by
  have hstep : ∀ a n, expectObs.spec (k a) (fun _ n' => ((n + n' : Nat) : ℝ≥0∞)) ≤ n + D :=
    fun a n => expect_le_add_of_le (hk a) fun _ _ => by push_cast; rfl
  refine (congrFun (expectObs.map_bind x k) _).le.trans ((Obs.MonotoneC.spec_mono x hstep).trans ?_)
  show SPMF.expect x (fun q => (q.2 : ℝ≥0∞) + D) ≤ C + D
  rw [SPMF.expect_add, SPMF.expect_const]
  exact add_le_add hx (mul_le_of_le_one_left' (SPMF.mass_le_one x))

theorem expect_trySizes_cost_le (hg : ∀ j, expectObs.spec (gs j) (fun _ n => (n : ℝ≥0∞)) ≤ C)
    (m k : Nat) : expectObs.spec (trySizes gs f m k) (fun _ n => (n : ℝ≥0∞)) ≤ k * C := by
  induction k generalizing m with
  | zero =>
    rw [trySizes]
    exact (congrFun (expectObs.map_pure _) _).le.trans (by simp [WPC.pure_apply])
  | succ k ih =>
    rw [trySizes]
    refine (expect_bind_le_add (hg m) fun a => ?_).trans
      (by rw [Nat.cast_succ, add_mul, one_mul, add_comm])
    split
    · exact (congrFun (expectObs.map_pure _) _).le.trans (by simp [WPC.pure_apply])
    · exact ih (m + 1)

@[gen_rule]
theorem expect_trySizes_le {m k : Nat} {post : Option β → Nat → ℝ≥0∞} {d : ℝ≥0∞}
    (hg : ∀ j, expectObs.spec (gs j) (fun _ n => (n : ℝ≥0∞)) ≤ C)
    (hpost : ∀ a n, post a n = d + n) :
    expectObs.spec (trySizes gs f m k) post ≤ d + k * C :=
  expect_le_add_of_le (expect_trySizes_cost_le hg m k) hpost

@[gen_rule] theorem expect_trySizes_le_const {m k : Nat} {p : Option β → Nat → ℝ≥0∞}
    {d : ℝ≥0∞} (hp : ∀ a n, p a n = d) : expectObs.spec (trySizes gs f m k) p ≤ d :=
  expect_le_of_const hp

@[gen_rule] theorem expect_trySizes_le_iSup {m k : Nat} {p : Option β → Nat → ℝ≥0∞} :
    expectObs.spec (trySizes gs f m k) p ≤ ⨆ a, ⨆ n, p a n := expect_le_iSup

/-- One round of `trySizes` from size `m` on, then `cont`: at most `B` in all, when `cont` costs
nothing after a value and at most `B` after none, and `C + r * B ≤ B`. -/
private theorem expect_trySizes_bind_le {n : Nat} {B : ℝ≥0∞}
    (hg : ∀ j, n ≤ j → expectObs.spec (gs j) (fun _ n => (n : ℝ≥0∞)) ≤ C)
    (hr : ∀ j, n ≤ j → expectObs.spec (gs j) (fun a _ => if (f a).isSome then 0 else 1) ≤ r)
    (hB : C + r * B ≤ B) {cont : Option β → SPMF.Cost β}
    (hsome : ∀ b, cont (some b) = Pure.pure b)
    (hnone : expectObs.spec (cont none) (fun _ n => (n : ℝ≥0∞)) ≤ B) :
    ∀ k m, n ≤ m → expectObs.spec (trySizes gs f m k >>= cont) (fun _ n => (n : ℝ≥0∞)) ≤ B := by
  intro k
  induction k with
  | zero =>
    intro m _
    rw [trySizes, LawfulMonad.pure_bind]
    exact hnone
  | succ k ih =>
    intro m hm
    rw [trySizes, LawfulMonad.bind_assoc]
    have hstep : ∀ a n, expectObs.spec
        ((if (f a).isSome then Pure.pure (f a) else trySizes gs f (m + 1) k) >>= cont)
        (fun _ n' => ((n + n' : Nat) : ℝ≥0∞)) ≤ if (f a).isSome then (n : ℝ≥0∞) else n + B := by
      intro a n
      split
      · rename_i h
        obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp h
        rw [hb, LawfulMonad.pure_bind, hsome]
        exact (congrFun (expectObs.map_pure _) _).le.trans (by simp [WPC.pure_apply])
      · exact expect_le_add_of_le (ih (m + 1) (by omega)) fun _ _ => by push_cast; rfl
    exact (congrFun (expectObs.map_bind _ _) _).le.trans ((Obs.MonotoneC.spec_mono _ hstep).trans
      ((expect_retry_le (p := fun a => (f a).isSome) (hg m hm) (hr m hm) B).trans hB))

theorem expect_suchThatFrom_cost_le {n : Nat}
    (hg : ∀ j, n ≤ j → expectObs.spec (gs j) (fun _ n => (n : ℝ≥0∞)) ≤ C)
    (hr : ∀ j, n ≤ j → expectObs.spec (gs j) (fun a _ => if (f a).isSome then 0 else 1) ≤ r) :
    expectObs.spec (suchThatFrom gs f n) (fun _ n => (n : ℝ≥0∞)) ≤ C / (1 - r) := by
  refine suchThatFrom.fixpoint_induct gs f
    (fun z => ∀ k, n ≤ k → expectObs.spec (z k) (fun _ n => (n : ℝ≥0∞)) ≤ C / (1 - r))
    (Lean.Order.admissible_pi_apply
      (fun k (x : SPMF.Cost β) => n ≤ k → expectObs.spec x (fun _ n => (n : ℝ≥0∞)) ≤ C / (1 - r))
      fun k c hc h hk => expectObs.admissible_le _ _ c hc fun x hx => h x hx hk)
    (fun z ih k hk => ?_) n le_rfl
  exact expect_trySizes_bind_le hg hr (add_mul_div_one_sub_le C r) (fun _ => rfl)
    (ih (k + 1) (by omega)) (k + 1) k hk

@[gen_rule]
theorem expect_suchThatFrom_le {n : Nat} {post : β → Nat → ℝ≥0∞} {d : ℝ≥0∞}
    (hg : ∀ j, n ≤ j → expectObs.spec (gs j) (fun _ n => (n : ℝ≥0∞)) ≤ C)
    (hr : ∀ j, n ≤ j → expectObs.spec (gs j) (fun a _ => if (f a).isSome then 0 else 1) ≤ r)
    (hpost : ∀ a n, post a n = d + n) :
    expectObs.spec (suchThatFrom gs f n) post ≤ d + C / (1 - r) :=
  expect_le_add_of_le (expect_suchThatFrom_cost_le hg hr) hpost

/-- `QuickCheck.suchThat p`, at a size, is `suchThatFrom` of `Option.guard p`: its rejections are
stated through `p`. -/
@[gen_rule]
theorem expect_suchThatFrom_guard_le {n : Nat} {p : α → Bool} {post : α → Nat → ℝ≥0∞} {d : ℝ≥0∞}
    {gs : Nat → SPMF.Cost α}
    (hg : ∀ j, n ≤ j → expectObs.spec (gs j) (fun _ n => (n : ℝ≥0∞)) ≤ C)
    (hr : ∀ j, n ≤ j → expectObs.spec (gs j) (fun a _ => if p a then 0 else 1) ≤ r)
    (hpost : ∀ a n, post a n = d + n) :
    expectObs.spec (suchThatFrom gs (Option.guard p) n) post ≤ d + C / (1 - r) :=
  expect_suchThatFrom_le hg (fun j hj => by simpa [Option.isSome_guard] using hr j hj) hpost

@[gen_rule] theorem expect_sublistOf_le_const {xs : List α} {p : List α → Nat → ℝ≥0∞}
    {d : ℝ≥0∞} (hp : ∀ a n, p a n = d) : expectObs.spec (sublistOf xs) p ≤ d :=
  expect_le_of_const hp

@[gen_rule] theorem expect_sublistOf_le_iSup {xs : List α} {p : List α → Nat → ℝ≥0∞} :
    expectObs.spec (sublistOf xs) p ≤ ⨆ a, ⨆ n, p a n := expect_le_iSup

@[gen_rule] theorem expect_shuffle_le_const {xs : List α} {p : List α → Nat → ℝ≥0∞}
    {d : ℝ≥0∞} (hp : ∀ a n, p a n = d) : expectObs.spec (shuffle xs) p ≤ d :=
  expect_le_of_const hp

@[gen_rule] theorem expect_shuffle_le_iSup {xs : List α} {p : List α → Nat → ℝ≥0∞} :
    expectObs.spec (shuffle xs) p ≤ ⨆ a, ⨆ n, p a n := expect_le_iSup

end quickCheck

@[gen_rule] theorem expect_permutationOf_le_const {xs : List α}
    {p : { ys // xs.Perm ys } → Nat → ℝ≥0∞} {d : ℝ≥0∞} (hp : ∀ a n, p a n = d) :
    expectObs.spec (permutationOf xs) p ≤ d := expect_le_of_const hp

@[gen_rule] theorem expect_permutationOf_le_iSup {xs : List α}
    {p : { ys // xs.Perm ys } → Nat → ℝ≥0∞} :
    expectObs.spec (permutationOf xs) p ≤ ⨆ a, ⨆ n, p a n :=
  expect_le_iSup

end SPMF.Cost
