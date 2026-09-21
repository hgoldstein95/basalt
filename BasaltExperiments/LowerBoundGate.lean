/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt
import BasaltExamples.ArbNat
open RandomChoice ENNReal Lean Meta Elab Tactic ArbNat

/-!
# The Lower-Bound Direction, Prototyped

What `mass_bound` would become under `PLAN.md`'s Stage 2 step 4: the rules for `b ≤ O.spec g post`
and `mass_bound'`, run on Appendix D's loops and on `BasaltTest/MassBound.lean`'s examples. The shape
rules that mirror `Basalt/SPMF/ExpectBound.lean`'s are `sorry`d.
-/

namespace Obs
variable {G : Type u → Type v} {Ω : Type w} [Preorder Ω] {m : Mix.{u} Ω} [Monad G] [RandomChoice G]
  {O : Obs G (WP m)}

@[gen_rule] theorem le_spec_pure {a : α} {post : α → Ω} {b : Ω} (hb : b ≤ post a) :
    b ≤ O.spec (Pure.pure a) post := hb.trans (congrFun (O.map_pure a) post).ge
@[gen_rule] theorem le_spec_bind [O.Monotone] {x : G α} {k : α → G β} {post : β → Ω} {h : α → Ω}
    {b : Ω} (hk : ∀ a, h a ≤ O.spec (k a) post) (hx : b ≤ O.spec x h) : b ≤ O.spec (x >>= k) post :=
  (hx.trans (Monotone.spec_mono x hk)).trans (congrFun (O.map_bind x k) post).ge
@[gen_rule] theorem le_spec_map [LawfulMonad G] {x : G α} {f : α → β} {post : β → Ω} {b : Ω}
    (hx : b ≤ O.spec x (fun a => post (f a))) : b ≤ O.spec (f <$> x) post :=
  hx.trans (congrFun (O.map_map f x) post).ge
@[gen_rule] theorem le_spec_ite {p : Prop} [Decidable p] {x y : G α} {post : α → Ω} {c d : Ω}
    (hx : p → c ≤ O.spec x post) (hy : ¬p → d ≤ O.spec y post) :
    (if p then c else d) ≤ O.spec (if p then x else y) post := by split <;> simp_all
theorem le_spec_of_map {g : G α} {w : WP m α} {post : α → Ω} {b : Ω}
    (h : O.spec g = w) (hw : b ≤ w post) : b ≤ O.spec g post := hw.trans (congrFun h post).ge
end Obs

namespace Mix
@[gen_rule] theorem le_average_mix {lo hi : Nat} {F : ULift.{u} {x : Nat // lo ≤ x ∧ x ≤ hi} → ℝ≥0∞}
    {d : Nat → ℝ≥0∞} (h : ∀ x (hx : lo ≤ x ∧ x ≤ hi), d x ≤ F ⟨⟨x, hx⟩⟩) :
    (∑ x ∈ Finset.Icc lo hi, d x) / ((hi - lo + 1 : ℕ) : ℝ≥0∞) ≤ Mix.average.mix lo hi F :=
  (range_average lo hi d).ge.trans (average_mix_mono fun a => h a.down.val a.down.property)
@[gen_rule] theorem le_average_binary {t e c d : ℝ≥0∞} (ht : c ≤ t) (he : d ≤ e) :
    (1/2 : ℝ≥0∞) * c + (1/2 : ℝ≥0∞) * d ≤ (Mix.average.{u}).binary t e := sorry
@[gen_rule] theorem le_average_threshold {d : Nat} {k : ℤ} {t e c c' : ℝ≥0∞} (hd : 0 < d)
    (h0 : 0 ≤ k) (hk : k ≤ d) (ht : c ≤ t) (he : c' ≤ e) :
    (k.toNat : ℝ≥0∞) / (d : ℝ≥0∞) * c + ((d - k.toNat : ℕ) : ℝ≥0∞) / (d : ℝ≥0∞) * c'
      ≤ (Mix.average.{u}).threshold d k t e := sorry
@[gen_rule] theorem le_average_index {γ : Type v} {l : List γ} {hne : l ≠ []} {F : γ → ℝ≥0∞}
    {cs : List ℝ≥0∞} (h : List.Forall₂ (fun c g => c ≤ F g) cs l) :
    cs.sum / (cs.length : ℝ≥0∞) ≤ (Mix.average.{u}).index l hne F := sorry
@[gen_branches]
inductive WeightedGE {γ : Type v} (F : γ → ℝ≥0∞) : List (Nat × ℝ≥0∞) → List (Nat × γ) → Prop
  | nil : WeightedGE F [] []
  | cons {w : Nat} {c : ℝ≥0∞} {g : γ} {cs gs} (h : c ≤ F g) (hs : WeightedGE F cs gs) :
      WeightedGE F ((w, c) :: cs) ((w, g) :: gs)
@[gen_rule] theorem le_average_select {γ : Type v} {l : List (Nat × γ)}
    {hpos : 0 < (l.map Prod.fst).sum} {F : γ → ℝ≥0∞} {d : ℝ≥0∞} {cs : List (Nat × ℝ≥0∞)}
    (h : WeightedGE F cs l) :
    (cs.map fun p => (p.1 : ℝ≥0∞) * p.2).sum / ((cs.map Prod.fst).sum : ℝ≥0∞)
      ≤ (Mix.average.{u}).select l hpos F d := sorry
@[gen_rule] theorem le_average_rangeInt {lo hi : ℤ} {h : lo ≤ hi} {F d : ℤ → ℝ≥0∞}
    (hF : ∀ x, lo ≤ x ∧ x ≤ hi → d x ≤ F x) :
    (∑ x ∈ Finset.Icc lo hi, d x) / (((hi - lo + 1).toNat : ℕ) : ℝ≥0∞)
      ≤ (Mix.average.{0}).rangeInt lo hi h F := sorry
end Mix

theorem SPMF.le_spec_of_le_mass {x : SPMF α} {p : α → ℝ≥0∞} {c d : ℝ≥0∞} (hx : c ≤ x.mass)
    (hp : ∀ a, p a = d) : c * d ≤ SPMF.expectObs.spec x p := by
  show c * d ≤ SPMF.expect x p
  rw [funext hp, SPMF.expect_const]; gcongr
theorem SPMF.le_spec_of_isPMF {x : SPMF α} {p : α → ℝ≥0∞} {d : ℝ≥0∞} (hx : SPMF.IsPMF x)
    (hp : ∀ a, p a = d) : 1 * d ≤ SPMF.expectObs.spec x p := SPMF.le_spec_of_le_mass hx.ge hp

open Basalt.Walk in
elab "mass_bound'" args:(" [" term,* "]")? : tactic => withMainContext do
  let extras : Array Term := match args with
    | some a => (a.raw[1].getSepArgs).map (⟨·⟩) | none => #[]
  let goal ← getMainGoal
  let ty ← whnfR (← goal.getType)
  let g := (← whnfR (ty.getArg! 3)).getArg! 1
  let gTy ← instantiateMVars (← inferType g)
  let one ← mkAppOptM ``SPMF.expect_one #[none, g]   -- expect g (fun _ => 1) = mass g
  let some (_, lhs, _) := (← inferType one).eq? | throwError "?"
  let spec := mkApp (← mkAppOptM ``Obs.spec #[none, none, none, none, none, none,
    some (mkConst ``SPMF.expectObs [← getDecLevel gTy]), none, some g]) (lhs.getArg! 2)
  let le := ty.appFn!.appFn!
  let bound ← mkFreshExprMVar (ty.getArg! 0)
  let structural ← mkFreshExprMVar (mkApp2 le bound spec)
  let rest ← walk extras structural.mvarId!
  let arith ← mkFreshExprMVar (mkApp2 le (ty.getArg! 2) (← instantiateMVars bound))
  goal.assign (← mkAppM ``le_of_le_of_eq #[← mkAppM ``le_trans #[arith, structural], one])
  replaceMainGoal (← (arith.mvarId! :: rest).mapM fun g => Basalt.ExpectBound.tidy g)

/-! ## Appendix D -/
section D
variable (rec : SPMF Nat) (c : ℝ≥0∞) (hrec : c ≤ rec.mass)
include hrec
example : 0 ≤ (pick (fun () => pure 0) (fun () => rec >>= fun n => pure (n + 1)) : SPMF Nat).mass := by
  mass_bound'
  trace_state
  all_goals sorry
example : 0 ≤ (coin (1/2) >>= fun b => if b then pure 0 else rec >>= fun n => pure (n + 1) : SPMF Nat).mass := by
  mass_bound'
  trace_state
  all_goals sorry
-- today:
example : 0 ≤ (coin (1/2) >>= fun b => if b then pure 0 else rec >>= fun n => pure (n + 1) : SPMF Nat).mass := by
  mass_bound
  trace_state
  all_goals sorry
end D

/-! ## Today's MassBound pins, by the generic path -/
example : (1 : ℝ≥0∞) ≤ (optionGen Nat.arbitrary : SPMF (Option Nat)).mass := by
  mass_bound'
  trace_state
  all_goals sorry
example : (1 : ℝ≥0∞) ≤
    (chooseNat 0 1 >>= fun x => if x = 0 then pure 0 else pure 1 : SPMF Nat).mass := by
  mass_bound'
  trace_state
  all_goals sorry
example (g : Nat → SPMF Nat) (c : Nat → ℝ≥0∞) (hrec : ∀ j, c j ≤ (g j).mass) (n : Nat) :
    0 ≤ (chooseNat 0 n (by omega) >>= g).mass := by
  mass_bound'
  trace_state
  all_goals sorry
