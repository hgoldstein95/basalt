/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Mathlib.Order.Basic
import Basalt.Obs.Combinators

/-!
# Observations into an Ordered Algebra

The walker's rules for a bound `O.spec g post ≤ b` or `b ≤ O.spec g post`, stated once for every
observation that is monotone in its postcondition: the postcondition is given, and the bound is what
the rule computes. A combinator with a `@[gen_map]` lemma needs no rule here; its bound is its
shape's, in the algebra.
-/

/-- Branch-wise bounds for a weighted choice, each paired with its weight, so that the bound computed
from them is free of the branches themselves (which under a `dite` carry the branch's proof). `r`
is the direction. -/
@[gen_branches]
inductive Mix.Weighted {γ : Type v} {Ω : Type w} (r : Ω → Ω → Prop) (F : γ → Ω) :
    List (Nat × Ω) → List (Nat × γ) → Prop
  | nil : Weighted r F [] []
  | cons {w : Nat} {c : Ω} {g : γ} {cs gs} (h : r (F g) c) (hs : Weighted r F cs gs) :
      Weighted r F ((w, c) :: cs) ((w, g) :: gs)

theorem Mix.Weighted.weights {γ : Type v} {Ω : Type w} {r : Ω → Ω → Prop} {F : γ → Ω} {cs gs}
    (h : Weighted r F cs gs) : (cs.map Prod.fst).sum = (gs.map Prod.fst).sum := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simpa using ih

namespace Obs

variable {G : Type u → Type v} {Ω : Type w} [Preorder Ω] {m : Mix.{u} Ω} [Monad G] [RandomChoice G]

/-- A larger postcondition has a larger observation. -/
class Monotone (O : Obs G (WP m)) : Prop where
  spec_mono : ∀ {α} (g : G α) {p q : α → Ω}, (∀ a, p a ≤ q a) → O.spec g p ≤ O.spec g q

@[inherit_doc Monotone]
class MonotoneC (O : Obs G (WPC m)) : Prop where
  spec_mono : ∀ {α} (g : G α) {p q : α → Nat → Ω}, (∀ a n, p a n ≤ q a n) → O.spec g p ≤ O.spec g q

section WP

variable {O : Obs G (WP m)}

@[gen_rule]
theorem spec_pure_le {a : α} {post : α → Ω} : O.spec (Pure.pure a) post ≤ post a :=
  (congrFun (O.map_pure a) post).le

/-- The continuation is walked first: its bound is the draw's postcondition. -/
@[gen_rule]
theorem spec_bind_le [O.Monotone] {x : G α} {k : α → G β} {post : β → Ω} {h : α → Ω} {b : Ω}
    (hk : ∀ a, O.spec (k a) post ≤ h a) (hx : O.spec x h ≤ b) : O.spec (x >>= k) post ≤ b :=
  (congrFun (O.map_bind x k) post).le.trans ((Monotone.spec_mono x hk).trans hx)

@[gen_rule]
theorem spec_map_le [LawfulMonad G] {x : G α} {f : α → β} {post : β → Ω} {b : Ω}
    (hx : O.spec x (fun a => post (f a)) ≤ b) : O.spec (f <$> x) post ≤ b :=
  (congrFun (O.map_map f x) post).le.trans hx

@[gen_rule]
theorem spec_ite_le {p : Prop} [Decidable p] {x y : G α} {post : α → Ω} {c d : Ω}
    (hx : p → O.spec x post ≤ c) (hy : ¬p → O.spec y post ≤ d) :
    O.spec (if p then x else y) post ≤ if p then c else d := by
  split <;> simp_all

/-- The bound may mention the branch's proof. -/
@[gen_rule]
theorem spec_dite_le {p : Prop} [Decidable p] {x : p → G α} {y : ¬p → G α} {post : α → Ω}
    {c : p → Ω} {d : ¬p → Ω} (hx : ∀ h, O.spec (x h) post ≤ c h)
    (hy : ∀ h, O.spec (y h) post ≤ d h) :
    O.spec (if h : p then x h else y h) post ≤ if h : p then c h else d h := by
  split <;> simp_all

theorem spec_le_of_map {g : G α} {w : WP m α} {post : α → Ω} {b : Ω}
    (h : O.spec g = w) (hw : w post ≤ b) : O.spec g post ≤ b :=
  (congrFun h post).le.trans hw

/-! ## Lower bounds -/

@[gen_rule]
theorem le_spec_pure {a : α} {post : α → Ω} {b : Ω} (hb : b ≤ post a) :
    b ≤ O.spec (Pure.pure a) post := hb.trans (congrFun (O.map_pure a) post).ge

@[gen_rule, inherit_doc spec_bind_le]
theorem le_spec_bind [O.Monotone] {x : G α} {k : α → G β} {post : β → Ω} {h : α → Ω} {b : Ω}
    (hk : ∀ a, h a ≤ O.spec (k a) post) (hx : b ≤ O.spec x h) : b ≤ O.spec (x >>= k) post :=
  (hx.trans (Monotone.spec_mono x hk)).trans (congrFun (O.map_bind x k) post).ge

@[gen_rule]
theorem le_spec_map [LawfulMonad G] {x : G α} {f : α → β} {post : β → Ω} {b : Ω}
    (hx : b ≤ O.spec x (fun a => post (f a))) : b ≤ O.spec (f <$> x) post :=
  hx.trans (congrFun (O.map_map f x) post).ge

@[gen_rule]
theorem le_spec_ite {p : Prop} [Decidable p] {x y : G α} {post : α → Ω} {c d : Ω}
    (hx : p → c ≤ O.spec x post) (hy : ¬p → d ≤ O.spec y post) :
    (if p then c else d) ≤ O.spec (if p then x else y) post := by
  split <;> simp_all

@[gen_rule, inherit_doc spec_dite_le]
theorem le_spec_dite {p : Prop} [Decidable p] {x : p → G α} {y : ¬p → G α} {post : α → Ω}
    {c : p → Ω} {d : ¬p → Ω} (hx : ∀ h, c h ≤ O.spec (x h) post)
    (hy : ∀ h, d h ≤ O.spec (y h) post) :
    (if h : p then c h else d h) ≤ O.spec (if h : p then x h else y h) post := by
  split <;> simp_all

theorem le_spec_of_map {g : G α} {w : WP m α} {post : α → Ω} {b : Ω}
    (h : O.spec g = w) (hw : b ≤ w post) : b ≤ O.spec g post :=
  hw.trans (congrFun h post).ge

end WP

section WPC

variable {O : Obs G (WPC m)}

@[gen_rule]
theorem specC_pure_le {a : α} {post : α → Nat → Ω} : O.spec (Pure.pure a) post ≤ post a 0 :=
  (congrFun (O.map_pure a) post).le

@[gen_rule, inherit_doc spec_bind_le]
theorem specC_bind_le [O.MonotoneC] {x : G α} {k : α → G β} {post : β → Nat → Ω}
    {h : α → Nat → Ω} {b : Ω}
    (hk : ∀ a n, O.spec (k a) (fun b n' => post b (n + n')) ≤ h a n) (hx : O.spec x h ≤ b) :
    O.spec (x >>= k) post ≤ b :=
  (congrFun (O.map_bind x k) post).le.trans ((MonotoneC.spec_mono x hk).trans hx)

@[gen_rule]
theorem specC_map_le [LawfulMonad G] {x : G α} {f : α → β} {post : β → Nat → Ω} {b : Ω}
    (hx : O.spec x (fun a n => post (f a) n) ≤ b) : O.spec (f <$> x) post ≤ b :=
  (congrFun (O.map_map f x) post).le.trans hx

@[gen_rule]
theorem specC_ite_le {p : Prop} [Decidable p] {x y : G α} {post : α → Nat → Ω} {c d : Ω}
    (hx : p → O.spec x post ≤ c) (hy : ¬p → O.spec y post ≤ d) :
    O.spec (if p then x else y) post ≤ if p then c else d := by
  split <;> simp_all

/-- The bound may mention the branch's proof. -/
@[gen_rule]
theorem specC_dite_le {p : Prop} [Decidable p] {x : p → G α} {y : ¬p → G α} {post : α → Nat → Ω}
    {c : p → Ω} {d : ¬p → Ω} (hx : ∀ h, O.spec (x h) post ≤ c h)
    (hy : ∀ h, O.spec (y h) post ≤ d h) :
    O.spec (if h : p then x h else y h) post ≤ if h : p then c h else d h := by
  split <;> simp_all

theorem specC_le_of_map {g : G α} {w : WPC m α} {post : α → Nat → Ω} {b : Ω}
    (h : O.spec g = w) (hw : w post ≤ b) : O.spec g post ≤ b :=
  (congrFun h post).le.trans hw

/-! ## Lower bounds -/

@[gen_rule]
theorem le_specC_pure {a : α} {post : α → Nat → Ω} {b : Ω} (hb : b ≤ post a 0) :
    b ≤ O.spec (Pure.pure a) post := hb.trans (congrFun (O.map_pure a) post).ge

@[gen_rule, inherit_doc spec_bind_le]
theorem le_specC_bind [O.MonotoneC] {x : G α} {k : α → G β} {post : β → Nat → Ω}
    {h : α → Nat → Ω} {b : Ω}
    (hk : ∀ a n, h a n ≤ O.spec (k a) (fun b n' => post b (n + n'))) (hx : b ≤ O.spec x h) :
    b ≤ O.spec (x >>= k) post :=
  (hx.trans (MonotoneC.spec_mono x hk)).trans (congrFun (O.map_bind x k) post).ge

@[gen_rule]
theorem le_specC_map [LawfulMonad G] {x : G α} {f : α → β} {post : β → Nat → Ω} {b : Ω}
    (hx : b ≤ O.spec x (fun a n => post (f a) n)) : b ≤ O.spec (f <$> x) post :=
  hx.trans (congrFun (O.map_map f x) post).ge

@[gen_rule]
theorem le_specC_ite {p : Prop} [Decidable p] {x y : G α} {post : α → Nat → Ω} {c d : Ω}
    (hx : p → c ≤ O.spec x post) (hy : ¬p → d ≤ O.spec y post) :
    (if p then c else d) ≤ O.spec (if p then x else y) post := by
  split <;> simp_all

@[gen_rule, inherit_doc spec_dite_le]
theorem le_specC_dite {p : Prop} [Decidable p] {x : p → G α} {y : ¬p → G α}
    {post : α → Nat → Ω} {c : p → Ω} {d : ¬p → Ω} (hx : ∀ h, c h ≤ O.spec (x h) post)
    (hy : ∀ h, d h ≤ O.spec (y h) post) :
    (if h : p then c h else d h) ≤ O.spec (if h : p then x h else y h) post := by
  split <;> simp_all

theorem le_specC_of_map {g : G α} {w : WPC m α} {post : α → Nat → Ω} {b : Ω}
    (h : O.spec g = w) (hw : b ≤ w post) : b ≤ O.spec g post :=
  hw.trans (congrFun h post).ge

end WPC

end Obs
