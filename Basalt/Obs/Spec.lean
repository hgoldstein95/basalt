/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt.RandomChoice
import Basalt.SPMF.Walk.Attr

/-!
# Specification Monads

The targets of an observation: continuation monads over an algebra `Ω` whose one operation, `Mix.mix`,
says what a uniform choice means in `Ω`. `WP m` transforms a postcondition on values; `WPC m`
transforms one that also sees the number of choices made.
-/

/-- What a uniform choice over `[lo, hi]` means in `Ω`, given what each outcome means. A structure
rather than a class, because `Prop` carries two. -/
structure Mix.{u, w} (Ω : Type w) where
  mix : (lo hi : Nat) → (ULift.{u} {x : Nat // lo ≤ x ∧ x ≤ hi} → Ω) → Ω

namespace Obs

/-- The entry of a weighted list that offset `n` falls in, or `d` past the end. -/
def selectD : List (Nat × β) → Nat → β → β
  | [], _, d => d
  | (k, x) :: xs, n, d => if n < k then x else selectD xs (n - k) d

theorem selectD_map (f : β → γ) (l : List (Nat × β)) (n : Nat) (d : β) :
    f (selectD l n d) = selectD (l.map fun p => (p.1, f p.2)) n (f d) := by
  induction l generalizing n with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨k, x⟩ := hd
    simp only [selectD, List.map_cons]
    split
    · rfl
    · exact ih _

theorem idx_lt {l : List γ} (hne : l ≠ []) {i : Nat} (h : 0 ≤ i ∧ i ≤ l.length - 1) :
    i < l.length := by
  have := List.length_pos_iff.mpr hne
  omega

end Obs

/-! ## Shapes of choice in an algebra -/

namespace Mix

variable {Ω : Type w} (m : Mix.{u} Ω)

/-- A binary choice. -/
def binary (t e : Ω) : Ω :=
  m.mix 0 1 fun a => if (a.down.val == 0) = true then t else e

/-- A choice among `d` outcomes, the first `k` of which mean `t`. -/
def threshold (d : Nat) (k : Int) (t e : Ω) : Ω :=
  m.mix 0 (d - 1) fun a => if (a.down.val : Int) < k then t else e

/-- A choice of a list entry. -/
def index (l : List γ) (hne : l ≠ []) (F : γ → Ω) : Ω :=
  m.mix 0 (l.length - 1) fun a => F (l[a.down.val]'(Obs.idx_lt hne a.down.property))

/-- A choice of a weighted list entry. -/
def select (l : List (Nat × γ)) (_hpos : 0 < (l.map Prod.fst).sum) (F : γ → Ω) (d : Ω) : Ω :=
  m.mix 0 ((l.map Prod.fst).sum - 1) fun a =>
    Obs.selectD (l.map fun p => (p.1, F p.2)) a.down.val d

/-- A choice from a range of integers. -/
def rangeInt (lo hi : Int) (_h : lo ≤ hi) (F : Int → Ω) : Ω :=
  m.mix 0 (hi - lo).toNat fun a => F (lo + (a.down.val : Int))

end Mix

/-! ## The same shapes in a specification monad -/

namespace Obs

open RandomChoice

variable {W : Type u → Type w} [Monad W] [RandomChoice W]

/-- `vectorOf` written with `Monad` operations only. -/
def replicateM (n : Nat) (w : W α) : W (List α) :=
  List.foldr (fun m acc => m >>= fun x => acc >>= fun xs => Pure.pure (x :: xs)) (Pure.pure [])
    (List.replicate n w)

/-- A uniform list entry, then `F`. -/
def index (l : List γ) (hne : l ≠ []) (F : γ → W α) : W α :=
  choose 0 (l.length - 1) (Nat.zero_le _) >>= fun a =>
    F (l[a.down.val]'(idx_lt hne a.down.property))

/-- A weighted list entry, then `F`; `d` past the end. -/
def select (l : List (Nat × γ)) (_hpos : 0 < (l.map Prod.fst).sum) (F : γ → W α) (d : W α) :
    W α :=
  choose 0 ((l.map Prod.fst).sum - 1) (Nat.zero_le _) >>= fun a =>
    selectD (l.map fun p => (p.1, F p.2)) a.down.val d

/-- A uniform integer in `[lo, hi]`, then `F`. -/
def rangeInt (lo hi : Int) (_h : lo ≤ hi) (F : Int → W α) : W α :=
  choose 0 (hi - lo).toNat (Nat.zero_le _) >>= fun a => F (lo + (a.down.val : Int))

end Obs

/-- A choice holds when every outcome does. -/
def Mix.demonic : Mix.{u} Prop where mix _ _ F := ∀ x, F x

/-- A choice holds when some outcome does. -/
def Mix.angelic : Mix.{u} Prop where mix _ _ F := ∃ x, F x

/-- Transformers from a postcondition on values to an `Ω`. The algebra is a parameter only to select
the `RandomChoice` instance. -/
def WP {Ω : Type w} (_m : Mix.{u} Ω) (α : Type u) : Type (max u w) := (α → Ω) → Ω

namespace WP

variable {Ω : Type w} {m : Mix.{u} Ω}

instance : Monad (WP m) where
  pure a := fun post => post a
  bind m k := fun post => m fun a => k a post

instance : LawfulMonad (WP m) := LawfulMonad.mk' _
  (id_map := fun _ => rfl) (pure_bind := fun _ _ => rfl) (bind_assoc := fun _ _ _ => rfl)

instance : RandomChoice (WP m) where
  choose lo hi _ := fun post => m.mix lo hi post

theorem choose_bind_apply {lo hi : Nat} {h : lo ≤ hi}
    (k : ULift.{u} {x : Nat // lo ≤ x ∧ x ≤ hi} → WP m α) (post : α → Ω) :
    (RandomChoice.choose lo hi h >>= k) post = m.mix lo hi fun a => k a post := rfl

theorem map_choose_apply {lo hi : Nat} {h : lo ≤ hi}
    (f : ULift.{u} {x : Nat // lo ≤ x ∧ x ≤ hi} → α) (post : α → Ω) :
    (f <$> RandomChoice.choose lo hi h : WP m α) post = m.mix lo hi fun a => post (f a) := rfl

theorem ite_apply {p : Prop} [Decidable p] (x y : WP m α) (post : α → Ω) :
    (if p then x else y) post = if p then x post else y post := by
  split <;> rfl

section shapes

open RandomChoice

@[spec_apply]
theorem pure_apply (a : α) (post : α → Ω) : (Pure.pure a : WP m α) post = post a := rfl

@[spec_apply]
theorem choose_apply {lo hi : Nat} {h : lo ≤ hi} (post : _ → Ω) :
    (choose lo hi h : WP m _) post = m.mix lo hi post := rfl

@[spec_apply]
theorem pick_apply (x y : Unit → WP m α) (post : α → Ω) :
    (pick x y) post = m.binary (x () post) (y () post) :=
  congrArg (m.mix 0 1) (funext fun _ => ite_apply _ _ _)

@[spec_apply]
theorem coin_apply {m : Mix.{0} Ω} (r : Rat) (post : Bool → Ω) :
    (coin r : WP m Bool) post = m.threshold r.den r.num (post true) (post false) :=
  congrArg (m.mix 0 (r.den - 1)) (funext fun _ => ite_apply _ _ _)

@[spec_apply]
theorem index_apply (l : List γ) (hne : l ≠ []) (F : γ → WP m α) (post : α → Ω) :
    (Obs.index l hne F) post = m.index l hne fun g => F g post := rfl

@[spec_apply]
theorem select_apply (l : List (Nat × γ)) (hpos : 0 < (l.map Prod.fst).sum) (F : γ → WP m α)
    (d : WP m α) (post : α → Ω) :
    (Obs.select l hpos F d) post = m.select l hpos (fun g => F g post) (d post) :=
  congrArg (m.mix 0 _) (funext fun a =>
    (Obs.selectD_map (fun w : WP m α => w post) _ _ _).trans (by rw [List.map_map]; rfl))

@[spec_apply]
theorem rangeInt_apply (lo hi : Int) (h : lo ≤ hi) (F : Int → WP m α) (post : α → Ω) :
    (Obs.rangeInt lo hi h F) post = m.rangeInt lo hi h fun x => F x post := rfl

end shapes

end WP

/-- Transformers from a postcondition on values and choice counts to an `Ω`. -/
def WPC {Ω : Type w} (_m : Mix.{u} Ω) (α : Type u) : Type (max u w) := (α → Nat → Ω) → Ω

namespace WPC

variable {Ω : Type w} {m : Mix.{u} Ω}

instance : Monad (WPC m) where
  pure a := fun post => post a 0
  bind m k := fun post => m fun a n => k a fun b n' => post b (n + n')

instance : LawfulMonad (WPC m) := LawfulMonad.mk' _
  (id_map := fun _ => rfl)
  (pure_bind := fun _ _ => by funext post; simp [bind, pure])
  (bind_assoc := fun _ _ _ => by funext post; simp [bind, Nat.add_assoc])

instance : RandomChoice (WPC m) where
  choose lo hi _ := fun post => m.mix lo hi fun a => post a 1

theorem choose_bind_apply {lo hi : Nat} {h : lo ≤ hi}
    (k : ULift.{u} {x : Nat // lo ≤ x ∧ x ≤ hi} → WPC m α) (post : α → Nat → Ω) :
    (RandomChoice.choose lo hi h >>= k) post
      = m.mix lo hi fun a => k a fun b n => post b (1 + n) := rfl

theorem map_choose_apply {lo hi : Nat} {h : lo ≤ hi}
    (f : ULift.{u} {x : Nat // lo ≤ x ∧ x ≤ hi} → α) (post : α → Nat → Ω) :
    (f <$> RandomChoice.choose lo hi h : WPC m α) post = m.mix lo hi fun a => post (f a) 1 := rfl

theorem ite_apply {p : Prop} [Decidable p] (x y : WPC m α) (post : α → Nat → Ω) :
    (if p then x else y) post = if p then x post else y post := by
  split <;> rfl

section shapes

open RandomChoice

@[spec_apply]
theorem pure_apply (a : α) (post : α → Nat → Ω) : (Pure.pure a : WPC m α) post = post a 0 := rfl

@[spec_apply]
theorem choose_apply {lo hi : Nat} {h : lo ≤ hi} (post : _ → Nat → Ω) :
    (choose lo hi h : WPC m _) post = m.mix lo hi fun a => post a 1 := rfl

@[spec_apply]
theorem pick_apply (x y : Unit → WPC m α) (post : α → Nat → Ω) :
    (pick x y) post
      = m.binary (x () fun b n => post b (1 + n)) (y () fun b n => post b (1 + n)) :=
  congrArg (m.mix 0 1) (funext fun _ => ite_apply _ _ _)

@[spec_apply]
theorem coin_apply {m : Mix.{0} Ω} (r : Rat) (post : Bool → Nat → Ω) :
    (coin r : WPC m Bool) post = m.threshold r.den r.num (post true 1) (post false 1) :=
  congrArg (m.mix 0 (r.den - 1)) (funext fun _ => ite_apply _ _ _)

@[spec_apply]
theorem index_apply (l : List γ) (hne : l ≠ []) (F : γ → WPC m α) (post : α → Nat → Ω) :
    (Obs.index l hne F) post = m.index l hne fun g => F g fun b n => post b (1 + n) := rfl

@[spec_apply]
theorem select_apply (l : List (Nat × γ)) (hpos : 0 < (l.map Prod.fst).sum) (F : γ → WPC m α)
    (d : WPC m α) (post : α → Nat → Ω) :
    (Obs.select l hpos F d) post
      = m.select l hpos (fun g => F g fun b n => post b (1 + n))
          (d fun b n => post b (1 + n)) :=
  congrArg (m.mix 0 _) (funext fun a =>
    (Obs.selectD_map (fun w : WPC m α => w fun b n => post b (1 + n)) _ _ _).trans
      (by rw [List.map_map]; rfl))

@[spec_apply]
theorem rangeInt_apply (lo hi : Int) (h : lo ≤ hi) (F : Int → WPC m α) (post : α → Nat → Ω) :
    (Obs.rangeInt lo hi h F) post
      = m.rangeInt lo hi h fun x => F x fun b n => post b (1 + n) := rfl

end shapes

end WPC
