/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt.Combinators
import Basalt.Sized

/-!
# Combinators at a Size

Lemmas to show how a combinator using a generator `WithSize G` unfolds to a `G` when evaluated at a
size.

TODO: Similar to my comment in `QuickCheck.lean`, I wish we could do this with more generic theory.
(Especially because most of these are `rfl`.) Also, I don't like that these are separated from the
theorems about the core QuickCheck combinators, although maybe that's unavoidable until we integrate
them better into the library.
-/

namespace WithSize

variable {G : Type → Type} [Gen G] {α β : Type} (n : Nat)

@[size_erasure]
theorem pure_apply (a : α) : (Pure.pure a : WithSize G α) n = Pure.pure a := rfl

@[size_erasure]
theorem bind_apply (x : WithSize G α) (k : α → WithSize G β) :
    (x >>= k) n = x n >>= fun a => k a n := rfl

@[size_erasure]
theorem map_apply (f : α → β) (x : WithSize G α) : (f <$> x) n = f <$> x n := rfl

@[size_erasure]
theorem choose_apply (lo hi : Nat) (h : lo ≤ hi) :
    (RandomChoice.choose lo hi h : WithSize G _) n = RandomChoice.choose lo hi h := rfl

@[size_erasure]
theorem default_apply : (default : WithSize G α) n = default := rfl

omit [Gen G] in
@[size_erasure]
theorem ite_apply (c : Prop) [Decidable c] (x y : WithSize G α) :
    (if c then x else y) n = if c then x n else y n := by
  split <;> rfl

omit [Gen G] in
@[size_erasure]
theorem dite_apply (c : Prop) [Decidable c] (x : c → WithSize G α) (y : ¬c → WithSize G α) :
    (if h : c then x h else y h) n = if h : c then x h n else y h n := by
  split <;> rfl

@[size_erasure]
theorem sized_apply (f : Nat → WithSize G α) : (Sized.sized f : WithSize G α) n = f n n := rfl

@[size_erasure]
theorem resize_apply (m : Nat) (g : WithSize G α) : (Sized.resize m g : WithSize G α) n = g m :=
  rfl

@[size_erasure]
theorem getSize_apply : (getSize : WithSize G Nat) n = Pure.pure n := rfl

@[size_erasure]
theorem chooseNat_apply (lo hi : Nat) (h : lo ≤ hi) :
    (chooseNat lo hi h : WithSize G Nat) n = chooseNat lo hi h := rfl

@[size_erasure]
theorem chooseInt_apply (lo hi : Int) (h : lo ≤ hi) :
    (chooseInt lo hi h : WithSize G Int) n = chooseInt lo hi h := rfl

@[size_erasure]
theorem coin_apply (r : Rat) : (RandomChoice.coin r : WithSize G Bool) n = RandomChoice.coin r := by
  unfold RandomChoice.coin
  show (_ : G _) >>= _ = _ >>= _
  congr 1
  funext a
  exact ite_apply n _ _ _

@[size_erasure]
theorem elements_apply (xs : List α) (hne : xs ≠ []) :
    (elements xs hne : WithSize G α) n = elements xs hne := by
  unfold elements
  show (_ : G _) >>= _ = _ >>= _
  congr 1
  funext ⟨i, _, _⟩
  rfl

theorem oneOfChain_apply (gs : List (Unit → WithSize G α)) (k i : Nat) :
    oneOfChain gs k i n = oneOfChain (gs.map fun g u => g u n) k i := by
  induction gs generalizing k with
  | nil => rfl
  | cons g gs ih =>
    cases gs with
    | nil => rfl
    | cons g' gs' =>
      rw [oneOfChain.eq_3 _ _ _ _ (List.cons_ne_nil _ _), List.map_cons, List.map_cons,
        oneOfChain.eq_3 _ _ _ _ (List.cons_ne_nil _ _), ite_apply, ih]
      rfl

/-- The branches of `gs`, each evaluated at `n`. -/
@[size_erasure]
theorem oneOf_apply (gs : List (Unit → WithSize G α)) (hne : gs ≠ []) :
    (oneOf gs hne : WithSize G α) n
      = oneOf (gs.map fun g u => g u n) (by simpa using hne) := by
  rw [oneOf_eq_chain gs hne (gs.length - 1) rfl,
    oneOf_eq_chain (gs.map fun g u => g u n) _ (gs.length - 1) (by simp), bind_apply]
  congr 1
  funext i
  exact oneOfChain_apply n gs 0 _

@[size_erasure]
theorem oneOfWith_apply (gs : List (Unit → WithSize G α)) (hne : gs ≠ []) (impl : WithSize G α)
    (h : impl = oneOf gs hne) :
    (oneOfWith gs hne impl h) n = oneOf (gs.map fun g u => g u n) (by simpa using hne) := by
  rw [oneOfWith_eq, oneOf_apply]

theorem frequencyChain_apply (gs : List (Nat × (Unit → WithSize G α))) (acc i : Nat) :
    frequencyChain gs acc i n = frequencyChain (gs.map fun p => (p.1, fun u => p.2 u n)) acc i := by
  induction gs generalizing acc with
  | nil => rfl
  | cons p gs ih =>
    simp only [frequencyChain, List.map_cons, ite_apply, ih]

/-- The branches of `gs`, each evaluated at `n`, at their weights. -/
@[size_erasure]
theorem frequency_apply (gs : List (Nat × (Unit → WithSize G α)))
    (h : 0 < (gs.map Prod.fst).sum) :
    (frequency gs h : WithSize G α) n
      = frequency (gs.map fun p => (p.1, fun u => p.2 u n))
          (by simpa [Function.comp_def] using h) := by
  rw [frequency_eq_chain gs h ((gs.map Prod.fst).sum - 1) rfl,
    frequency_eq_chain (gs.map fun p => (p.1, fun u => p.2 u n)) _ ((gs.map Prod.fst).sum - 1)
      (by simp [Function.comp_def]), bind_apply, chooseNat_apply]
  congr 1
  funext i
  exact frequencyChain_apply n gs 0 _

@[size_erasure]
theorem frequencyWith_apply (gs : List (Nat × (Unit → WithSize G α)))
    (h : 0 < (gs.map Prod.fst).sum) (impl : WithSize G α) (he : impl = frequency gs h) :
    (frequencyWith gs h impl he) n
      = frequency (gs.map fun p => (p.1, fun u => p.2 u n))
          (by simpa [Function.comp_def] using h) := by
  rw [frequencyWith_eq, frequency_apply]

@[size_erasure]
theorem vectorOf_apply (k : Nat) (g : WithSize G α) :
    (vectorOf k g : WithSize G (List α)) n = vectorOf k (g n) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [vectorOf_succ, vectorOf_succ, ← ih]; rfl

@[size_erasure]
theorem listOfMaxLength_apply (k : Nat) (g : WithSize G α) :
    (listOfMaxLength k g : WithSize G (List α)) n = listOfMaxLength k (g n) := by
  unfold listOfMaxLength
  show (_ : G _) >>= _ = _ >>= _
  congr 1
  funext ⟨i, _, _⟩
  exact vectorOf_apply n i g

@[size_erasure]
theorem permutationOf_apply (xs : List α) :
    (permutationOf xs : WithSize G { ys // xs.Perm ys }) n = permutationOf xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    unfold permutationOf
    show (_ : G _) >>= _ = _ >>= _
    rw [ih]
    congr 1
    funext ⟨ys, h⟩
    show (_ : G _) >>= _ = _ >>= _
    congr 1
    funext ⟨i, _, _⟩
    rfl

end WithSize
