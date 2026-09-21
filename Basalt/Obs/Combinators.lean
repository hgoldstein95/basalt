/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt.Obs.Basic
import Basalt.Obs.Spec
import Basalt.Combinators

/-!
# Observations Commute with the Combinators

One `map_X` lemma per non-recursive combinator: what an observation of `X` is, written with the
specification monad's `Monad` and `RandomChoice` operations only, so that it need not be a `Gen`.
Each right-hand side is one shape of choice (`Basalt/Obs/Spec.lean`), which is what a presentation
lemma or a walker rule of an algebra reads.
-/

open RandomChoice

namespace Obs

variable {G : Type → Type v} {W : Type → Type w}
  [Gen G] [LawfulMonad G] [Monad W] [RandomChoice W] [LawfulMonad W] (O : Obs G W)

theorem map_chooseNat (lo hi : Nat) (h : lo ≤ hi) :
    O.spec (chooseNat lo hi h) = (·.down.val) <$> choose lo hi h := by
  simp only [chooseNat, O.map_map, O.map_choose]

@[gen_map]
theorem map_chooseInt (lo hi : Int) (h : lo ≤ hi) :
    O.spec (chooseInt lo hi h) = rangeInt lo hi h Pure.pure := by
  unfold chooseInt rangeInt
  rw [O.map_bind, O.map_chooseNat, bind_map_left]
  simp only [O.map_pure]

@[gen_map]
theorem map_elements (xs : List α) (hne : xs ≠ []) :
    O.spec (elements xs hne) = element xs hne := by
  unfold elements element index
  rw [O.map_bind, O.map_map, O.map_choose, bind_map_left]
  congr 1
  funext ⟨i, h1, h2⟩
  exact O.map_pure _

theorem map_oneOfAux (l : List (Unit → G α)) (n : Nat) (hlt : ∀ i, i ≤ n → i < l.length) :
    O.spec (Helpers.oneOfAux l n hlt)
      = choose 0 n (Nat.zero_le _) >>= fun a =>
          O.spec ((l[a.down.val]'(hlt _ a.down.property.2)) ()) := by
  unfold Helpers.oneOfAux
  rw [O.map_bind, O.map_map, O.map_choose, bind_map_left]
  congr 1
  funext ⟨i, h1, h2⟩
  rfl

@[gen_map]
theorem map_oneOf (gs : List (Unit → G α)) (hne : gs ≠ []) :
    O.spec (oneOf gs hne) = index gs hne fun g => O.spec (g ()) :=
  O.map_oneOfAux gs _ _

omit [LawfulMonad G] [LawfulMonad W] in
theorem map_frequencySelect (gs : List (Nat × (Unit → G α))) (n : Nat)
    (h : n < (gs.map Prod.fst).sum) (d : W α) :
    O.spec (Helpers.frequencySelect gs n h)
      = selectD (gs.map fun p => (p.1, O.spec (p.2 ()))) n d := by
  induction gs generalizing n with
  | nil => simp at h
  | cons hd tl ih =>
    obtain ⟨k, x⟩ := hd
    simp only [Helpers.frequencySelect, selectD, List.map_cons]
    split
    · rfl
    · exact ih _ _

/-- The draw is below the total weight, so neither `frequencyAux`'s `default` branch nor `selectD`'s
`d` is reached, and no law about `default` is needed. -/
theorem map_frequencyAux (gs : List (Nat × (Unit → G α))) (total : Nat)
    (htotal : total = (gs.map Prod.fst).sum) (hpos : 0 < total) (d : W α) :
    O.spec (Helpers.frequencyAux gs total htotal)
      = choose 0 (total - 1) (Nat.zero_le _) >>= fun a =>
          selectD (gs.map fun p => (p.1, O.spec (p.2 ()))) a.down.val d := by
  unfold Helpers.frequencyAux
  rw [O.map_bind, O.map_map, O.map_choose, bind_map_left]
  congr 1
  funext ⟨i, h1, h2⟩
  have hi : i < total := by omega
  simp only [dif_pos hi]
  exact O.map_frequencySelect gs i (by omega) d

@[gen_map]
theorem map_frequency (gs : List (Nat × (Unit → G α))) (h : 0 < (gs.map Prod.fst).sum) :
    O.spec (frequency gs h) = select gs h (fun g => O.spec (g ())) (O.spec default) :=
  O.map_frequencyAux gs _ rfl h _

omit [LawfulMonad G] [LawfulMonad W] in
theorem map_vectorOf (n : Nat) (g : G α) : O.spec (vectorOf n g) = replicateM n (O.spec g) := by
  induction n with
  | zero => exact O.map_pure _
  | succ n ih =>
    rw [vectorOf_succ]
    simp only [O.map_bind, O.map_pure, ih]
    rfl

theorem map_listOfMaxLength (n : Nat) (g : G α) :
    O.spec (listOfMaxLength n g)
      = choose 0 n (Nat.zero_le _) >>= fun a => replicateM a.down.val (O.spec g) := by
  unfold listOfMaxLength
  rw [O.map_bind, O.map_map, O.map_choose, bind_map_left]
  congr 1
  funext ⟨k, _⟩
  exact O.map_vectorOf k g

theorem map_biasedOptionGen (r : Rat) (g : G α) :
    O.spec (biasedOptionGen r g)
      = coin r >>= fun b => if b = true then some <$> O.spec g else Pure.pure none := by
  simp only [biasedOptionGen, O.map_bind, O.map_coin, O.map_ite, O.map_pure, O.map_map,
    bind_pure_comp]

theorem map_optionGen (g : G α) :
    O.spec (optionGen g)
      = coin (1 / 2) >>= fun b => if b = true then some <$> O.spec g else Pure.pure none :=
  O.map_biasedOptionGen _ g

/-! ## Into a generator monad

When the target is itself a `Gen`, the right-hand side folds back into the combinator: `O.map_X`
forwards, then `(Obs.refl W).map_X` backwards. -/

section gen

variable {G W : Type → Type v} [Gen G] [LawfulMonad G] [Gen W] [LawfulMonad W] (O : Obs G W)

theorem spec_chooseNat (lo hi : Nat) (h : lo ≤ hi) :
    O.spec (chooseNat lo hi h) = chooseNat lo hi h :=
  O.map_chooseNat lo hi h

theorem spec_chooseInt (lo hi : Int) (h : lo ≤ hi) :
    O.spec (chooseInt lo hi h) = chooseInt lo hi h :=
  (O.map_chooseInt lo hi h).trans ((refl W).map_chooseInt lo hi h).symm

theorem spec_elements (xs : List α) (hne : xs ≠ []) : O.spec (elements xs hne) = elements xs hne :=
  (O.map_elements xs hne).trans ((refl W).map_elements xs hne).symm

theorem spec_oneOf (gs : List (Unit → G α)) (hne : gs ≠ []) :
    O.spec (oneOf gs hne) = oneOf (gs.map fun g u => O.spec (g u)) (by simpa using hne) := by
  have aux : ∀ n hlt hlt', O.spec (Helpers.oneOfAux gs n hlt)
      = Helpers.oneOfAux (gs.map fun g u => O.spec (g u)) n hlt' := by
    intro n hlt hlt'
    refine (O.map_oneOfAux gs n hlt).trans
      (Eq.trans ?_ ((refl W).map_oneOfAux _ n hlt').symm)
    congr 1
    funext a
    simp [refl]
  unfold oneOf
  rw [aux _ _ (by simpa using fun i hi => idx_lt hne ⟨Nat.zero_le i, hi⟩)]
  congr 1
  simp

theorem spec_frequency (gs : List (Nat × (Unit → G α))) (h : 0 < (gs.map Prod.fst).sum) :
    O.spec (frequency gs h)
      = frequency (gs.map fun p => (p.1, fun u => O.spec (p.2 u)))
          (by simpa [Function.comp_def] using h) := by
  have hsum : (gs.map Prod.fst).sum
      = ((gs.map fun p => (p.1, fun u => O.spec (p.2 u))).map Prod.fst).sum := by
    simp [Function.comp_def]
  have aux : ∀ total h1 h2, 0 < total → O.spec (Helpers.frequencyAux gs total h1)
      = Helpers.frequencyAux (gs.map fun p => (p.1, fun u => O.spec (p.2 u))) total h2 := by
    intro total h1 h2 hpos
    refine (O.map_frequencyAux gs total h1 hpos default).trans
      (Eq.trans ?_ ((refl W).map_frequencyAux _ total h2 hpos default).symm)
    simp [List.map_map, Function.comp_def, refl]
  unfold frequency
  rw [aux _ rfl hsum h]
  congr 1

omit [LawfulMonad G] [LawfulMonad W] in
theorem spec_vectorOf (n : Nat) (g : G α) : O.spec (vectorOf n g) = vectorOf n (O.spec g) :=
  (O.map_vectorOf n g).trans ((refl W).map_vectorOf n (O.spec g)).symm

theorem spec_listOfMaxLength (n : Nat) (g : G α) :
    O.spec (listOfMaxLength n g) = listOfMaxLength n (O.spec g) :=
  (O.map_listOfMaxLength n g).trans ((refl W).map_listOfMaxLength n (O.spec g)).symm

theorem spec_biasedOptionGen (r : Rat) (g : G α) :
    O.spec (biasedOptionGen r g) = biasedOptionGen r (O.spec g) :=
  (O.map_biasedOptionGen r g).trans ((refl W).map_biasedOptionGen r (O.spec g)).symm

theorem spec_optionGen (g : G α) : O.spec (optionGen g) = optionGen (O.spec g) :=
  O.spec_biasedOptionGen _ g

end gen

end Obs
