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

end Obs
