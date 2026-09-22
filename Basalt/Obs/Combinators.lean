/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt.Combinators
import Basalt.Obs.Basic
import Basalt.Obs.Spec

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

omit [LawfulMonad G] [LawfulMonad W] in
theorem map_frequencyAux (gs : List (Nat × (Unit → G α))) (n : Nat)
    (h : n < (gs.map Prod.fst).sum) (d : W α) :
    O.spec (frequencyAux gs n h)
      = selectD (gs.map fun p => (p.1, O.spec (p.2 ()))) n d := by
  induction gs generalizing n with
  | nil => simp at h
  | cons hd tl ih =>
    obtain ⟨k, x⟩ := hd
    simp only [frequencyAux, selectD, List.map_cons]
    split
    · rfl
    · exact ih _ _

/-- The draw is below the total weight, so neither `frequency`'s `default` branch nor `selectD`'s
`d` is reached, and no law about `default` is needed. -/
@[gen_map]
theorem map_frequency (gs : List (Nat × (Unit → G α))) (h : 0 < (gs.map Prod.fst).sum) :
    O.spec (frequency gs h) = select gs h (fun g => O.spec (g ())) (O.spec default) := by
  unfold frequency select
  rw [O.map_bind, O.map_chooseNat, bind_map_left]
  congr 1
  funext ⟨i, h1, h2⟩
  have hi : i < (gs.map Prod.fst).sum := by omega
  simp only [dif_pos hi]
  exact O.map_frequencyAux gs i hi _

/-- `oneOf` is `Obs.index` at every universe: unlike the other combinators it draws no `Nat`, so
neither the generator's element type nor its laws are confined to `Type`. -/
@[gen_map]
theorem map_oneOf {G : Type u → Type v} {W : Type u → Type w} [Gen G] [Monad W] [RandomChoice W]
    (O : Obs G W) {α : Type u} (gs : List (Unit → G α)) (hne : gs ≠ []) :
    O.spec (oneOf gs hne) = index gs hne fun g => O.spec (g ()) := by
  unfold oneOf index
  rw [O.map_bind, O.map_choose]

end Obs
