/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
module

public import Basalt.Combinators
public import Basalt.Obs.Basic
public import Basalt.Obs.Spec
public import Basalt.Walk.Attr

/-!
# Observations Commute with the Combinators
-/

@[expose] public section

open RandomChoice

namespace Obs

attribute [gen_map] map_choose map_coin

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

omit [Gen G] [LawfulMonad G] [LawfulMonad W] in
/-- Two draws below bounds that are equal but written differently agree where their continuations
do. -/
theorem choose_bind_congr {n n' : Nat} (hn : n = n') {f : ULift {x : Nat // 0 ≤ x ∧ x ≤ n} → W α}
    {f' : ULift {x : Nat // 0 ≤ x ∧ x ≤ n'} → W α}
    (hf : ∀ (k : Nat) (h : k ≤ n) (h' : k ≤ n'), f ⟨k, Nat.zero_le _, h⟩ = f' ⟨k, Nat.zero_le _, h'⟩) :
    choose 0 n (Nat.zero_le _) >>= f = choose 0 n' (Nat.zero_le _) >>= f' := by
  subst hn
  congr 1
  funext ⟨k, _, h⟩
  exact hf k h h

/-- `pick`'s total is the list's total weight, from `j` on. -/
theorem totalFrom_eq {β : Type u} (l : List (Nat × β)) {n : Nat} (hn : l.length = n)
    (w : Fin n → Nat) (hw : ∀ i : Fin n, w i = (l[i.val]'(by rw [hn]; exact i.isLt)).1) (j : Nat) :
    totalFrom w j = ((l.drop j).map Prod.fst).sum := by
  rw [totalFrom]
  by_cases hj : j < n
  · rw [dite_eq_left hj, List.drop_eq_getElem_cons (by omega), List.map_cons, List.sum_cons,
      hw ⟨j, hj⟩, totalFrom_eq l hn w hw (j + 1)]
  · rw [dite_eq_right hj, List.drop_of_length_le (by omega)]
    rfl
termination_by n - j

/-- `pick`'s scan finds the entry `selectD` does, from `j` on. -/
theorem selectD_drop_eq {β : Type u} (l : List (Nat × β)) (d : β) {n : Nat} (hn : l.length = n)
    (w : Fin n → Nat) (hw : ∀ i : Fin n, w i = (l[i.val]'(by rw [hn]; exact i.isLt)).1)
    (k j : Nat) (hk : k < totalFrom w j) :
    selectD (l.drop j) k d = (l.getD (scanFrom w k j) (0, d)).2 := by
  rw [totalFrom] at hk
  by_cases hj : j < n
  · rw [dite_eq_left hj] at hk
    rw [List.drop_eq_getElem_cons (by omega), selectD, scanFrom, dite_eq_left hj, ← hw ⟨j, hj⟩]
    by_cases hlt : k < w ⟨j, hj⟩
    · rw [ite_eq_left hlt, ite_eq_left hlt, ← List.getElem_eq_getD]
    · rw [ite_eq_right hlt, ite_eq_right hlt]
      exact selectD_drop_eq l d hn w hw _ (j + 1) (by omega)
  · rw [dite_eq_right hj] at hk
    omega
termination_by n - j

omit [LawfulMonad G] in
/-- The draw is below the total weight, so `selectD`'s `d` is not reached, and no law about
`default` is needed. -/
@[gen_map]
theorem map_frequency [LawfulPick G] [LawfulPick W] (gs : List (Nat × (Unit → G α)))
    (h : 0 < (gs.map Prod.fst).sum) :
    O.spec (frequency gs h) = select gs h (fun g => O.spec (g ())) (O.spec default) := by
  have htot := totalFrom_eq gs rfl (fun i => gs[i].1) (fun _ => rfl) 0
  rw [List.drop_zero] at htot
  unfold frequency select
  rw [O.map_bind, O.map_pick, LawfulPick.pick_eq (m := W)]
  simp only [pickVia, bind_assoc, pure_bind]
  refine choose_bind_congr (W := W) (congrArg (· - 1) htot) fun k hk _ => ?_
  have hk' : k < totalFrom (fun i : Fin gs.length => gs[i].1) 0 := by omega
  have := selectD_drop_eq (gs.map fun p => (p.1, O.spec (p.2 ()))) (O.spec default)
    (List.length_map _) (fun i : Fin gs.length => gs[i].1) (fun _ => by simp) k 0 hk'
  rw [List.drop_zero] at this
  show _ = selectD _ k _
  rw [this, ← List.getElem_eq_getD (h := by simpa using scanFrom_lt _ hk'), List.getElem_map]
  rfl

/-- `oneOf` is `Obs.index` at every universe: unlike the other combinators it draws no `Nat`, so
neither the generator's element type nor its laws are confined to `Type`. -/
@[gen_map]
theorem map_oneOf {G : Type u → Type v} {W : Type u → Type w} [Gen G] [Monad W] [RandomChoice W]
    (O : Obs G W) {α : Type u} (gs : List (Unit → G α)) (hne : gs ≠ []) :
    O.spec (oneOf gs hne) = index gs hne fun g => O.spec (g ()) := by
  unfold oneOf index
  rw [O.map_bind, O.map_choose]

@[gen_map]
theorem map_oneOfWith {G : Type u → Type v} {W : Type u → Type w} [Gen G] [Monad W]
    [RandomChoice W] (O : Obs G W) {α : Type u} (gs : List (Unit → G α)) (hne : gs ≠ [])
    (impl : G α) (h : impl = oneOf gs hne) :
    O.spec (oneOfWith gs hne impl h) = index gs hne fun g => O.spec (g ()) := by
  rw [oneOfWith_eq, O.map_oneOf]

omit [LawfulMonad G] in
@[gen_map]
theorem map_frequencyWith [LawfulPick G] [LawfulPick W] (gs : List (Nat × (Unit → G α))) (h : 0 < (gs.map Prod.fst).sum)
    (impl : G α) (he : impl = frequency gs h) :
    O.spec (frequencyWith gs h impl he)
      = select gs h (fun g => O.spec (g ())) (O.spec default) := by
  rw [frequencyWith_eq, O.map_frequency]

end Obs
