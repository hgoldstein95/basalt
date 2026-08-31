/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt
import BasaltExamples.SkipList.Def

open RandomChoice

/-!
# Skip Lists With Few Full-Height Towers

`SkipList.genFewTall` generates the valid skip lists in which fewer than 25% of the entries have the
maximum tower height — Dewey, Nichols & Hardekopf's edge case, and a *global* counting constraint.
The generator draws the length first, which turns the constraint into a budget of full-height towers
that the element-by-element recursion spends.
-/

namespace SkipList

/-- Fewer than `25%` of the entries have the maximum tower height. The empty skip list does not
qualify: `100 * 0 < 25 * 0` is false. -/
def ValidFewTall (maxHeight maxLen maxVal : Nat) (xs : List Entry) : Prop :=
  Valid maxHeight maxLen maxVal xs ∧ 100 * tallCount maxHeight xs < 25 * xs.length

/-- Generates exactly `n` entries with keys in `[lo, lo + slack + n)`, at most `budget` of them with
a full-height tower. `slack` is the key room left over once each of the `n` entries has taken one
key, so drawing the head's gap `g` from `[0, slack]` cannot overshoot and needs no guard. -/
def genExact [Gen G] (maxHeight : Nat) (hh : 2 ≤ maxHeight) :
    Nat → Nat → Nat → Nat → G (List Entry)
  | 0, _, _, _ => pure []
  | n + 1, budget, lo, slack => do
    let g ← chooseNat 0 slack (Nat.zero_le _)
    let ht ← chooseNat 1 (if 0 < budget then maxHeight else maxHeight - 1) (by split <;> omega)
    let rest ← genExact maxHeight hh n (if ht = maxHeight then budget - 1 else budget)
      (lo + g + 1) (slack - g)
    return ⟨lo + g, ht⟩ :: rest

/-- Generates a valid skip list with fewer than `25%` full-height towers: draw the length `n`, which
fixes both the key room and the budget `(n - 1) / 4` of full-height towers, then fill it. -/
def genFewTall [Gen G] (maxHeight maxLen maxVal : Nat) (hh : 2 ≤ maxHeight) (hl : 1 ≤ maxLen) :
    G (List Entry) := do
  let n ← chooseNat 1 (min maxLen (maxVal + 1)) (by omega)
  genExact maxHeight hh n ((n - 1) / 4) 0 (maxVal + 1 - n)

/-- Strictly increasing keys in `[m, M]` leave room for at most `M + 1 - m` entries. -/
theorem length_le_of_pairwise {xs : List Entry} {m M : Nat}
    (hpw : xs.Pairwise (fun d e => d.val < e.val))
    (hb : ∀ e ∈ xs, m ≤ e.val ∧ e.val ≤ M) :
    xs.length ≤ M + 1 - m := by
  induction xs generalizing m with
  | nil => simp
  | cons e rest ih =>
    simp only [List.pairwise_cons] at hpw
    have he := hb e (by simp)
    have := ih hpw.2 (m := e.val + 1) fun f hf => ⟨hpw.1 f hf, (hb f (by simp [hf])).2⟩
    simp only [List.length_cons]
    omega

theorem genExact_mem_support {maxHeight : Nat} {hh : 2 ≤ maxHeight} (xs : List Entry)
    (n budget lo slack : Nat) :
    xs ∈ SPMF.support (genExact maxHeight hh n budget lo slack) ↔
      xs.length = n ∧
      xs.Pairwise (fun d e => d.val < e.val) ∧
      (∀ e ∈ xs, lo ≤ e.val ∧ e.val < lo + slack + n ∧ 1 ≤ e.height ∧ e.height ≤ maxHeight) ∧
      tallCount maxHeight xs ≤ budget := by
  induction xs generalizing n budget lo slack with
  | nil => cases n <;> simp [genExact, tallCount]
  | cons e rest ih =>
    obtain ⟨v, ht⟩ := e
    cases n with
    | zero => simp [genExact]
    | succ n =>
      rw [genExact]
      simp [ih, List.pairwise_cons, tallCount, List.countP_cons]
      constructor
      · rintro ⟨g, hg, ⟨hht1, hht2⟩, ⟨hlen, hpw, hb, htc⟩, rfl⟩
        refine ⟨hlen, ⟨fun f hf => (hb f hf).1, hpw⟩,
          ⟨⟨by omega, by omega, hht1, ?_⟩, fun f hf => ?_⟩, ?_⟩
        · split_ifs at hht2 <;> omega
        · have := hb f hf; omega
        · split_ifs at hht2 htc ⊢ <;> omega
      · rintro ⟨hlen, ⟨hgt, hpw⟩, ⟨⟨hlov, hvhi, hht1, hht2⟩, hb⟩, htc⟩
        have hroom : rest.length ≤ lo + slack + n + 1 - (v + 1) :=
          length_le_of_pairwise hpw fun f hf => ⟨hgt f hf, by have := hb f hf; omega⟩
        rw [hlen] at hroom
        refine ⟨v - lo, by omega, ⟨hht1, ?_⟩, ⟨hlen, hpw, fun f hf => ?_, ?_⟩, by omega⟩
        · split_ifs at htc ⊢ <;> omega
        · have := hb f hf; have := hgt f hf; omega
        · split_ifs at htc ⊢ <;> omega

theorem genFewTall.sound_complete {maxHeight maxLen maxVal : Nat} {hh : 2 ≤ maxHeight}
    {hl : 1 ≤ maxLen} :
    IsSoundAndComplete (genFewTall maxHeight maxLen maxVal hh hl)
      (ValidFewTall maxHeight maxLen maxVal) := by
  intro xs
  rw [genFewTall]
  support_simp [genExact_mem_support]
  simp only [ValidFewTall, Valid]
  constructor
  · rintro ⟨n, ⟨hn1, hn2⟩, hlen, hpw, hb, htc⟩
    refine ⟨⟨by omega, hpw, fun e he => ?_⟩, by omega⟩
    have := hb e he
    omega
  · rintro ⟨⟨hlen, hpw, hb⟩, hfew⟩
    have hroom : xs.length ≤ maxVal + 1 - 0 :=
      length_le_of_pairwise hpw fun e he => ⟨Nat.zero_le _, (hb e he).1⟩
    exact ⟨xs.length, ⟨by omega, by omega⟩, rfl, hpw,
      fun e he => by have := hb e he; omega, by omega⟩

end SkipList
