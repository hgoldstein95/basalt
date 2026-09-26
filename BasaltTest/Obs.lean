/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt

/-!
# One Lemma per Combinator

Pins the contract of `Basalt/Obs/`: a combinator the library knows nothing about gets one `map_`
lemma, and each judgment about it, at either interpretation, is that lemma read through an
observation and a presentation of its choice.
-/

open RandomChoice SPMF ENNReal

namespace ObsTest

/-- `g` at a uniformly drawn size. -/
def sized [Gen G] (n : Nat) (g : Nat → G α) : G α := do
  let k ← choose 0 n (Nat.zero_le n)
  g k.down.val

theorem map_sized {G : Type u → Type v} {W : Type u → Type w} [Gen G] [Monad W] [RandomChoice W]
    (O : Obs G W) (n : Nat) (g : Nat → G α) :
    O.spec (sized n g) = choose 0 n (Nat.zero_le n) >>= fun k => O.spec (g k.down.val) := by
  simp only [sized, O.map_bind, O.map_choose]

theorem mem_support_sized_iff {n : Nat} {g : Nat → SPMF α} {a : α} :
    a ∈ (sized n g).support ↔ ∃ k, ∃ _ : 0 ≤ k ∧ k ≤ n, a ∈ (g k).support :=
  (mem_support_of_may (map_sized mayObs n g)).trans ((Mix.range_angelic _).trans
    (exists_congr fun _ => exists_congr fun _ => mem_support_iff_may.symm))

theorem always_sized_iff {n : Nat} {g : Nat → SPMF α} {Q : α → Prop} :
    (∀ a ∈ (sized n g).support, Q a) ↔ ∀ k, 0 ≤ k ∧ k ≤ n → ∀ a ∈ (g k).support, Q a :=
  (iff_of_eq (congrFun (map_sized alwaysObs n g) Q)).trans (Mix.range_demonic _)

theorem expect_sized {n : Nat} {g : Nat → SPMF α} (f : α → ℝ≥0∞) :
    expect (sized n g) f
      = (∑ k ∈ Finset.Icc 0 n, expect (g k) f) / ((n - 0 + 1 : ℕ) : ℝ≥0∞) :=
  (congrFun (map_sized expectObs n g) f).trans (Mix.range_average 0 n fun k => expect (g k) f)

/-! The cost of the draw appears in each postcondition without being stated: it is `WPC`'s. -/

theorem costAlways_sized_iff {n : Nat} {g : Nat → SPMF.Cost α} {Q : α → Nat → Prop} :
    SPMF.Cost.alwaysObs.spec (sized n g) Q
      ↔ ∀ k, 0 ≤ k ∧ k ≤ n → SPMF.Cost.alwaysObs.spec (g k) fun a m => Q a (1 + m) :=
  (iff_of_eq (congrFun (map_sized SPMF.Cost.alwaysObs n g) Q)).trans (Mix.range_demonic _)

end ObsTest

-- Every non-recursive combinator has its `@[gen_map]` lemma, which is all the walker knows of it;
-- each recursive one has a bridge from its law for every direction it is walked in.
open Lean Elab Command Basalt.Walk in
run_cmd do
  let env ← getEnv
  let noMap := [``RandomChoice.choose, ``RandomChoice.coin, ``chooseInt,
    ``elements, ``oneOf, ``frequency, ``oneOfWith, ``frequencyWith].filter (mapFor env · |>.isNone)
  unless noMap.isEmpty do throwError "combinators with no `@[gen_map]` lemma: {noMap}"
  for j in [Judgment.spec true, .spec false] do
    for c in [``vectorOf, ``listOfMaxLength, ``permutationOf] ++
        (if j.key == (Judgment.spec false).key then [``listOf, ``nonEmptyListOf] else []) do
      if (rulesFor env j.key c).isNone then
        throwError "`{c}` has no bridge for the judgment `{j.key}`"
  -- The support observations share `.spec false`'s key with the others, so each is looked for.
  for obs in [``SPMF.alwaysObs, ``SPMF.mayObs] do
    for c in [``vectorOf, ``listOfMaxLength, ``listOf, ``nonEmptyListOf, ``permutationOf] do
      let rules := (rulesFor env (Judgment.spec false).key c).getD #[]
      unless rules.any fun r => ((env.find? r).get!.type.find? (·.isConstOf obs)).isSome do
        throwError "`{c}` has no bridge for a lower bound on `{obs}`"
