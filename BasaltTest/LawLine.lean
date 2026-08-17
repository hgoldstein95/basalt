/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt

/-!
# The `#genstats` laws line

`#genstats` reports which laws a generator carries, next to what it merely *measured*. The point is
the contrast: `0/1000 divergences` is evidence, not a termination proof, and the report should not
let one be read as the other.

Laws are found by **naming convention** (`genFoo.sound_complete`), and the **statement is checked**
— a conventionally-named theorem that says something else, or says it about a different generator,
must not be laundered into a ✓.
-/

def genCoin [Gen G] : G Bool :=
  RandomChoice.pick (fun () => pure true) (fun () => pure false)

/-! ## No laws: the block is absent

With nothing proved there is no contrast to draw, so five lines of `—` would be noise. -/

/--
info: genCoin — 5 draws (seed 0, fuel 10000)

  outcomes    ok 5 (100.0%)
  size        mean 1.0   p50 1   p95 1   max 1
  choices     mean 1.0   p50 1   p95 1   max 1
  distinct    2 / 5

  head constructor
    false    60.0%  (3)
    true     40.0%  (2)

  most common
     60.0%  (3)  false
     40.0%  (2)  true

  samples
    false
    true
    true
-/
#guard_msgs in
#genstats (draws := 5) genCoin

/-! ## A conventionally-named theorem that is not the law does **not** count

`genDud.sound_complete` exists and is true, but says nothing about `IsSoundAndComplete`. Reporting
it would make the ✓ mean "someone wrote a theorem with the right name". -/

def genDud [Gen G] : G Bool := pure true

theorem genDud.sound_complete : 1 + 1 = 2 := rfl

/-- info: false -/
#guard_msgs in
open Lean Elab Meta in
#eval show CoreM Bool from do
  let env ← getEnv
  Prod.fst <$> (GenStats.Command.lawProvedFor env `genDud `sound_complete).run {} {}

/-! ## The law, proved: ✓ beside the measurement it is not

`terminates` names the divergence count it was *not* proved by. -/

theorem genCoin.sound_complete : IsSoundAndComplete (genCoin (G := SPMF)) (fun _ => True) := by
  intro a
  constructor
  · intro _; trivial
  · intro _
    cases a <;> simp [genCoin, SPMF.support_pick]

/--
info: genCoin — 5 draws (seed 0, fuel 10000)

  outcomes    ok 5 (100.0%)
  size        mean 1.0   p50 1   p95 1   max 1
  choices     mean 1.0   p50 1   p95 1   max 1
  distinct    2 / 5

  head constructor
    false    60.0%  (3)
    true     40.0%  (2)

  most common
     60.0%  (3)  false
     40.0%  (2)  true

  samples
    false
    true
    true

  laws: sound_complete ✓
        terminates      — (not proved; measured 0/5 divergences)
        cost_bounded    — (not proved)
        filter_free     — (not proved)
        productive      — (not proved)
-/
#guard_msgs in
#genstats (draws := 5) genCoin

/-! ## The partial-generator laws: `productive` and `filter_free` -/

open SPMF in

def genMaybe [Gen G] : G (Option Nat) :=
  RandomChoice.pick (fun () => pure none) (fun () => pure (some 0))

theorem genMaybe.productive : IsProductive (genMaybe (G := SPMF)) :=
  IsProductive_of_mem_support (a := 0)
    (by simp [genMaybe, SPMF.support_pick, SPMF.support_pure])

/--
info: genMaybe — 5 draws (seed 0, fuel 10000)

  outcomes    ok 5 (100.0%)
  size        mean 1.0   p50 1   p95 1   max 1
  choices     mean 1.0   p50 1   p95 1   max 1
  distinct    2 / 5

  head constructor
    some    60.0%  (3)
    none    40.0%  (2)

  most common
     60.0%  (3)  some 0
     40.0%  (2)  none

  samples
    some 0
    none
    none

  laws: productive ✓
        sound_complete  — (not proved)
        terminates      — (not proved; measured 0/5 divergences)
        cost_bounded    — (not proved)
        filter_free     — (not proved)
-/
#guard_msgs in
#genstats (draws := 5) genMaybe

open SPMF in
def genSurely [Gen G] : G (Option Nat) :=
  RandomChoice.pick (fun () => pure (some 0)) (fun () => pure (some 1))

theorem genSurely.filter_free : IsFilterFree (genSurely (G := SPMF)) := by
  have hmass : (genSurely (G := SPMF)).mass = 1 :=
    SPMF.IsPMF_pick (SPMF.IsPMF_pure _) (SPMF.IsPMF_pure _)
  rw [IsFilterFree_iff_massNone_eq_zero hmass]
  show (genSurely (G := SPMF)) none = 0
  rw [SPMF.apply_eq_zero_iff]
  simp [genSurely, SPMF.support_pick, SPMF.support_pure]

theorem genSurely.productive : IsProductive (genSurely (G := SPMF)) :=
  IsProductive_of_IsFilterFree genSurely.filter_free

/--
info: genSurely — 5 draws (seed 0, fuel 10000)

  outcomes    ok 5 (100.0%)
  size        mean 1.0   p50 1   p95 1   max 1
  choices     mean 1.0   p50 1   p95 1   max 1
  distinct    2 / 5

  head constructor
    some   100.0%  (5)

  most common
     60.0%  (3)  some 1
     40.0%  (2)  some 0

  samples
    some 1
    some 0
    some 0

  laws: filter_free ✓  productive ✓
        sound_complete  — (not proved)
        terminates      — (not proved; measured 0/5 divergences)
        cost_bounded    — (not proved)
-/
#guard_msgs in
#genstats (draws := 5) genSurely
