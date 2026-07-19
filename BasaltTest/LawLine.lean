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
