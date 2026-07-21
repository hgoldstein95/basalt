/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt.Gen

open Lean.Order

/-!
# Generator Statistics

This file enables empirical measurements to back up the proofs that appear in the rest of the
repository.  We provide `#genstats` (see `Basalt.GenStats.Command`), a diagnostic that draws from a
generator many times and summarizes the results.

Note that since we do not require a generator to be a true PBT (i.e., AST) to use this command, we
need to add fuel to the generation process. Fuel truncates the tail of the distribution being
measured: a draw that would have made more than `fuel` choices is reported as `fuel-exhausted`
rather than completed. The summary reports how many draws hit the budget, so a nonzero count is a
signal to raise `Config.fuel` --- or, more likely, a signal that the generator's recursion is
critical or supercritical.

## Main Definitions

- `GenStats.StatGen` — A choice-counting, fuel-guarded, seedable interpretation of `Gen`.
- `GenStats.Config` — Draw count, fuel budget, and seed for a `#genstats` run.
- `GenStats.runDraws` — Draw repeatedly, splitting the RNG per draw.
- `GenStats.render` — Format draw results as a terse, deterministic text summary.
- `GenStats.report` — `runDraws` + `render` + `IO.println`; the entry point `#genstats` emits.
-/

namespace GenStats

/-- Why a draw failed to produce a value. -/
inductive Error where
  /-- The draw exceeded its choice budget (see `Config.fuel`). -/
  | outOfFuel
  /-- The generator failed with a message. -/
  | failure (msg : String)
deriving Repr, Inhabited

/-- State threaded through a single draw: the RNG, the remaining choice budget, and the number of
    choices made so far. -/
structure StatState where
  rng : StdGen
  fuel : Nat
  choices : Nat

/-- A statistics-gathering interpretation of `Gen`: makes real (seeded) random choices, counts
    them, and fails with `Error.outOfFuel` when the budget runs out. -/
abbrev StatGen (α : Type) := StateT StatState (Except Error) α

instance : Inhabited (StatGen α) :=
  ⟨fun _ => .error default⟩

/-! ### Order-theoretic instances on `Except Error`

Like `Basalt.PlausibleGen`, we use a flat order with `Except.error default` as bottom, which gives
`StatGen` its `CCPO` and `MonoBind` instances via the standard `StateT` lifts. -/

instance instPartialOrderExceptError : PartialOrder (Except Error α) :=
  FlatOrder.instOrder (b := Except.error default)

instance instCCPOExceptError : CCPO (Except Error α) :=
  FlatOrder.instCCPO (b := Except.error default)

instance : MonoBind (Except Error) where
  bind_mono_left h := by
    cases h with
    | bot => exact FlatOrder.rel.bot
    | refl => exact FlatOrder.rel.refl
  bind_mono_right h := by
    cases ‹Except Error _› with
    | error => exact FlatOrder.rel.refl
    | ok a => exact h a

/-- `choose` decrements the fuel, counts the choice, and advances the RNG. -/
instance : RandomChoice StatGen where
  choose lo hi h := do
    let s ← get
    if s.fuel == 0 then
      throw .outOfFuel
    else
      let (r, rng') := randNat s.rng lo hi
      set { rng := rng', fuel := s.fuel - 1, choices := s.choices + 1 : StatState }
      pure (ULift.up ⟨min hi (max lo r), by omega⟩)

/-- `StatGen` has everything a generator needs. -/
example : Gen StatGen := inferInstance

/-- Configuration for a `#genstats` run. The default seed is fixed so that output is deterministic
    (and hence testable with `#guard_msgs`); pass a different `seed` to see another sample. -/
structure Config where
  /-- Number of values to draw. -/
  draws : Nat := 1000
  /-- Maximum number of `choose` calls per draw. A draw that exceeds this is reported as
      `fuel-exhausted`; this is what keeps a divergent generator from hanging the elaborator. -/
  fuel : Nat := 10000
  /-- RNG seed. -/
  seed : Nat := 0
deriving Repr

/-- Run a single draw: the value and the number of choices it made, or the error. -/
def runDraw (g : StatGen α) (fuel : Nat) (rng : StdGen) : Except Error (α × Nat) :=
  (g.run { rng, fuel, choices := 0 }).map fun (a, s) => (a, s.choices)

/-- Run `cfg.draws` draws. The RNG is split before each draw so that a failing draw (whose
    post-state is lost to the `Except`) does not make every subsequent draw identical. -/
def runDraws (g : StatGen α) (cfg : Config) : Array (Except Error (α × Nat)) := Id.run do
  let mut rng := mkStdGen cfg.seed
  let mut out := #[]
  for _ in [0:cfg.draws] do
    let (rng₁, rng₂) := RandomGen.split rng
    out := out.push (runDraw g cfg.fuel rng₁)
    rng := rng₂
  return out

/-- Render a value on a single line via its `Repr` instance. -/
def reprLine [Repr α] (a : α) : String :=
  ((repr a).pretty 100000).replace "\n" " "

/-! ### Formatting helpers

All formatting is `Nat`-only arithmetic (no `Float`), so summaries are bit-for-bit reproducible
across platforms — which is what lets `#genstats` output live under `#guard_msgs`. -/

private def padR (s : String) (w : Nat) : String := s ++ "".pushn ' ' (w - s.length)

private def padL (s : String) (w : Nat) : String := "".pushn ' ' (w - s.length) ++ s

/-- `k / n` as a percentage with one decimal place. -/
private def pctStr (k n : Nat) : String :=
  if n == 0 then "-" else
    let m := (k * 1000 + n / 2) / n
    s!"{m / 10}.{m % 10}%"

/-- `sum / count` with one decimal place. -/
private def meanStr (sum count : Nat) : String :=
  if count == 0 then "-" else
    let t := (sum * 10 + count / 2) / count
    s!"{t / 10}.{t % 10}"

/-- Nearest-rank percentile of a sorted array. -/
private def percentile (sorted : Array Nat) (p : Nat) : Nat :=
  if sorted.isEmpty then 0
  else sorted[(p * (sorted.size - 1) + 50) / 100]!

/-- One `label  mean … p50 … p95 … max …` line. -/
private def statLine (label : String) (xs : Array Nat) : String :=
  if xs.isEmpty then
    s!"  {padR label 12}(no data)"
  else
    let sorted := xs.qsort (· < ·)
    let sum := xs.foldl (· + ·) 0
    s!"  {padR label 12}mean {meanStr sum xs.size}   p50 {percentile sorted 50}   " ++
      s!"p95 {percentile sorted 95}   max {sorted.back!}"

/-- Count occurrences of each string, most frequent first (ties alphabetical). -/
private def countRuns (xs : Array String) : Array (String × Nat) := Id.run do
  let sorted := xs.qsort (· < ·)
  let mut out : Array (String × Nat) := #[]
  let mut cur : Option (String × Nat) := none
  for s in sorted do
    match cur with
    | some (t, k) =>
      if t == s then
        cur := some (t, k + 1)
      else
        out := out.push (t, k)
        cur := some (s, 1)
    | none => cur := some (s, 1)
  if let some p := cur then
    out := out.push p
  return out.qsort fun a b => a.2 > b.2 || (a.2 == b.2 && a.1 < b.1)

private def truncate (s : String) (w : Nat := 90) : String :=
  if s.length ≤ w then s else s!"{s.take (w - 1)}…"

/-- What `#genstats` found for one law slot: the conventional name (`sound_complete`) and whether a
declaration under it actually proves the law. -/
abbrev LawStatus := String × Bool

/-- Format draw results as a terse text summary: outcomes, size and choice-count distributions,
    value diversity, head-constructor histogram, most common values, a few samples, and the laws
    the generator carries. The optional functions are supplied by the `#genstats` elaborator based
    on what the output type supports; a `none` simply omits that section. -/
def render (label : String) (cfg : Config) (results : Array (Except Error (α × Nat)))
    (size? : Option (α → Nat) := none) (repr? : Option (α → String) := none)
    (ctor? : Option (α → String) := none) (laws : Array LawStatus := #[]) : String := Id.run do
  let n := results.size
  let oks := results.filterMap fun | .ok p => some p | .error _ => none
  let fuelExhausted := (results.filter fun | .error .outOfFuel => true | _ => false).size
  let failed := n - oks.size - fuelExhausted
  let mut lines := #[s!"{label} — {n} draws (seed {cfg.seed}, fuel {cfg.fuel})", ""]
  -- outcomes
  let mut outcomes := s!"  {padR "outcomes" 12}ok {oks.size} ({pctStr oks.size n})"
  if fuelExhausted > 0 then
    outcomes := outcomes ++ s!"   fuel-exhausted {fuelExhausted} ({pctStr fuelExhausted n})"
  if failed > 0 then
    outcomes := outcomes ++ s!"   failed {failed} ({pctStr failed n})"
  lines := lines.push outcomes
  -- size and choice-count distributions (over completed draws)
  if let some size := size? then
    lines := lines.push (statLine "size" (oks.map fun p => size p.1))
  lines := lines.push (statLine "choices" (oks.map (·.2)))
  -- value diversity
  let reprs? := repr?.map fun f => oks.map fun p => f p.1
  if let some reprs := reprs? then
    if !oks.isEmpty then
      lines := lines.push s!"  {padR "distinct" 12}{(countRuns reprs).size} / {reprs.size}"
  -- head-constructor histogram
  if let some ctor := ctor? then
    if !oks.isEmpty then
      let runs := countRuns (oks.map fun p => ctor p.1)
      let w := runs.foldl (fun w r => max w r.1.length) 0
      let cw := runs.foldl (fun w r => max w (toString r.2).length) 0
      lines := lines.push "" |>.push "  head constructor"
      for (name, k) in runs do
        lines := lines.push
          s!"    {padR name (w + 3)}{padL (pctStr k oks.size) 6}  {padL s!"({k})" (cw + 2)}"
  -- most common values and samples
  if let some reprs := reprs? then
    let runs := countRuns reprs
    if runs.any (·.2 ≥ 2) then
      let top := (runs.take 5).filter (·.2 ≥ 2)
      let cw := top.foldl (fun w r => max w (toString r.2).length) 0
      lines := lines.push "" |>.push "  most common"
      for (s, k) in top do
        lines := lines.push
          s!"    {padL (pctStr k reprs.size) 6}  {padL s!"({k})" (cw + 2)}  {truncate s}"
    if !reprs.isEmpty then
      lines := lines.push "" |>.push "  samples"
      for s in reprs.take 3 do
        lines := lines.push s!"    {truncate s}"
  -- Laws last, so the measurements above are read *before* the reminder of what is merely measured.
  -- A generator with no laws at all prints nothing here: the block exists to put proved next to
  -- unproved, and with nothing proved there is no contrast to draw.
  if !laws.isEmpty then
    let w := laws.foldl (fun acc (n, _) => max acc n.length) 0 + 2
    let proved := laws.filterMap fun (n, ok) => if ok then some n else none
    lines := lines.push ""
    lines := lines.push <|
      if proved.isEmpty then "  laws: (none proved)"
      else s!"  laws: {String.intercalate "  " (proved.map (· ++ " ✓")).toList}"
    for (name, ok) in laws do
      if !ok then
        -- The one slot the report can speak to empirically. Naming the measurement next to the
        -- missing proof is the point: 0 divergences in 1000 draws is not a termination proof.
        let note :=
          if name == "terminates" then
            s!"(not proved; measured {fuelExhausted}/{n} divergences)"
          else "(not proved)"
        lines := lines.push s!"        {padR name w}— {note}"
  return String.intercalate "\n" lines.toList

/-- Draw, summarize, print. This is the function that `#genstats` elaborates to a call of. -/
def report (g : StatGen α) (label : String) (cfg : Config)
    (size? : Option (α → Nat) := none) (repr? : Option (α → String) := none)
    (ctor? : Option (α → String) := none) (laws : Array LawStatus := #[]) : IO Unit :=
  IO.println (render label cfg (runDraws g cfg) size? repr? ctor? laws)

end GenStats
