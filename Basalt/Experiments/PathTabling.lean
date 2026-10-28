/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Segev Elazar-Mittelman
-/
module

public import Basalt.Enum.Finite
public import Basalt.Enum.Tabled

/-!
# Experiment: Path-Counting Tabling

`PolyStep.supports` (`Basalt.Enum.Tabled`) finds which values a recursion with no measure produces.
This finds how many paths reach each, at `Finite`: it memoizes such a recursion on its arguments,
with no measure asked for, and gives `undef` where the paths are infinite instead of running
forever, naming the keys it found depending on themselves.

Re-entering a key still being computed is reaching `undef` there, which at `Finite` is the least
fixpoint: every operation is strict in `undef`, and a monotone function on a flat order that is
not strict is constant. A key computed while a key below it on the stack was open saw a
placeholder, so it is not kept: it is recomputed when next asked for (Tarjan's low-link). `fuel`
bounds how deeply calls nest, which is what makes this total; running out of it is reported, and a
key that comes back defined is right regardless.

Parked: for a recursion that has a measure, `KeyedStep.memoPure` does the same with less; for one
with cycles, infinitely many paths make this `undef` exactly where `supports` has an answer. What is
left is memoizing without writing a measure, and finding a cycle no one meant to write.

Not yet proved: a complete run is the least fixpoint, key for key.
-/

@[expose] public section

namespace Basalt

namespace Tab

variable {κ α : Type} [BEq κ] [Hashable κ]

inductive Slot (α : Type) where
  | open (depth : Nat)
  | done (v : Finite α)

structure State (κ α : Type) [BEq κ] [Hashable κ] where
  table : Std.HashMap κ (Slot α) := {}
  depth : Nat := 0
  /-- The shallowest open key reached from the current frame. -/
  low : Nat := 0
  /-- Keys found to depend on themselves. -/
  cyclic : Array κ := #[]
  /-- Whether some call ran out of fuel. -/
  outOfFuel : Bool := false

end Tab

/-- `Finite`, with the table threaded through every step. -/
def TabM (κ α : Type) [BEq κ] [Hashable κ] (β : Type) : Type :=
  Tab.State κ α → Finite β × Tab.State κ α

namespace TabM

variable {κ α : Type} [BEq κ] [Hashable κ]

def bind (x : TabM κ α β) (f : β → TabM κ α γ) : TabM κ α γ := fun s =>
  match x s with
  | (.undef, s) => (.undef, s)
  | (.mk n idx, s) =>
    let (parts, s) := Fin.foldl n (fun (acc, s) i => let (y, s) := f (idx i) s; (y :: acc, s)) ([], s)
    (Finite.flatten parts.reverse, s)

instance : Monad (TabM κ α) where
  pure b s := (Finite.singleton b, s)
  bind := TabM.bind
  map g x s := let (y, s) := x s; (y.map g, s)
  seq f x s := let (g, s) := f s; let (y, s) := x () s; (Finite.seq g y, s)

instance : RandomChoice (TabM κ α) where
  choose lo hi h s := (RandomChoice.choose (m := Finite) lo hi h, s)

instance : Fail (TabM κ α) := ⟨fun s => (Finite.empty, s)⟩

end TabM

namespace PolyStep

variable {κ α : Type} [BEq κ] [Hashable κ]

/-- A recursive call: a lookup, `undef` on re-entering an open key, or a computation that records
itself unless it saw a key below it open. -/
def tab (step : PolyStep κ α) : Nat → κ → TabM κ α α
  | 0, _ => fun s => (.undef, { s with outOfFuel := true })
  | fuel + 1, k => fun s =>
    match s.table[k]? with
    | some (.done v) => (v, s)
    | some (.open d) => (.undef, { s with low := min s.low d })
    | none =>
      let d := s.depth
      let outerLow := s.low
      let s := { s with table := s.table.insert k (.open d), depth := d + 1, low := d + 1 }
      let (v, s) := step (TabM κ α) (tab step fuel) k s
      let low := s.low
      let s := { s with depth := d }
      if low < d then
        (v, { s with table := s.table.erase k, low := min outerLow low })
      else
        (v, { s with table := s.table.insert k (.done v), low := outerLow,
                     cyclic := if low == d then s.cyclic.push k else s.cyclic })

/-- What a tabled run found. -/
structure Tabled (κ α : Type) where
  values : List (Finite α)
  /-- No call ran out of fuel: every `undef` is the least fixpoint's. -/
  complete : Bool
  /-- Keys found to depend on themselves. -/
  cyclic : Array κ

/-- The recursion at each key, sharing one table, calls nesting at most `fuel` deep. -/
def run (step : PolyStep κ α) (fuel : Nat) (ks : List κ) : Tabled κ α :=
  let (vs, s) := ks.foldl (fun (vs, s) k => let (v, s) := tab step fuel k s; (v :: vs, s)) ([], {})
  { values := vs.reverse, complete := !s.outOfFuel, cyclic := s.cyclic }

end PolyStep

end Basalt
