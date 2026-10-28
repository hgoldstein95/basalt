/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
module

public import Basalt.Fail
public import Std.Data.HashMap

/-!
# Supports of Recursion With No Measure: Set-Valued Tabling

A recursion whose calls need not get smaller — a retry loop, a relation with a transitive rule —
has no finite enumeration at `Finite` wherever it has infinitely many paths, even when it has
finitely many values: `g = pick (pure 0) g` reaches `0` once for every number of coin flips. Asked
which values it can produce, it has one, `{0}`.

`supports` asks that question. A table entry is a set of values (a list without repeats); a key not
yet in the table reads as `∅`, and is added at the end of the round; and whole rounds over the table
repeat until nothing changes, as Datalog evaluates a recursive query. Starting from `∅` and only ever growing, a round that changes nothing
is the least fixpoint under inclusion — the support — and the run is
`complete`: every value is there, so a value that is not is not producible. An infinite support never
stops growing; it runs out of fuel, and says so.

Only the table's entries need `BEq`; within a step, values are a plain list. Each round recomputes
every key (naive evaluation), which wants to become semi-naive before it meets a large relation.

That a complete run is the support, key for key, is `PolyStep.supports_eq`
(`Basalt.Enum.TabledLaws`).
-/

@[expose] public section

namespace Basalt

/-- A recursion with no measure, written once for every interpretation that can choose and fail. -/
abbrev PolyStep (κ α : Type) : Type 1 :=
  ∀ (G : Type → Type) [Monad G] [RandomChoice G] [Fail G], (κ → G α) → κ → G α

/-- A list of values, reading a table of each key's values so far, and reporting the keys it looked
for and did not find. The table is not changed within a step. -/
def SetM (κ α : Type) [BEq κ] [Hashable κ] (β : Type) : Type :=
  Std.HashMap κ (List α) → List β × List κ

namespace SetM

variable {κ α : Type} [BEq κ] [Hashable κ]

/-- Every continuation, run against the same table, on every value of `x`. -/
def bind (x : SetM κ α β) (f : β → SetM κ α γ) : SetM κ α γ := fun t =>
  let r := x t
  let rs := r.1.map fun a => f a t
  (rs.flatMap (·.1), r.2 ++ rs.flatMap (·.2))

instance : Monad (SetM κ α) where
  pure b _ := ([b], [])
  bind := SetM.bind

instance : RandomChoice (SetM κ α) where
  choose lo hi _ _ :=
    ((List.range (hi - lo + 1)).attach.map fun ⟨i, hi'⟩ =>
      .up ⟨lo + i, by have := List.mem_range.mp hi'; omega⟩, [])

instance : Fail (SetM κ α) := ⟨fun _ => ([], [])⟩

end SetM

namespace PolyStep

variable {κ α : Type} [BEq κ] [Hashable κ] [BEq α]

/-- A recursive call: the key's values so far, or `∅` and the key reported missing. -/
def lookupSet (k : κ) : SetM κ α α := fun t =>
  match t[k]? with
  | some v => (v, [])
  | none => ([], [k])

/-- One key's step: its new values added if there are any. Whether it changed, and the keys it missed. -/
def update (step : PolyStep κ α) (k : κ) (t : Std.HashMap κ (List α)) :
    Std.HashMap κ (List α) × Bool × List κ :=
  let (vs, ms) := step (SetM κ α) lookupSet k t
  let old := t.getD k []
  if vs.all old.contains then (t, false, ms) else (t.insert k (old ++ vs).eraseDups, true, ms)

/-- One round: every key known at its start updated in turn, then every key missed added with `∅`.
Whether anything changed: a key gained a value, or a key was missed. -/
def round (step : PolyStep κ α) (t : Std.HashMap κ (List α)) : Std.HashMap κ (List α) × Bool :=
  let (t, changed, ms) := t.keys.foldl (fun (t, changed, ms) k =>
    let (t, c, m) := update step k t
    (t, changed || c, ms ++ m)) (t, false, [])
  (ms.foldl (fun t k => if t.contains k then t else t.insert k []) t, changed || !ms.isEmpty)

/-- What a set-valued run found. -/
structure Supports (κ α : Type) [BEq κ] [Hashable κ] where
  values : List (List α)
  /-- A round changed nothing: these are the supports, and no key's values were missed. -/
  complete : Bool
  rounds : Nat
  /-- The table the run ended with. -/
  table : Std.HashMap κ (List α)

/-- Rounds until nothing changes, at most `fuel` of them, from a table. -/
def rounds (step : PolyStep κ α) : Nat → Nat → Std.HashMap κ (List α) →
    Std.HashMap κ (List α) × Bool × Nat
  | 0, n, t => (t, false, n)
  | fuel + 1, n, t =>
    let (t', changed) := round step t
    if changed then rounds step fuel (n + 1) t' else (t', true, n + 1)

/-- The support at each key: rounds until nothing changes, at most `fuel` of them. -/
def supports (step : PolyStep κ α) (fuel : Nat) (ks : List κ) : Supports κ α :=
  let t0 : Std.HashMap κ (List α) := ks.foldl (fun t k => t.insert k []) {}
  let (t, complete, rounds) := rounds step fuel 0 t0
  { values := ks.map (t.getD · []), complete, rounds, table := t }

end PolyStep

end Basalt
