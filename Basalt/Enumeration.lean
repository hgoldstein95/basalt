/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Segev Elazar Mittelman
-/
import Basalt.BacktrackGen

/-!
# Enumerations

`Choice` is nondeterministic collection, the enumerator's counterpart of `RandomChoice`: alternatives
are kept rather than sampled. An `Enumeration` is a `Producer` of the `enum` kind over such a carrier.
-/

namespace Basalt

/-- Nondeterministic collection. Not Lean's `Alternative`, whose `orElse` keeps the first success
rather than both alternatives.

Under `Basalt` rather than at the root: a root `Choice` would squat on a common word in every file
that derived code is written into. -/
class Choice (m : Type u → Type v) where
  /-- The empty collection. -/
  nothing : m α
  /-- Keep both alternatives. -/
  union : m α → m α → m α

end Basalt

open Basalt

instance : Choice List where
  nothing := []
  union := List.append

/-- An enumeration: a `Producer` of the `enum` kind. -/
abbrev Enumeration (m : Type → Type) (α : Type) := Producer .enum m α

namespace Enumeration

/-- `default` is the empty enumeration, not `exhausted`, which would claim there might be more. -/
instance [Choice m] : Inhabited (Producer .enum m α) where
  default := ⟨Choice.nothing⟩

/-- Every alternative, in order. -/
def enumerate [Choice m] (es : List (Enumeration m α)) : Enumeration m α :=
  ⟨es.foldr (fun e acc => Choice.union e.run acc) Choice.nothing⟩

end Enumeration

namespace Outcome

/-- Conjunction of two outcomes into an outcome of the pair: Kleene's strong conjunction, in which
`refuted` annihilates even an `exhausted` partner. -/
def seq : Outcome α → Outcome β → Outcome (α × β)
  | .refuted, _ => .refuted
  | _, .refuted => .refuted
  | .exhausted, _ => .exhausted
  | _, .exhausted => .exhausted
  | .ok a, .ok b => .ok (a, b)

/-- `seq` commutes up to swapping the pair, so a product of enumerations can be reordered. -/
theorem seq_comm (x : Outcome α) (y : Outcome β) : seq x y = map Prod.swap (seq y x) := by
  cases x <;> cases y <;> rfl

@[simp] theorem seq_refuted_left (y : Outcome β) : seq (.refuted : Outcome α) y = .refuted := rfl

@[simp] theorem seq_refuted_right (x : Outcome α) : seq x (.refuted : Outcome β) = .refuted := by
  cases x <;> rfl

theorem seq_ok_iff {x : Outcome α} {y : Outcome β} {p : α × β} :
    seq x y = .ok p ↔ x = .ok p.1 ∧ y = .ok p.2 := by
  obtain ⟨p1, p2⟩ := p
  cases x <;> cases y <;> simp [seq]

end Outcome
