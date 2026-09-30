/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Segev Elazar Mittelman
-/
import Basalt.Enumeration

/-!
# Graded Enumeration

An enumeration stratified by size, the algebra of Duregård's Feat: level `n` holds the derivations of
size `n`, and every level must be finite, which is what makes convolution fair without interleaving.
`Graded` is what counting (`Cnt`) supports; `GradedBind` adds the value-dependent operations.
-/

universe u v

namespace Basalt

/-- Size-stratified enumeration. `pay` shifts a level — one rule application — and `pair` is the
convolution `⨆_{i+j=n}`. -/
class Graded (f : Type u → Type v) extends Choice f where
  /-- A single value, at level 0. -/
  single : α → f α
  /-- Shift every level up by one: what a rule application costs. -/
  pay : f α → f α
  /-- Convolution: level `n` of the product is `⨆_{i+j=n} xᵢ × yⱼ`. -/
  pair : f α → f β → f (α × β)
  /-- Renaming. Sound for `Cnt` precisely because it cannot change cardinality — unlike `bind`. -/
  gmap : (α → β) → f α → f β

/-- A three-valued verdict for a checked premise. `inconclusive` claims only that nothing was determined:
it is neither `no` nor a claim that a search was completed. -/
inductive V where
  | yes
  | no
  | inconclusive
  deriving Repr, DecidableEq, Inhabited

/-- The value-dependent operations. `Cnt` cannot implement them: it is phantom in `α`, so it has no
value to pass to a continuation or a filter. -/
class GradedBind (f : Type u → Type v) extends Graded f where
  /-- Level-preserving dependent sequencing: the value and the continuation are both taken at level `n`.

  Incomplete for an auxiliary output that has its own size — a small derivation with a large auxiliary
  output lies at no level — so a sized auxiliary output needs `bindC`. -/
  bind : f α → (α → f β) → f β
  /-- Convolving dependent sequencing, `⨆_{i+j=n}`: the value from level `i`, the continuation at
  level `j`. `pair` with a dependency. -/
  bindC : f α → (α → f β) → f β
  /-- Keep the values a check does not reject, consuming no level: `yes` keeps with `true`,
  `inconclusive` keeps with `false`, `no` drops. -/
  guard : (α → V) → f α → f (α × Bool)

/-! ## Interpretations -/

/-- **Values.** Level `n` is the list of size-`n` values. The interpretation to reason at; a function
recomputes every level it is asked for, so it is not the one to run (see `LvT`, `LvL`, `LvC`). -/
def Lv (α : Type) := Nat → List α

/-- **Cardinality.** Level `n` is the number of size-`n` values. -/
def Cnt (_α : Type) := Nat → Nat

/-- **Specification.** Which values inhabit which level. -/
def SetE (α : Type) := Nat → α → Prop

instance : Graded Lv where
  nothing _ := []
  union x y n := x n ++ y n
  single a n := if n = 0 then [a] else []
  pay x n := match n with | 0 => [] | n + 1 => x n
  pair x y n := (List.range (n + 1)).flatMap fun i => (x i).flatMap fun a => (y (n - i)).map (a, ·)
  gmap g x n := (x n).map g

instance : Graded Cnt where
  nothing _ := 0
  union x y n := x n + y n
  single _ n := if n = 0 then 1 else 0
  pay x n := match n with | 0 => 0 | n + 1 => x n
  pair x y n := ((List.range (n + 1)).map fun i => x i * y (n - i)).sum
  gmap _ x := x

instance : Graded SetE where
  nothing _ _ := False
  union x y n a := x n a ∨ y n a
  single a n b := n = 0 ∧ b = a
  pay x n a := match n with | 0 => False | n + 1 => x n a
  pair x y n p := ∃ i ≤ n, x i p.1 ∧ y (n - i) p.2
  gmap g x n b := ∃ a, x n a ∧ g a = b

instance : GradedBind Lv where
  bind x k n := (x n).flatMap fun a => k a n
  bindC x k n := (List.range (n + 1)).flatMap fun i => (x i).flatMap fun a => k a (n - i)
  guard p x n := (x n).filterMap fun a =>
    match p a with
    | .yes => some (a, true)
    | .inconclusive => some (a, false)
    | .no => none

instance : GradedBind SetE where
  bind x k n b := ∃ a, x n a ∧ k a n b
  bindC x k n b := ∃ i ≤ n, ∃ a, x i a ∧ k a (n - i) b
  guard p x n q := x n q.1 ∧ (match p q.1 with
    | .yes => q.2 = true
    | .inconclusive => q.2 = false
    | .no => False)

/-! ## Iteration, and graded leaves

A recursive enumeration takes its recursive occurrence as a parameter and is closed by `gradedIter`,
since recursing at `enum (n - i)` inside `pair` is not structural. A leaf must be graded too: an
ungraded one (all of `Nat` at level 0) makes that level infinite. -/

/-- Close a graded recursion at a given number of levels. -/
def gradedIter [Graded f] (step : f α → f α) : Nat → f α
  | 0 => Choice.nothing
  | n + 1 => step (gradedIter step n)

/-- Close an indexed graded recursion: a family of enumerations, one per index, whose rules may recurse
at other indices. Levels decrease, not indices, so an index that grows needs no termination argument. -/
def gradedIterIx [Graded f] {ι : Type} (step : (ι → f α) → ι → f α) : Nat → ι → f α
  | 0, _ => Choice.nothing
  | n + 1, i => step (gradedIterIx step n) i

/-- `Nat` graded by magnitude: level `n` is `{n}`. -/
def natStep [Graded f] (rec : f Nat) : f Nat :=
  Choice.union (Graded.single 0) (Graded.pay (Graded.gmap (· + 1) rec))

/-- `Bool`, at level 0. -/
def boolStep [Graded f] (_rec : f Bool) : f Bool :=
  Choice.union (Graded.single false) (Graded.single true)

/-- `List α` from a graded element enumeration: `[]` at level 0; a cons costs one level, its element and
tail convolved. -/
def listStep [Graded f] (elem : f α) (rec : f (List α)) : f (List α) :=
  Choice.union (Graded.single [])
    (Graded.pay (Graded.gmap (fun p => p.1 :: p.2) (Graded.pair elem rec)))

end Basalt
