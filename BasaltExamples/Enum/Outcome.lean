/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
module

public import Basalt.Enum

/-!
# How Often a Derived Generator Exhausts, and Why

A generator shaped like Specimen's derived `BacktrackGen` code — `backtrack` over rules, size-0
truncation, a premise decided by a checker with limited fuel — with each `exhausted` tagged by its
source, and run at `WFinite`: the exact probability of each outcome, by size and checker fuel.

* `lit n : nat`; `le a b : bool` when `Le a b`; `succ e : pos` when `e : nat`. `pos` has no
  non-recursive rule, so at size 0 it can only be truncated, and `Le` is decided by its derived
  checker, which can run out of fuel.
* `genHasType` truncates at size 0 the way derived code does now, relabelling every size-0
  refutation (`refutedToExhausted`); `genHasType'` truncates per call, cutting off a recursive
  rule only once its conclusion has matched. For `bool`, whose rules are all non-recursive, the
  first reports genuine refutations as truncated; the second does not.
-/

@[expose] public section

namespace Basalt.Examples.Enum.Exhaustion

open Basalt RandomChoice

/-! ## `Outcome`, with a reason on `exhausted` -/

/-- Why a search came back without an answer. Only `truncated` means the budget was searched
completely; the other two mean the search was cut short. -/
inductive Why where
  /-- `backtrack`'s fuel backstop tripped. -/
  | fuel
  /-- A size-0 disjunction offered only its non-recursive rules, and they all failed. -/
  | truncated
  /-- A premise checker ran out of fuel before deciding. -/
  | inconclusive
  deriving Repr, BEq, DecidableEq

inductive Outcome (α : Type) where
  | ok (a : α)
  | refuted
  | exhausted (whys : List Why)
  deriving Repr, BEq

/-- The branch's `BacktrackGen`, over any interpretation. -/
structure BG (G : Type → Type) (α : Type) where
  run : G (Outcome α)

instance [Monad G] : Monad (BG G) where
  pure a := ⟨pure (.ok a)⟩
  bind x f := ⟨do
    match ← x.run with
    | .ok a => (f a).run
    | .refuted => pure .refuted
    | .exhausted w => pure (.exhausted w)⟩

def lift [Monad G] (g : G α) : BG G α := ⟨do return .ok (← g)⟩
def refute [Monad G] : BG G α := ⟨pure .refuted⟩
def exhaust [Monad G] (w : Why) : BG G α := ⟨pure (.exhausted [w])⟩

def refutedToExhausted [Monad G] (g : BG G α) : BG G α := ⟨do
  match ← g.run with
  | .refuted => pure (.exhausted [.truncated])
  | o => pure o⟩

def addWhys (acc ws : List Why) : List Why := ws.foldl (fun a w => if a.contains w then a else a ++ [w]) acc

/-- The branch's `backtrack`: draw a branch by weight, drop it on failure, try again. All failed:
`refuted` if every one was, else `exhausted`, with the reasons of the ones that were. -/
def backtrack [Monad G] [RandomChoice G] (gs : List (Nat × (Unit → BG G α))) : BG G α :=
  ⟨go gs.length gs []⟩
where
  go : Nat → List (Nat × (Unit → BG G α)) → List Why → G (Outcome α)
    | _, [], whys => pure (if whys.isEmpty then .refuted else .exhausted whys)
    | 0, _, whys => pure (.exhausted (addWhys whys [.fuel]))
    | fuel + 1, gs@(_ :: _), whys => do
      let total := gs.foldl (fun t (w, _) => t + w) 0
      if total = 0 then pure (if whys.isEmpty then .refuted else .exhausted whys) else
      let r := (← choose 0 (total - 1) (Nat.zero_le _)).down.val
      let rec split : List (Nat × (Unit → BG G α)) → Nat → Option ((Unit → BG G α) × List (Nat × (Unit → BG G α)))
        | [], _ => none
        | (w, g) :: rest, r =>
          if r < w then some (g, rest) else (split rest (r - w)).map fun (g', rest') => (g', (w, g) :: rest')
      match split gs r with
      | none => pure (if whys.isEmpty then .refuted else .exhausted whys)
      | some (g, rest) =>
        match ← (g ()).run with
        | .ok a => pure (.ok a)
        | .refuted => go fuel rest whys
        | .exhausted ws => go fuel rest (addWhys whys ws)

/-! ## A relation with a truncated rule and a fuel-bounded premise

`lit n : nat`; `le a b : bool` when `Le a b`; `succ e : pos` when `e : nat`. `pos` has no
non-recursive rule, so at size 0 it is truncated. `Le` is decided by its derived checker, which
recurses on `b` and gives up when its fuel (the initial size, as Specimen emits it) runs out. -/

inductive Expr where
  | lit (n : Nat)
  | le (a b : Nat)
  | succ (e : Expr)
  deriving Repr, BEq

inductive Ty | nat | bool | pos
  deriving Repr, BEq

inductive V | yes | no | inconclusive

/-- `Le a b`'s checker: `le_refl` (`a = b`) or `le_step` (`Le a (b - 1)`), within `fuel` steps. -/
def checkLe : Nat → Nat → Nat → V
  | 0, _, _ => .inconclusive
  | fuel + 1, a, b => if a == b then .yes else if b == 0 then .no else checkLe fuel a (b - 1)

def digit [Monad G] [RandomChoice G] : G Nat := do return (← choose 0 9 (by omega)).down.val

def litRule [Monad G] [RandomChoice G] : Ty → BG G Expr
  | .nat => do return .lit (← lift digit)
  | _ => refute

def leRule [Monad G] [RandomChoice G] (initSize : Nat) : Ty → BG G Expr
  | .bool => do
    let a ← lift digit
    let b ← lift digit
    match checkLe initSize a b with
    | .yes => pure (.le a b)
    | .no => refute
    | .inconclusive => exhaust .inconclusive
  | _ => refute

def genHasType [Monad G] [RandomChoice G] (initSize : Nat) (τ : Ty) : Nat → BG G Expr
  | 0 => refutedToExhausted (backtrack [(1, fun () => litRule τ), (1, fun () => leRule initSize τ)])
  | size + 1 => backtrack [
      (1, fun () => litRule τ),
      (1, fun () => leRule initSize τ),
      (size + 1, fun () => match τ with
        | .pos => do return .succ (← genHasType initSize .nat size)
        | _ => refute)]

/-- Truncation decided per call: at size 0 the recursive rule is still offered, its conclusion still
matched against `τ`, and only a match is cut off (`exhaust .truncated`). Nothing is relabelled
wholesale: if no recursive rule could have applied, the disjunction was complete, and a refutation
stands. -/
def genHasType' [Monad G] [RandomChoice G] (initSize : Nat) (τ : Ty) : Nat → BG G Expr
  | 0 => backtrack [
      (1, fun () => litRule τ),
      (1, fun () => leRule initSize τ),
      (1, fun () => match τ with | .pos => exhaust .truncated | _ => refute)]
  | size + 1 => backtrack [
      (1, fun () => litRule τ),
      (1, fun () => leRule initSize τ),
      (size + 1, fun () => match τ with
        | .pos => do return .succ (← genHasType' initSize .nat size)
        | _ => refute)]

/-! ## The exact probability of each outcome -/

structure Report where
  ok : Rat
  refuted : Rat
  fuel : Rat
  truncated : Rat
  inconclusive : Rat

/-- Each outcome's probability. A run exhausted for several reasons counts toward each. -/
def report (g : BG WFinite Expr) : Report :=
  let es := (WFinite.entries? g.run).getD []
  let p (f : Outcome Expr → Bool) := (es.filter (f ·.1)).foldl (fun s (_, w) => s + w) (0 : Rat)
  let has (w : Why) : Outcome Expr → Bool | .exhausted ws => ws.contains w | _ => false
  { ok := p (· matches .ok _), refuted := p (· matches .refuted),
    fuel := p (has .fuel), truncated := p (has .truncated), inconclusive := p (has .inconclusive) }

def row (g : Nat → Ty → Nat → BG WFinite Expr) (τ : Ty) (initSize size : Nat) : String :=
  let r := report (g initSize τ size)
  s!"{repr τ}\tinit={initSize}\tsize={size}\tok={r.ok}\trefuted={r.refuted}\tfuel={r.fuel}\ttruncated={r.truncated}\tinconclusive={r.inconclusive}"

end Basalt.Examples.Enum.Exhaustion
