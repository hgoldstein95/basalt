/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
module

public import Basalt.Enum

/-!
# Local Backtracking with `exhaust`

First, `exhaust` on its own: two digits with a given sum, found, refuted, or out of budget; and a
geometric list conditioned on a property within a budget of choices.

Then a generator shaped like Specimen's derived code: `genHasType` from the Specimen bridge example
(failure as `OptionT`, branches combined by the bridge's `backtrack`). Its `isPos` rule draws `n`
and then checks the premise `n ≠ 0`, so it fails whenever it draws `0`, and backtracking cannot
recover, since for `bool` the other rules fail too. Meeting the premise with `exhaust` instead
looks at every value of the draw, keeps the ones that satisfy it, and never fails; given success,
the two have the same distribution.
-/

@[expose] public section

namespace Basalt.Examples.Enum.Local

open Basalt RandomChoice

/-- Two digits. Finite: every path costs two choices. -/
def digits : Poly (Nat × Nat) := fun _ _ => do
  let x := (← choose 0 9 (by omega)).down.val
  let y := (← choose 0 9 (by omega)).down.val
  pure (x, y)

/-- A geometric list of booleans: unbounded, so a budget can cut it off. -/
def geomList [Gen G] : G (List Bool) := do
  if (← choose 0 1 (by omega)).down.val = 0 then pure []
  else do
    let x := (← choose 0 1 (by omega)).down.val == 1
    let xs ← geomList
    pure (x :: xs)
partial_fixpoint

/-- The exact distribution of `g`. -/
def distOf [BEq α] (g : WFinite α) : List (α × Rat) := WFinite.dist ((WFinite.entries? g).getD [])

/-! ## A Specimen-shaped generator -/

inductive Ty | nat | bool
  deriving Repr, BEq

inductive Expr
  | lit (n : Nat)
  | isPos (n : Nat)
  | add (l r : Expr)
  deriving Repr, BEq

inductive Prog
  | expr (e : Expr)
  | both (e1 e2 : Expr)
  deriving Repr, BEq

/-! ## The bridge's `backtrack`: draw a branch by weight; on failure, drop it and draw again -/

def backtrack [Monad G] [RandomChoice G] (gs : List (Nat × (Unit → OptionT G α))) : OptionT G α :=
  go gs.length gs
where
  go : Nat → List (Nat × (Unit → OptionT G α)) → OptionT G α
    | 0, _ => failure
    | _, [] => failure
    | fuel + 1, gs => do
      let total := gs.foldl (fun t (w, _) => t + w) 0
      if total = 0 then failure else
      let r := (← OptionT.lift (choose 0 (total - 1) (Nat.zero_le _))).down.val
      let rec split : List (Nat × (Unit → OptionT G α)) → Nat →
          Option ((Unit → OptionT G α) × List (Nat × (Unit → OptionT G α)))
        | [], _ => none
        | (w, g) :: rest, r =>
          if r < w then some (g, rest) else (split rest (r - w)).map fun (g', rest') => (g', (w, g) :: rest')
      match split gs r with
      | none => failure
      | some (g, rest) =>
        match ← OptionT.lift (g ()).run with
        | some a => pure a
        | none => go fuel rest

def natGen [Monad G] [RandomChoice G] : G Nat := do return (← choose 0 100 (by omega)).down.val

/-! ## `genHasType`: the bridge's, and with the premise met by `exhaust` -/

/-- `isPos n` as derived: draw `n`, then check `n ≠ 0`. -/
def isPosDerived [Monad G] [RandomChoice G] : OptionT G Expr := do
  let n ← OptionT.lift natGen
  if n ≠ 0 then pure (.isPos n) else failure

/-- `isPos n` by enumerating the draw: every `n` with `n ≠ 0`, weighted as the draw weights it. -/
def isPosExhaust [Monad G] [RandomChoice G] : OptionT G Expr := do
  match ← OptionT.lift (exhaust 1 (fun _ _ => natGen) (· ≠ 0)) with
  | .found n => pure (.isPos n)
  | _ => failure

def genHasType [Monad G] [RandomChoice G] (isPos : OptionT G Expr) (τ : Ty) :
    (size : Nat) → OptionT G Expr
  | 0 => backtrack [
      (1, fun () => match τ with | .nat => do return .lit (← OptionT.lift natGen) | _ => failure),
      (1, fun () => match τ with | .bool => isPos | _ => failure)]
  | size + 1 => backtrack [
      (1, fun () => match τ with | .nat => do return .lit (← OptionT.lift natGen) | _ => failure),
      (1, fun () => match τ with | .bool => isPos | _ => failure),
      (size + 1, fun () => match τ with
        | .nat => do
          let l ← genHasType isPos .nat size
          let r ← genHasType isPos .nat size
          return .add l r
        | _ => failure)]

def genWellFormed [Monad G] [RandomChoice G] (isPos : OptionT G Expr) (size : Nat) : OptionT G Prog :=
  let ty : OptionT G Ty := do
    return if (← OptionT.lift (choose 0 1 (by omega))).down.val == 0 then .nat else .bool
  backtrack [
    (1, fun () => do return .expr (← genHasType isPos (← ty) size)),
    (1, fun () => do
      let τ ← ty
      return .both (← genHasType isPos τ size) (← genHasType isPos τ size))]

/-! ## Exact comparison -/

/-- The probability that `g` fails, and the distribution of what it produces otherwise. -/
def failAndDist [BEq α] (g : OptionT WFinite α) : Rat × List (α × Rat) :=
  let es := (WFinite.entries? (g.run : WFinite (Option α))).getD []
  let fail := (es.filter (·.1.isNone)).foldl (fun s (_, w) => s + w) 0
  (fail, WFinite.dist (es.filterMap fun (a, w) => a.map (·, w)))

def failure? (g : OptionT WFinite α) : Rat :=
  let es := (WFinite.entries? (g.run : WFinite (Option α))).getD []
  (es.filter (·.1.isNone)).foldl (fun s (_, w) => s + w) 0

/-- What `g` produces, given that it succeeds. -/
def given [BEq α] (g : OptionT WFinite α) : List (α × Rat) :=
  let (fail, d) := failAndDist g
  d.map fun (a, w) => (a, w / (1 - fail))

end Basalt.Examples.Enum.Local
