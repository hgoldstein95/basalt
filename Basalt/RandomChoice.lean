/-- A typeclass for monads that support sampling random `Nat`s
    in the interval `[lo, hi]` -/
class RandomChoice (m : Type → Type) where
  choose : (lo hi : Nat) → (h : lo ≤ hi) → m Nat

/-- Picks between two (thunked) generators, each with probability 0.5 -/
def RandomChoice.pick [Monad m] [RandomChoice m] (x y : Unit → m α) : m α := do
  if (← choose 0 1 (by simp)) == 0 then x () else y ()

/-- Biased coin-flip with success probability `r` -/
def RandomChoice.coin [Monad m] [RandomChoice m] (r : Rat) : m Bool := do
  if (← choose 0 r.den (by simp)) < r.num then pure true else pure false

/-- Samples an element randomly from the input list `xs` -/
def RandomChoice.elements
  [Monad m]
  [RandomChoice m]
  [Inhabited α]
  (xs : List α) : m α := do
  let idx ← RandomChoice.choose 0 xs.length (by simp)
  pure xs[idx]!

/-- Picks a generator from a list of generators -/
def RandomChoice.oneOf
  {m : Type → Type}
  {α : Type}
  [Monad m]
  [RandomChoice m]
  [Inhabited (m α)]
  (gs : List (Unit → m α)) : m α := do
  let idx ← RandomChoice.choose 0 gs.length (by simp)
  gs[idx]! ()

def RandomChoice.oneOf'
  {m : Type → Type}
  {α : Type}
  [Monad m]
  [RandomChoice m]
  [Inhabited (m α)]
  (gs : List (Unit → m α)) (default : Unit → m α) : m α :=
  match gs with
  | [] => default ()
  | [g] => pick g default
  | _ => List.foldl (fun acc g => pick g (fun () => acc)) (default ()) gs



open Lean.Order

/-- Proof that if the two arguments to `pick` are monotone, then
    the resultant generator is also monotone  -/
@[partial_fixpoint_monotone]
theorem RandomChoice.monotone_pick
    [∀ α, PartialOrder (m α)]
    [Monad m]
    [MonoBind m]
    [RandomChoice m]
    [PartialOrder α]
    {x y : (α → m β)}
    (hx : monotone (fun a => x a))
    (hy : monotone (fun a => y a)) :
    monotone (fun (a : α) => pick (fun () => x a) (fun () => y a)) := by
  simp [pick]
  apply monotone_bind
  . apply monotone_const
  . refine monotone_of_monotone_apply _ fun ref => ?_
    apply monotone_ite
    . assumption
    . assumption
