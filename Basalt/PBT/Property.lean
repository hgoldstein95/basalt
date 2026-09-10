/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Michael Hicks, Harrison Goldstein
-/
import Basalt.Gen

/-!
# Properties

A property is the easiest top-level way into using Basalt for PBT; it is represented under the hood
as a generator of test results (pass, fail, or discard). The following property does some sampling,
makes some assumptions that discard invalid data, and then checks a predicate.

```lean
def prop [Gen G] : Property := do
  let xs ← generate (listOf (chooseNat 0 99))
  let k ← generate (chooseNat 0 99)
  assume !xs.isEmpty                          -- a precondition
  check (xs.take k ++ xs.drop k == xs) s!"xs={xs}, k={k}"
```
-/

namespace Basalt.PBT

/-- Why a test did not pass. -/
inductive Rejection where
  /-- The test failed, with sampled inputs represented in `counterExample`. -/
  | fail (counterExample : String)
  /-- The test was skipped because a generated input was discarded. -/
  | discard
  deriving Inhabited

/-- The outcome of one test. `.ok ()` passed; `.error` carries the reason it did not.  -/
abbrev TestOutcome := Except Rejection Unit

/-! ## The Property Monad -/

/-- Note, this is definitionally equal to `G TestOutcome`, but the monad instance threads failure
and discards better. -/
abbrev PropM (G : Type → Type) := ExceptT Rejection G

def generate [Gen G] (g : G α) : PropM G α := ExceptT.lift g

/-! ## Stating a property -/

/-- `pass` iff `b`, with `msg` as the counterexample. -/
def check [Gen G] (b : Bool) (msg : Thunk String := "") : PropM G Unit :=
  if b then pure () else throw (.fail (Thunk.get msg))

/-- A precondition: reject this input unless `c` holds. Unlike a bare outcome value, this
short-circuits — the rest of the `do` block does not run, and neither does the rest of a *caller's*
block. -/
def assume [Gen G] (c : Bool) : PropM G Unit :=
  if c then pure () else throw .discard

/-- A precondition written around the rest of the property rather than before it (QuickChick's
`implication`). `assume c` is the same thing in statement position. -/
def implies [Gen G] (c : Bool) (p : PropM G Unit) : PropM G Unit := do
  assume c
  p

@[inherit_doc] scoped infixr:55 " ==> " => implies

/-- Prefix `outer` to `inner`, which may be the empty message a bare `check` leaves. -/
private def joinDetail (outer inner : String) : String :=
  if inner.isEmpty then outer else s!"{outer}, {inner}"

/-- Draw from `gen` and check `p` of the result, naming the drawn value in the counterexample.

`p` returns a property rather than a `Bool` so that `forAll`s nest, each layer adding its own value
to the counterexample; a `Bool` still works, through the coercion below.

The `try`/`catch` is not decoration: `let r ← (p x).run` instead would elaborate, because
`G TestOutcome` unifies with `PropM G Unit` before the do-block's automatic lift is tried, and `r`
would silently be `Unit`. -/
def forAll [Repr α] [Gen G] (gen : G α) (p : α → PropM G Unit) : PropM G Unit := do
  let x ← gen
  try
    p x
  catch
    | .fail r => throw (.fail (joinDetail (reprStr x) r))
    | .discard => throw .discard

/-- A `Bool` is a property with no counterexample detail of its own, so `forAll gen (· < 9)` reads
as it did before `forAll` took a continuation. -/
instance instCoeBoolPropM [Gen G] : CoeTail Bool (PropM G Unit) := ⟨check⟩

/-- A decidable `Prop` is a property too, so `forAll gen (fun n => n ≤ 9)` reads as it would in
Plausible — one `decide` away from the `Bool` case.

`CoeDep`, not `CoeTail`, and `p` explicit: the proposition has to be an argument for `Decidable p`
to have a synthesization order (this is how Lean's own `Prop`-to-`Bool` coercion is stated). These
two instances are the API's only ones — they coerce the *leaf* of a property, never its generator,
which stays explicit. -/
instance instCoeDecidablePropM [Gen G] (p : Prop) [Decidable p] : CoeDep Prop p (PropM G Unit) :=
  ⟨check (decide p)⟩

/-- One test at a chosen interpretation: the property as a plain generator of its outcome.

`PropM G Unit` is definitionally `G TestOutcome`, so this is `ExceptT.run` and costs nothing — but a
runner must go through it, and so must anything that wants to *observe* an outcome. Without it, `←`
on a property inside a `do` block infers the block's monad as `PropM G` and yields the property's
`Unit`, hiding the outcome rather than reporting it. -/
def runProp [Gen G] (p : PropM G Unit) : G TestOutcome := p.run

/-- A property still polymorphic in its monad. The explicit `G` binder is what lets a caller choose
the interpretation to test at (`T IO`, `T Plausible.Gen`, …); `List (String × IO TestOutcome)` could
not. -/
def Property := (G : Type → Type) → [Gen G] → PropM G Unit

end Basalt.PBT
