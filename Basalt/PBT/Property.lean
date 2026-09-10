/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Michael Hicks
-/
import Basalt.Gen

/-!
# Properties

A property is a generator that can *reject* the input it drew, so it lives in `PropM G`, an
`ExceptT` over the generator monad. Rejecting short-circuits, so a precondition is a statement and
not a nesting, and inputs are drawn with ordinary monadic `do`:

```lean
def prop [Gen G] : PropM G Unit := do
  let xs ← listOf (chooseNat 0 99)
  let k ← chooseNat 0 99
  assume !xs.isEmpty                          -- a precondition
  check (xs.take k ++ xs.drop k == xs) s!"xs={xs}, k={k}"
```

Because a property is polymorphic in its monad, one term is testable at every interpretation of
`Gen`; `Basalt.PBT.Campaign` runs it, and `Property` is how it is passed around before an
interpretation is chosen.
-/

namespace Basalt.PBT

/-- Why a test did not pass: a counterexample or a precondition that rejected the input. Passing
needs no constructor — it is `Except.ok`, so a property that fails to report cannot be mistaken for
one that passed. -/
inductive Rejection where
  | fail (message : String)
  | discard
  deriving Inhabited

/-- The outcome of one test. `.ok ()` passed; `.error` carries the reason it did not. -/
abbrev TestOutcome := Except Rejection Unit

/-! ## The property monad

`PropM G` is `ExceptT Rejection G`, so `PropM G Unit` is definitionally `G TestOutcome` — a runner
can take a property as a plain generator of outcomes, and the instances below are all that stand
between the two views. -/

abbrev PropM (G : Type → Type) := ExceptT Rejection G

instance instRandomChoiceExceptT [Monad g] [RandomChoice g] : RandomChoice (ExceptT ε g) where
  choose lo hi h := ExceptT.lift (RandomChoice.choose lo hi h)

instance [Gen G] : Gen (PropM G) where
  instCCPO := inferInstance
  instInhabited := fun _ => instInhabitedExceptTOfMonad
  instMonad := inferInstance
  instRandomChoice := instRandomChoiceExceptT
  instMonoBind := inferInstanceAs (Lean.Order.MonoBind (ExceptT Rejection G))

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
