/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Michael Hicks
-/
import Basalt.Gen

/-!
# Properties

A property under test is a generator of `TestOutcome`, so its inputs are drawn with ordinary monadic
`do` — no combinator is needed for several or dependent inputs, and a precondition is a plain
`return .discard`:

```lean
def prop [Gen G] : G TestOutcome := do
  let xs ← listOf (chooseNat 0 99)
  let k ← chooseNat 0 99
  if xs.isEmpty then return .discard          -- a precondition
  checkWith (xs.take k ++ xs.drop k == xs) (fun () => s!"xs={xs}, k={k}")
```

Because a property is polymorphic in its monad, one term is testable at every interpretation of
`Gen`; `Basalt.PBT.Campaign` runs it, and `Property` is how it is passed around before an
interpretation is chosen.
-/

namespace Basalt.PBT

/-- The result of a property on one input: `pass`, `fail` (with a counterexample rendered on demand),
or `discard` (a precondition rejected the input). -/
inductive TestOutcome where
  | pass
  | fail (render : Unit → String)
  | discard

/-- The leaf of a property: `pass` iff `b`, with no counterexample detail. -/
def check [Gen G] (b : Bool) : G TestOutcome :=
  pure (if b then .pass else .fail (fun () => "(no counterexample detail)"))

/-- Like `check`, but attaches a rendered counterexample on failure. Build the description from the
values drawn earlier in the `do` block (e.g. `fun () => s!"x={x}, y={y}"`). -/
def checkWith [Gen G] (b : Bool) (render : Unit → String) : G TestOutcome :=
  pure (if b then .pass else .fail render)

/-- A precondition in terminal position: reject this input (`discard`) unless `c` holds. Earlier in a
`do` block, `if !c then return .discard` short-circuits the rest. -/
def assume [Gen G] (c : Bool) : G TestOutcome :=
  pure (if c then .pass else .discard)

/-- The single-input case: draw from `gen` and check `p`, reporting the drawn value as the
counterexample. -/
def forAll [Repr α] [Gen G] (gen : G α) (p : α → Bool) : G TestOutcome := do
  let a ← gen
  checkWith (p a) (fun () => reprStr a)

/-- A property still polymorphic in its monad. The explicit `G` binder is what lets a caller choose
the interpretation to test at (`T IO`, `T Plausible.Gen`, …); `List (String × IO TestOutcome)` could
not. -/
def Property := (G : Type → Type) → [Gen G] → G TestOutcome

end Basalt.PBT
