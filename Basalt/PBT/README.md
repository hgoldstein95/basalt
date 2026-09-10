# Property-based testing in Basalt

Basalt's generators are the *inputs* of property-based tests. This directory is the other half:
stating a property, and running it. The design in one sentence:

> A property is a generator that may reject the input it drew, so it is polymorphic in its monad,
> and one property term is testable at every interpretation of `Gen`.

The rest of this document is the *why*. For names, defaults, and flag spellings, read the
declarations — they own those facts. For a compiled tour of every feature below, read
[`BasaltTest/PBT.lean`](../../BasaltTest/PBT.lean); each snippet here has a counterpart there that
`lake build` checks.

## The three layers

| File | Owns |
|---|---|
| [`Property.lean`](Property.lean) | `PropM`, `Rejection`, `check` / `assume` / `forAll`, `Property` — what a property *is* |
| [`Campaign.lean`](Campaign.lean) | `runCampaign`, `CampaignReport`, and the failure contract every interpretation shares |
| [`Driver.lean`](Driver.lean) | `Backend`, `dispatch` — a command line over named properties |

Nothing here may name an interpretation. `Campaign.lean` bottoms out at `IO` because reporting is
`IO`, but a runner that needs a *particular* generator monad (a fuzzer, say) lives with that
interpretation and registers itself as a `Backend`.

## Stating a property

```lean
def prop_takeDrop [Gen G] : PropM G Unit := do
  let xs ← listOf (chooseNat 0 99)
  let k ← chooseNat 0 99
  assume !xs.isEmpty
  check (xs.take k ++ xs.drop k == xs) s!"xs={xs}, k={k}"
```

Three things are worth noticing.

**Inputs are drawn with `←`, not with a combinator.** Several inputs, or dependent ones, need no
`forAll2` and no tupling — this is just a `do` block in the generator monad. That falls out of the
monad-polymorphic representation and is the main ergonomic advantage over both Plausible and
QuickChick, where a multi-argument property is a curried function whose arguments a `Testable`
instance supplies.

**`assume` is a statement, not a nesting.** It rejects the input and stops everything after it.
QuickChick's `==>` (and Plausible's) wraps the rest of the property as an argument; `assume` is
available too as `implies` / `==>` when that reads better, but the flat form is the default.

### `forAll`, when you want the value named

```lean
def prop_insertMem [Gen G] : PropM G Unit :=
  forAll (Tree.genBST 0 99) fun t =>
    forAll (chooseInt 0 99 (by omega)) fun k =>
      k ∈ (t.insert k).preorder
```

`forAll gen p` draws from `gen`, runs `p`, and if `p` fails *anywhere inside* prefixes the drawn
value to the counterexample. Nesting composes, outermost value first. `p` may return a property, a
`Bool`, or a decidable `Prop` — the last two through the two coercions in `Property.lean`, which
coerce the *leaf* of a property and never its generator.

Use `←` when you want to name the variable and write your own message; use `forAll` when you want
the value reported for free.

## Why `PropM`?

A property has to be able to say three things: it passed, it failed (here is the counterexample), or
the input was rejected. That is a three-valued *result* — `TestOutcome` — and the obvious encoding
is to return it: `def prop [Gen G] : G TestOutcome`. Basalt did that first. The problem is that two
of the three values are not results at all; they are *aborts*.

Returning an outcome works inside one `do` block, because `return` is the block's own early exit
(this and the next snippet describe the abandoned design, so neither compiles today):

```lean
def prop [Gen G] : G TestOutcome := do
  let t ← Tree.genBST 0 99
  let k ← chooseInt 0 99 (by omega)
  if k ∈ t.preorder then return .discard        -- fine, here
  check ((t.insert k).size == t.size + 1)
```

It stops working the moment the precondition moves into a function — which is exactly what you want
to do with a precondition, since `k` being fresh for `t` is a fact about the input, not about this
one test:

```lean
def assumeFresh [Gen G] (t : Tree Int) (k : Int) : G TestOutcome :=
  pure (if k ∈ t.preorder then .discard else .ok ())

def prop [Gen G] : G TestOutcome := do
  let t ← Tree.genBST 0 99
  let k ← chooseInt 0 99 (by omega)
  let _ ← assumeFresh t k                       -- the rejection is DROPPED
  check ((t.insert k).size == t.size + 1)       -- ... and the test runs on a bad input
```

Nothing catches this. `G TestOutcome` bound with `←` yields a `TestOutcome` the caller is free to
ignore, so every call site has to `match` on the callee and re-`return` its rejection by hand, and
forgetting to is silent — the test still passes, on inputs it should never have seen. Reusable
preconditions are the first thing users factor out, and this representation cannot express one.

`PropM G` is `ExceptT Rejection G`, which makes rejection control flow instead of a value. `throw`
is not something a caller can drop, so `assume` propagates through calls, and so does a failing
`check`. Two further things follow:

- **`forAll` becomes a `try`/`catch`.** It can attach the drawn value to a failure raised anywhere
  inside the continuation, however deep. With outcomes as values, `forAll` would see only what the
  continuation chose to hand back, and a nested failure would have to thread its message up by hand.
- **It is free, and it changes nothing about generators.** `ExceptT ε g α` is *by definition*
  `g (Except ε α)`, so `PropM G Unit` is literally the `G TestOutcome` of the old design; the
  campaign runner took the change as a rename. And `PropM G` is itself a `Gen` (that is what the
  instances in `Property.lean` are for), so every generator combinator works inside a property with
  no `lift`, `partial_fixpoint` included.

The bill for that defeq comes in two hazards, both fenced on the declarations that carry them and
listed in [`CLAUDE.md`](../../CLAUDE.md)'s gotchas: `←` on a property inside a property silently
binds `Unit` rather than the outcome (go through `runProp` to *observe* an outcome), and an
`IO TestOutcome` argument does not determine `G` (ascribe `(prop : PropM IO Unit)` at the call site).

**`OptionT`** would not do instead: it is two-valued, so it can reject but cannot carry a
counterexample.

## Relation to QuickCheck, QuickChick, and Plausible

Read from the sources: QuickCheck 2.18's `Test.QuickCheck.Property` / `.Exception` / `.Test`,
QuickChick's `src/Checker.v` and `src/Test.v`, and Plausible's `Plausible/Testable.lean`.

| | QuickCheck | QuickChick | Plausible | Basalt |
|---|---|---|---|---|
| A property is | `Gen (Rose Result)` | `G QProp`, `QProp = Rose Result` | a `Prop`; `Testable p` supplies `Gen (TestResult p)` | `PropM G Unit`, i.e. `G (Except Rejection Unit)` |
| Its outcome | `ok :: Maybe Bool` | `ok : option bool` | `success` / `gaveUp n` / `failure` | `.ok ()` / `.error .discard` / `.error (.fail msg)` |
| Rejecting an input | `==>` wraps the rest; `discard` throws | `==>` wraps the rest | the precondition is a *hypothesis* of the statement | `assume` throws; `==>` also available |
| Reaches into a helper? | only via `discard`'s exception | no | only by factoring the *predicate* | yes |
| Naming the drawn value | `forAll` + a `counterexample` callback | `forAll` + a `printTestCase` callback | automatic, from `NamedBinder` | `forAll`, by catch-and-re-throw |
| Choosing the generator | implicit (`Arbitrary`) | implicit, or explicit in `forAll` | implicit (`SampleableExt`) | always explicit |
| Discards vs. the budget | separate (`maxDiscardRatio`) | separate (`maxDiscardedTests`) | consume it, after `numRetries` retries | separate (`maxDiscardRatio`) |

**The vocabulary and the outcome are the standard ones.** All four have the same three-valued
outcome — passed, failed with a counterexample, input rejected — and Basalt's `check` / `assume` /
`==>` / `forAll` mean what they mean elsewhere. Plausible's is the most refined: `TestResult p` is
*indexed by the proposition*, so `failure` carries a `¬p` and a reported counterexample cannot be a
false positive. Basalt gives that up by taking properties to be `Bool`-valued computations rather
than `Prop`s, and gets in exchange a property that is an ordinary monadic program.

**The one real deviation is that rejection is thrown rather than returned** — and it is the
deviation the older systems converged on too, from both directions:

- QuickCheck has exactly this mechanism, as a retrofit. Alongside the value-returning `==>` it
  exports `discard :: a`, whose doc comment says to use it when you want to drop a test case but are
  somewhere `==>` is unavailable, "such as inside a generator". It is implemented as
  `throw (ErrorCall "DISCARD. …")` and detected by *comparing the exception's message string*, with
  handlers installed by `protect` / `protectResult`. So: same idea, untyped, invisible in the type,
  and defeated by a user who catches `ErrorCall` or writes that message themselves.
- QuickChick cannot do that at all — Coq is pure — so its idiom moves rejection into the *generator*:
  constrained generators return `option`, and `forAllMaybe` discards on `None`. That is a rejection
  monad; QuickChick puts it on the generator side, Basalt puts it on the property side. (The seam
  shows in `Checker.v`, where `Checkable unit` is `checker rejected` under the comment "what's the
  relation between unit and discards?")
- Plausible's preconditions are hypotheses: `decGuardTestable` tests `∀ h : p, β h` by deciding `p`
  and returning `gaveUp 1` when it fails. That composes well at the `Prop` level — factor the
  predicate, give it a `Decidable` instance — but a helper that both *generates* and rejects is not
  expressible, because generating is not something a `Prop` does.

So Basalt is the typed, statically visible version of what QuickCheck bolted on and QuickChick
approximates: rejection appears in the property's type, cannot be silently dropped by a caller, and
needs no sentinel string.

**What Basalt does not have that all three do.** A `Testable`/`Checkable` instance for *functions*,
which is what makes `prop :: [Int] -> Bool` testable with no generator named. That is deliberate —
generators are Basalt's object of study and carry proofs about themselves, so an implicitly selected
instance would hide which generator's laws a test depends on — and it can be added on top of this
layer later. Also absent: Rose-tree shrinking, and `Result`'s stamps and callbacks (`collect`,
`classify`, `whenFail`); `Rejection` is where the latter would go.

**Accounting follows QuickCheck.** A discard has its own budget, `maxDiscardRatio * runs` with the
same default ratio of 10, and does not consume a run, so a property with a selective precondition
still gets the tests it asked for. Exhausting that budget sets `CampaignReport.gaveUp`, which is
reported as a failure and exits nonzero: a property whose precondition is unsatisfiable would
otherwise report success without ever having been tested. Plausible instead lets a discard consume
one of its `numInst` slots after retrying it `numRetries` times; that is the one place Basalt now
prefers QuickCheck's design to Plausible's.

## The discard budget is the outermost backtracking policy

Worth writing down because it is about to matter twice. A discard is a *rejected input*, and there
are only ever two things to do with one: give up on it and draw a fresh input (what `runCampaign`
does, up to the budget above), or back up to the nearest choice point and try a different branch
(what a constrained generator wants to do). Same signal, different retry scope — and the mechanism
that carries the signal is the same monad either way.

That is the connection to [Specimen's Basalt port](https://github.com/strata-org/specimen/blob/main/Docs/Specimen-Basalt-port.md),
which needs the local version. It proposes `BacktrackGen G α`, a newtype over `G (Option α)`, with a
`backtrack` combinator that drops a branch returning `none` and retries another, fuel-bounded by the
branch count. `G (Option α)` is `ExceptT Unit G α`; `PropM G` is `ExceptT Rejection G`. These are the
same construction at two scopes, and three things follow that are worth keeping in view before either
side hardens:

- **The `Gen (ExceptT ε G)` instances in [`Property.lean`](Property.lean) are what that port needs,**
  and they are already generic in `ε`: `Inhabited`, `PartialOrder`, `CCPO`, `MonoBind`,
  `RandomChoice`. The port's premise that Basalt's `Gen` has no failure story is out of date as of
  this directory. In particular `MonoBind` is the one that makes `partial_fixpoint` work through the
  transformer, which a recursive derived generator needs.
- **Fuel is not the only option for `backtrack`.** The port bounds retries by the branch count to get
  structural termination, and its appendix notes the cost: a fuel-bounded generator cannot reach
  everything satisfying `P`, which is why its correctness structure carries an extra `Bounded`
  side-condition. An unbounded retry written with `partial_fixpoint` has no such gap — completeness
  is recoverable — and its termination becomes an `IsAlmostSurelyTerminating` obligation, which is
  the one kind of obligation Basalt is actually built to discharge
  ([Basalt/SPMF/Ranking.lean](../SPMF/Ranking.lean)). That trade is worth making deliberately rather
  than by default.
- **One rejection type or two.** If the port lands its own newtype, a generator that can fail and a
  property that can reject are different monads, and composing them needs a hand-written
  `Option`-to-`Rejection` step at every boundary. Sharing `Rejection` instead makes a generator's
  failure *be* a discard, which is exactly what QuickChick's `forAllMaybe` does with a `GOpt`
  generator, and what makes "the generator could not satisfy the precondition" and "the property
  rejected this input" one budget rather than two.

None of that is settled here, and none of it blocks the current API — but a `retry` combinator
factored out of `runCampaign`'s loop is the shared primitive if we want one.

## Running one

`runCampaign` runs a property until it has tested the requested number of inputs, stopping at the
first counterexample, and returns a `CampaignReport` — it neither prints nor exits. That split is the
point: the reporting policy lives on the report, so every interpretation shares one failure contract
(counterexample on stderr, one exit code) and campaigns stay comparable across them. Rejected inputs
are budgeted separately; see the accounting note below.

```lean
#eval ioCampaign (fun _ => prop_takeDrop) 1000
```

`#eval` is the shortest path and needs nothing else. The argument is a `Property` — a property held
polymorphically, `(G : Type → Type) → [Gen G] → PropM G Unit` — which is why the campaign, not the
property, chooses the interpretation. `List (String × IO TestOutcome)` could not: the interpretation
would already have been picked when the list was built.

That explicit `(G : Type → Type)` binder is unusual-looking but load-bearing, and it is not unique
to Basalt: Strata-Generators' `Generable` class uses the same encoding for the same reason.

For an executable, `dispatch` turns a list of named properties into a `main`, with the backend and
the run budget on the command line; `Backend` is a list rather than an enumeration so that an
interpretation defined elsewhere can register itself. The available interpretations of `Gen`, and
what each is for, are in the [top-level README](../../README.md).

## Not here yet

Named so that their absence is a decision and not an oversight: **shrinking** (the fuzzer backend
shrinks by mutating inputs, so whether a shrinker belongs in the outcome or in the backend is open),
**statistics** (`collect` / `classify` — `#genstats` reports on generators, not on test runs),
**`expectFailure`**, **`conjoin` / `disjoin`**, the `Testable`-for-functions front end, and a
`backtrack` combinator for local retry. The two sections above say what each would look like.
