# Generator Creation Workflow

Basalt provides a foundation for provably correct and efficient data generators. It can be used in
conjunction with property-based testing frameworks in Lean and other languages to find a wide range
of bugs in code.

This file provides a workflow for creating your own generator and proving it correct. The first half
covers writing the generator; the second half gives a **recipe for each of the three proof
obligations**, as a skeleton with named holes. The recipes are written so that every step is a
standard tactic with a local, legible failure mode — follow them mechanically and the failures tell
you what to fix.

The worked instances live in `BasaltExamples/`; each recipe below names the examples that follow it
verbatim.

## Part 1: Writing the Generator

### Step 0: Choose a Data Type

Determine a type `α` of data that you would like to generate. If you are generating data for
consumption by another language, you will likely want to make a bespoke inductive data type in Lean
that mirrors your data structures in your implementation language.

Do **not** use a dependent type for `α`. Rely on your validity predicate (Step 1) to constrain the
data.

### Step 1: Define Validity

Determine what it means for your data to be _valid_. This should be a predicate `P` of type `α →
Prop`, and `P a` should be `True` iff `a` is a valid input to your system under test.

Advanced users might want to target specific sub-spaces of their data type for testing (e.g.,
well-typed programs vs. ill-typed but well-scoped programs). In that case, we recommend going
through this process multiple times for each sub-space, rather than trying to do all sub-spaces at
once.

### Step 2: Set a Cost Bound

Determine a reasonable cost bound for generation: a function `c : α → Nat` such that producing the
value `v` never takes more than `c v` random choices. Count the choices your generator makes per
constructor of the output:

- each `chooseNat` / `choose` / `elements` is 1 choice;
- each `oneOf` / `frequency` is 1 choice *plus* the cost of the selected branch;
- a call to another generator costs whatever that generator's bound says.

For a list generator that flips a coin per element, the bound is `fun xs => xs.length + 1` (one
`oneOf` per cons, one for the nil). When a generated *value* feeds a later recursion (e.g.
`Nat.arbitrary` producing an `n` by counting coin flips), the value itself shows up in the bound
(`fun n => n + 1`).

Keep the bound *tight*: a precise bound is what catches accidental backtracking or other
inefficiency, and (see the cost recipe) a too-tight bound fails as a legible `omega` goal that
shows you exactly which term is missing.

### Step 3: Create and Validate Your Generator

Create a generator of the appropriate type:

```lean
def myGen [Gen G] : G α := ...
```

We use a type-class embedding of generators because it works well with our proof infrastructure
(see `Gen.lean`): the same term runs at `Plausible.Gen`/`IO` and is reasoned about at `SPMF`.

Guidelines that make the proofs go smoothly:

- **Prefer `chooseNat lo hi h` over raw `choose`.** `choose` returns a
  `ULift {x : Nat // lo ≤ x ∧ x ≤ hi}`, which costs `.down.val` projections in the generator and
  `⟨⟨n, ⟨hge, hle⟩⟩⟩` destructuring in every proof. `chooseNat` returns a bare `Nat`, and a proof
  sees its range as plain inequalities that `omega` consumes directly.
- **Use `chooseInt` when the recursion subtracts from the bounds.** `Nat` truncation turns the
  empty interval `[lo, lo - 1]` into the singleton `[0, 0]` at `lo = 0`, silently widening the
  generator's support — and the matching predicate is wrong in the same way, so the support proof
  still goes through. `Tree.genBST` (`BasaltExamples/BST.lean`) recurses on `[lo, x - 1]` and takes
  `Int` bounds for exactly this reason.
- **Recursive generators use `partial_fixpoint`** (Lean's CCPO fixpoint). Any combinator appearing
  in the recursive body needs a `@[partial_fixpoint_monotone]` lemma; the library's own combinators
  carry theirs (grep for the `@[partial_fixpoint_monotone]` tag for the current list), and
  combinators that don't mention the recursive call (like `chooseNat`) need nothing.
- **Weighted choices go through `frequency`**, one n-ary choice per site, with the weights inline.
  Tag the definition `@[tunable]` to make the weights runtime-addressable later (see
  `Basalt/Tuning/Attr.lean` and `BasaltTest/Tuning.lean`); it changes nothing about the proofs below.
- Sample it (`#eval`, or `#genstats` for distribution statistics) before proving anything. A
  generator whose median output is trivial passes every proof below and is still useless.

## Part 2: The Three Proof Obligations

For a total generator, the properties to prove are these three (`Basalt/Laws.lean`, where they
are plain `def`s — there is no bundle to instantiate). A *filtering* generator is the exception: its
mass is below 1, so termination is replaced by `IsProductive` / `IsFilterFree` on the `Option`
interpretation.

| Obligation | Statement shape | Meaning |
|---|---|---|
| Support | `IsSoundAndComplete g P`, i.e. `∀ a, a ∈ SPMF.support g ↔ P a` | Soundness and completeness: nothing invalid is produced, nothing valid is missed. |
| Termination | `IsAlmostSurelyTerminating g`, i.e. `SPMF.IsPMF g` (`mass g = 1`) | The generator terminates with probability 1. |
| Cost | `IsCostBounded g c`, i.e. `IsBounded g c` | Producing `v` takes at most `c v` random choices. |

Each has a fixed recipe, and every recipe is the same walk over one step of the recursion: a tactic
pushes the judgment's postcondition backward through the generator's syntax, closes recursive
occurrences and callees itself, and leaves what only you can supply — logic about `P`, or
arithmetic. Support is two judgments, one per direction of its `↔`. What differs between judgments
is the algebra the walk computes in, the direction of the bound, and who supplies the induction:

| Judgment | Observation | Algebra | Bound | Induction | What is left |
|---|---|---|---|---|---|
| Soundness, `IsSound g P` | `SPMF.alwaysObs` | demonic: `∀`, `∧` | lower, by `True` | `sound_fixpoint` | one goal per path: `P` of the value it built |
| Completeness, `a ∈ SPMF.support g` | `SPMF.mayObs` at `(· = a)` | angelic: `∃`, `∨` | lower | yours, on the value or on `P` | one goal: an `∃` per draw, an `∨` per choice, recursive occurrences as themselves |
| Termination, `c ≤ g.mass` | `SPMF.expectObs` at `1` | average | lower | `mass_fixpoint using <certificate>` | `F c ≤ <computed bound>`, in `ℝ≥0∞` |
| Cost, `IsCostBounded g c` | `SPMF.Cost.alwaysObs` | demonic | lower, by `True` | `cost_fixpoint` | one arithmetic goal per path |
| Expected value, `SPMF.expect g f ≤ B` | `SPMF.expectObs` | average | upper | `expect_fixpoint` | `<computed bound> ≤ B`, in `ℝ≥0∞` |

The induction column is forced. Fixpoint induction proves what holds of the generator that never
returns and survives a step: a `∀` over the support, an upper bound on an expectation. Reaching a
value and having mass `1` are lower bounds on a least fixed point, false of that generator, and need
a ranking (Hark et al., "Aiming Low Is Harder") — a certificate for termination, your induction for
completeness. That is why there is no `complete_fixpoint`.

**A generator that post-processes another** (`let x ← g; return f x`) has no recursion to unfold,
and every obligation reduces to composition instead: the recipes unchanged, with
`mass_fixpoint using SPMF.LfpIsOne.one` for termination. `List.genSortedBySorting`
(`SortedList/BySorting.lean`) is the worked instance — it sorts a `List.arbitrary` draw, and each
law follows from the corresponding law of `List.arbitrary`, which the walk finds, plus one fact
about `f`: that sorting sorts, that it fixes a sorted list, that it is a permutation. Cost is the
obligation that can fail outright for this shape (Step 2).

**Name the laws `<GEN>.sound_complete`, `<GEN>.terminates`, `<GEN>.cost_bounded`.** The dot is not
cosmetic: `#genstats` discovers laws by exactly this naming convention and reports which ones a
generator carries beside the statistics it merely *measured*, and the walk closes a callee by the
same convention (`lawConventions`, `Basalt/Walk/Attr.lean`). A law under any other name is invisible to the report — the generator will show
`— (not proved)` for something you proved. The statement is checked too, not just the name, so a
conventionally-named theorem that says something else cannot be laundered into a ✓. Automated
synthesis that emits the same convention reports identically to hand-written generators.
(`IsFilterFree`/`IsProductive`, for filtering generators, are `.filter_free` and `.productive`.)
A generator that has only one half of the support law — a size-bounded generator is sound and
deliberately incomplete — names it `<GEN>.sound` or `<GEN>.complete`; the two together count as
`.sound_complete`, to `#genstats` and to the walk.

### Unfolding: one idiom per context

`partial_fixpoint` definitions unfold three ways, and picking the wrong one gives confusing errors:

| Context | Idiom |
|---|---|
| Completeness step, goal `a ∈ SPMF.support (gen …)` (soundness needs none: `sound_fixpoint` unfolds) | `rw [gen]` (the equation lemma) |
| Mass bound by hand (rewrite only one side of `≤`/`≥`) | `conv_rhs => rw [gen]` (or `conv_lhs`) |
| Under binders where `rw` fails | `unfold gen` |

### Recipe 1: Support

Worked instances: `Tree.genHeap.sound_complete` (`Heap.lean`) is the recipe verbatim;
`Tree.genBST.sound_complete` (`BST.lean`) has a `dite`, a `frequency`, and a pivot;
`Tree.genLeftistOfRank.sound_complete` (`LeftistHeap.lean`) is defined by `match` and draws a value
its predicate must solve for; `String.arbitrary_support` (`ArbString.lean`) goes through a list
combinator.

```lean
theorem <GEN>.sound_complete : IsSoundAndComplete (<GEN> <IDX>) (<PRED> <IDX>) := by
  refine .intro ?sound ?complete
  case sound =>
    sound_fixpoint                      -- one goal per path: `<PRED>` of the value that path built
    all_goals simp_all [<PRED>]
  case complete =>
    intro x
    -- 1. Induct on the generated value, generalizing any index the recursion changes.
    induction x generalizing <IDX> with
    | <base case> => intro _; rw [<GEN>]; complete_bound
    | <recursive case> ... ih₁ ih₂ =>
      intro ⟨...facts...⟩
      -- 2. The only creative step in the whole proof: inverting the index arithmetic — if the
      --    recursion ran at `lo + d` and you know `lo ≤ x`, then `x` is `lo + d` for `d := x - lo`.
      obtain ⟨d, rfl⟩ : ∃ d, x = lo + d := ⟨x - lo, by omega⟩
      rw [<GEN>]; complete_bound        -- 3. unfold one step and walk it
      exact ⟨d, l, ih₁ ‹_›, r, ih₂ ‹_›, rfl⟩   -- 4. a witness per draw; the IHs for recursive ones
```

**`sound_fixpoint`** (`Basalt/Tactic/Sound.lean`) inducts over the arguments some recursive
call of `<GEN>` changes, unfolds one step, and runs `sound_bound` (`Basalt/Tactic/Sound.lean`),
which is `cost_bound` at the support interpretation: one goal per path, the drawn values and what is
known of them in context under the generator's names. A recursive occurrence is closed by `ih`, a
callee by its `.sound_complete` or `.sound` law, anything else by a fact: `sound_fixpoint [h]`.
`BasaltTest/Tactic/Sound.lean` shows the goals `genHeap`, `genBST`, and `genLeftist` leave.

**`complete_bound`** (`Basalt/Tactic/Complete.lean`) turns `a ∈ SPMF.support (<GEN> …)`, after one
unfolding, into a precondition for the step to produce `a`: an `∃` for each draw, an `∨` for each
choice, and last the equation between `a` and the value built. On `IsCompleteFor g P` it introduces
`a` and `P a` first. `BasaltTest/Tactic/Complete.lean` shows the goals. What to expect of it:

- a **callee** contributes its predicate, from its `.sound_complete` or `.complete` law; a fact is
  passed as `complete_bound [h]`.
- a **recursive occurrence** stays as itself, `∃ l ∈ SPMF.support (<GEN> (lo + d)), …`. No tactic can
  close it: the hypothesis that does is about one value, and comes from the induction *you* chose.
  That induction is ordinary Lean — on the value, or on `<PRED>` with `fun_induction`.
- a **branch that cannot produce `a`** is pruned — a constructor clash, a weight that is `0` — and a
  base case usually closes outright. It never chooses between branches that survive: that is
  `Or.inl` / `Or.inr`, and a conditional your facts decide is `rw [dif_neg (by omega)]`
  (`Tree.genBST`).

Notes:

- **A combinator that takes a generator** (`listOf`, `vectorOf`, …) asks for that generator's
  soundness or completeness, for a predicate of the argument's own, and states the list's in terms
  of it. A callee's law supplies it. A combinator term in that position has no law: prove its two
  halves, each one `sound_bound` or `complete_bound`, and pass them
  (`Tree.genBSTByInsertion.sound_complete`, `BST/ByInsertion.lean`).
- **A generator defined by `match` on its arguments** is split into its cases before the walk, by
  every tactic here.
- **Completeness by a measure**, when no structural induction fits or the script has to be fixed in
  advance: `apply IsCompleteFor.of_measure μ fun n ih s a hn hP => ?_` and then
  `rw [<GEN>]; complete_bound` leave a goal with no generator in it. `μ` is a measure of seed and
  value that every recursive call decreases (`BasaltTest/Tactic/Complete.lean`).
- **A law that transfers along a support equation** is `IsSoundAndComplete.of_support_eq`, or the
  callee's law applied to the value: `List.genSorted.sound_complete` (`SortedList.lean`).

### Recipe 2: Termination

Every termination proof is one criterion, `SPMF.IsPMF_of_lfp_eq_one` (`Basalt/SPMF/Termination.lean`):
if one unfolding bounds the generator's mass below by `F c` whenever `c` bounds it below, and `F`'s
least fixed point is `1` (`LfpIsOne F`), the generator is a PMF. Outside the shrinking-seed regime
the proof is the tactic and the arithmetic:

```lean
theorem <GEN>.terminates : IsAlmostSurelyTerminating (<GEN> <ARGS>) := by
  mass_fixpoint using <CERTIFICATE>
  simp                      -- the goal left is `F c ≤ <computed bound>`, pure ℝ≥0∞
```

What you choose is the **certificate** for `F`, read off the generator's branches. A generator with
no recursion — including one that only post-processes a callee — is the first row:

| Generator | Certificate | `F c` |
|---|---|---|
| No recursive call | `SPMF.LfpIsOne.one` | `1` |
| Mean offspring `m < 1` | `SPMF.LfpIsOne.affine (m := m) h` | `(1 - m) + m * c` |
| At most two calls, mean offspring `≤ 1` (critical included) | `SPMF.LfpIsOne.quadratic (a := _) (b := _) (d := _) h₁ h₂ h₃` | `a + b * c + d * c ^ 2` |
| Shrinking seed, mean offspring `> 1` | `SPMF.LfpIsOne.ranking …` with `mass_fixpoint per_seed` (below) | a function of `c` and the seed |

`m` is weights-on-recursive-branches over total weights, counting each branch once per recursive
call: a two-branch `oneOf` with one recursive branch has `m = 1/2`;
`frequency [(2, leaf…), (1, node…)]` with two calls in `node` has `m = 2·(1/3) = 2/3`, or, as a
quadratic, `a = 2/3`, `d = 1/3`; a two-branch `oneOf` between a leaf and two calls is the quadratic
`a = d = 1/2`. **A critical generator
(`m = 1`) terminates but has infinite expected size** (`AllTwoTree.genTree_expectedSteps_infinite`)
— reweight it if you can. The side conditions of a certificate are closed numerals: `by norm_num`,
or `by ennreal_to_real; norm_num`.

**`mass_fixpoint`** reads the seed off `<GEN>.fixpoint_induct` (the arguments some recursive call
changes; a tuple of them, or none), unfolds one step, and runs `mass_bound`. It leaves `c`,
`hc1 : c ≤ 1`, `hrec` (the bound on every recursive occurrence), and the seed under its own binder
names in context. Without `using`, the goal left is `LfpIsOne <computed bound>` instead, to be
finished with `SPMF.LfpIsOne.mono` and a certificate (`BasaltTest/Tactic/MassFixpoint.lean`).

**`mass_bound` is the whole structural argument.** It walks the unfolded generator and *computes* a
lower bound on its mass. Mass is the expectation of `1`, and the walk pushes that postexpectation
backward: a draw is bounded at the bound its continuation computed, so the bound comes out in the
shape of the do-block and is exact wherever the generator's callees are
(`Basalt/Tactic/Mass.lean` owns how a fact is used, `Basalt/Tactic/Average.lean` the bound of
each shape of choice, `Basalt/Walk/Basic.lean` the walk; `BasaltTest/Tactic/Mass.lean` shows a generator
that uses every combinator). Nothing about the generator is yours to supply:

- a **recursive occurrence** is discharged by `hrec`, whatever the shape of the seed.
- a **callee** is discharged by its own `<callee>.terminates` law, found by the naming convention
  (Part 2 above) — `Nat.arbitrary` inside a body needs no mention. Any other fact is passed
  explicitly: `mass_fixpoint [h₁, h₂] using …`.
- a **helper with no law**, or a derived combinator (`optionGen`, `BasaltTest/OptionGen.lean`), is
  unfolded and walked through when it is not recursive.
- an **`if`/`dite`** is no different from any other combinator: the bound is the same conditional
  over the branches' bounds, which the arithmetic `split`s — `Tree.genBST` (`BST.lean`) shortcuts on
  an exhausted interval. A conditional on a value drawn inside the step belongs to that draw's
  postexpectation: after a `coin` it is the weighted sum of the branches' bounds, and when the
  branches have one bound it is that bound. `Tree.genLeftist` (`LeftistHeap.lean`) ends its
  recursive branch in an `if` that orders the two children and `Tree.genHeap` (`Heap.lean`) does
  not, and their termination proofs are the same text.

**The arithmetic** has your `F c` on the left, the computed bound on the right, and no generator in
sight. Try `simp` (`ArbNat.lean`, `SortedList.lean`), then `simp` with the identities the goal needs
(`simp [sq, ENNReal.div_eq_inv_mul, mul_add]` in `LeftistHeap.lean` and `AllTwoTree.lean`), then
`ennreal_to_real` (`Basalt/Tactic/ENNReal.lean`) and `nlinarith`. If it looks *false*, your
certificate is wrong, not your proof. A generator that is not a `Gen` term, or whose seed has an
argument typed by another, goes through `SPMF.IsPMF_of_lfp_eq_one_uniform` on an explicit family
(`SPMF.IsPMF_retry`, `Basalt/SPMF/Failure.lean`). A bare combinator term, which has no definition
to unfold, is `SPMF.IsPMF.of_one_le` and `mass_bound` (`BasaltTest/Combinators.lean`). A generator
recursive by `termination_by` has no fixpoint: induct on its decreasing argument and close each case
with the same two (`BasaltTest/Tactic/MassFixpoint.lean`).

**Shrinking seed** (`Tree.genWeightedBST`, `BST/Weighted.lean`) is the one regime with real
content, and the one where the bound is not a single `F c`: `mass_fixpoint per_seed` takes the
bound family `c` and the computed bound `T c seed` as functions of the seed, and leaves
`LfpIsOne T`. You supply a ranking function `φ : Seed → ℝ≥0∞` whose expected value drops by `ε` at
every step, and `SPMF.LfpIsOne.ranking` (`Basalt/SPMF/Ranking.lean`) discharges the certificate,
with `E[#steps] ≤ φ/ε` as a byproduct. Its obligations are a `LevelOp` `A` (three algebra laws), a
drift lemma (`A φ + ε ≤ φ` — pure arithmetic about your rank), and the deficit condition
`1 - T c seed ≤ A (1 - c) seed` — arithmetic about `T`, with no generator in sight, pushed through
the branches by `ENNReal.one_sub_le_mul_one_sub`, `one_sub_sum_div_le`, and `one_sub_mul_le_add`.
A uniform pivot's continuation has a bound that depends on the pivot, which `mass_bound` computes
as the average over the range. Follow `genWeightedBST_drift`/`genWeightedBST.terminates`.
Two things to know:

- Candidate `φ`s, in order: the seed measure; `≡ const` (that's the static-seed case); seed measure
  plus a depth term. Evaluate the drift in the seed's *actual* arithmetic: `bstRank` is the plain
  interval measure and the children's ranks sum to the parent's at every pivot, but that holds
  because the bounds are `Int`. Under `Nat` bounds the `lo = 0` pivot has an unshrunk child and the
  same `φ` fails its drift check — a truncating seed costs you a correction term in the rank.
- A wrong `φ` is a *failed drift check*, never a wrong theorem. Guess freely.

### Recipe 3: Cost

Worked instances: `Nat.arbitrary.cost_bounded` (`ArbNat.lean`) is the minimal case;
`Tree.genHeap.cost_bounded` (`Heap.lean`) has a callee and two recursive calls;
`Tree.genBST.cost_bounded` (`BST.lean`) has a `dite`, a `frequency`, and a pivot; and
`List.genSortedBySorting.cost_bounded` (`SortedList/BySorting.lean`) has no recursion at all.

```lean
theorem <GEN>.cost_bounded : IsCostBounded (<GEN> <ARGS>) <COST> := by
  cost_fixpoint
  all_goals simp only [<COST>'s equations]; omega   -- one goal per path through <GEN>
```

**`cost_fixpoint`** (`Basalt/Tactic/Cost.lean`) inducts over the arguments some recursive
call of `<GEN>` changes, unfolds one step, and runs `cost_bound`. A generator with no recursion is
unfolded and walked.

**`cost_bound` is the whole structural argument.** It pushes the postcondition "producing `v` took
at most `<COST> v` choices" backward through the step, by the same walk as `mass_bound` — the tally
of Step 2 is what it computes. It leaves one goal per path through the generator,
stated over the values that path drew; the walker (`Basalt/Walk/Basic.lean`, "Names") says how
they are named, and `BasaltTest/Tactic/CostFixpoint.lean` shows the goals `genHeap` and `genBST`
leave. Nothing about the generator is yours to supply:

- a **recursive occurrence** is bounded by `ih`, at whatever arguments it is called with.
- a **callee** is bounded by its own `<callee>.cost_bounded` law, found by the naming convention
  (Part 2 above). Any other cost bound is passed explicitly: `cost_fixpoint [h₁, h₂]`. A
  non-recursive helper with no law is unfolded and walked through instead.
- a **combinator that takes a generator** (`listOf`, `vectorOf`, …) asks for that generator's cost
  law the same way, and the goal states the combinator's bound in terms of it —
  `String.arbitrary_cost` (`ArbString.lean`). A combinator term in that position, which has no law,
  is bounded by its worst case: the most choices any of its runs makes.

**The arithmetic** is the only content. Unfold the cost function one constructor and finish with
`omega`; when the cost function is a named `def`, unfold it `at *` so the hypotheses about
sub-costs unfold too (`AllTwoTree.lean`). If `omega` fails, the bound is too tight: the failing goal
is exactly the linear inequality that doesn't hold, with each sub-cost's bound as a hypothesis.
Adjust the bound in Step 2; nothing else in the proof changes. A bare combinator term, which has no
definition to unfold, is `cost_bound` alone (`BasaltTest/Tactic/Cost.lean`). A generator recursive
by `termination_by` is induction on its decreasing argument and `cost_bound` in each case
(`BasaltTest/Tactic/CostFixpoint.lean`).

### Recipe 4: Expected Values

Not one of the three obligations: a bound on an expectation (the expected size of what is generated,
the expected number of choices) when the worst case of Recipe 3 is too coarse or does not exist.

Worked instances: `Nat.arbitrary.expected_cost` (`ArbNat.lean`), at the cost interpretation, and
`Tree.genBST.expect_size_le` (`BST.lean`), whose arithmetic is a harmonic sum.

```lean
theorem <GEN>.<NAME> : SPMF.expect (<GEN> <ARGS>) (fun v => <QUANTITY> v) ≤ <BOUND> := by
  expect_fixpoint
  <arithmetic>          -- `<computed bound> ≤ <BOUND>`, with `ih` in context
```

**`expect_fixpoint`** (`Basalt/Tactic/Expect.lean`) inducts as `cost_fixpoint` does and runs
`expect_bound` (`Basalt/Tactic/Expect.lean`), the same walk again: it pushes `<QUANTITY>` backward
and computes an upper bound, at `SPMF` or at `SPMF.Cost` (where the quantity sees the choices made,
and `SPMF.Cost.expectedCost` is accepted). A recursive occurrence is bounded by `ih`, used under
whatever the walk arrives with as long as that is `ih`'s own quantity plus a constant
(`(node l x r).size` is `l.size + 1 + r.size`); a callee's bound is passed explicitly,
`expect_fixpoint [h]`. Only an upper bound can be proved this way: the fixpoint induction starts from
the generator that never returns. `BasaltTest/Tactic/Expect.lean` pins the goals.

A **list combinator** has no shape of choice, so it is bounded by a rule rather than averaged. At the
cost interpretation `vectorOf n g` is exact — `n` times `g`'s expected cost, which the walk takes
from a fact you pass. Everywhere else only the mass is used: a constant postexpectation exactly, and
otherwise its worst case over every value (`⨆`), which for an unbounded quantity is `⊤`. When that is
too coarse, prove the bound separately and pass it: `expect_bound [h]`.

## When Stuck

- **`rw [gen]` fails** → wrong unfolding idiom for the context; see the table above.
- **A `mem_support` fact outside a support law won't simplify** (a probability goal,
  `SPMF.prob_eq_zero_iff`) → `support_simp` / `cost_support_simp`; their docstrings
  (`Basalt/Tactic/Support.lean`) say what the sets contain. Inside a support law, use Recipe 1's
  tactics.
- **The completeness witness for a draw** → it is almost always the inverse of the index arithmetic
  (`x - lo` when the recursion ran at `lo + d`). Substitute it *before* unfolding
  (`obtain ⟨d, rfl⟩ : ∃ d, x = lo + d`), so that the equation at the end of the goal is `rfl`.
- **`complete_bound` leaves `∃ a ∈ SPMF.support <callee>, …` for a callee** → no law of the callee
  was found: it is under another name, or not proved. The walk does not fail there, unlike the
  others; the missing law shows up as this residual.
- **`complete_bound` leaves `False`** → every branch that could build the value was refuted, or the
  one conditional on the way is decided the other way by your hypotheses. Check the case split:
  the predicate may admit a value the generator cannot produce.
- **`sound_bound` / `complete_bound` says no hypothesis or law gives `IsSound _ _` /
  `IsCompleteFor _ _` of a combinator argument** → the argument of a list combinator has no law
  (it is a combinator term, or its law is under another name); prove the half and pass it.
- **A walk says it does not enter a `match`** → the `match` is on a drawn value, or is not at the
  head of the generator. Restate the generator with an `if`, or with the cases as separate
  definitions that carry laws.
- **`omega` fails in a cost proof** → read the goal: it is the exact inequality your bound must
  satisfy, with every sub-cost's bound in context. Either the cost function is still folded in a
  hypothesis (`simp only [...] at *`), or the bound is too tight.
- **`cost_bound` says nothing bounds a sub-generator** → it is a callee whose cost law is under
  another name, or the generator argument of a combinator that has no law of its own and no worst
  case (it recurses, or draws from something that does); pass a bound for it: `cost_fixpoint [h]`. A
  recursive combinator of your own gets the same message: it needs a law and a bridge from it
  (`SPMF.Cost.le_always_listOf`, `Basalt/Tactic/Cost.lean`).
- **`mass_bound` says nothing bounds a sub-generator** → it is a recursive combinator of your own
  (bridge its law, as `SPMF.le_expect_listOf` does in `Basalt/Tactic/MassFixpoint.lean`), a callee
  whose termination law is under another name (pass it: `mass_bound [h]`), or a recursive occurrence whose
  fact needs a premise that neither unification nor a hypothesis supplies (`m < n` for a size
  computed from a draw). Pass that fact instantiated; the drawn values are in scope under the
  generator's names (`mass_bound [ih _ (… k₁ …)]`).
- **`mass_bound` leaves `⨅ x, …`** → a continuation's bound depends on a value drawn by a callee or
  a recursive occurrence, of which only the mass is known, so the bound is its worst case over
  every value. A value drawn by a combinator is averaged over instead.
- **A walk leaves `0 < r.den`, `0 ≤ r.num`, `r.num ≤ r.den`** → the weight of a `coin r` is not a
  literal; `SPMF.coin_num_bounds` gives the last two from `0 ≤ r` and `r ≤ 1`.
- **`expect_bound` says a postcondition is not the fact's plus a constant** → the fact about a
  callee or a recursive occurrence bounds `expect x h`, and the walk arrived at it with something
  other than `k + h`. State the fact for the quantity the generator's result is built from, or
  pass one that is.
- **`mass_fixpoint` leaves an arithmetic goal that is false** → the structural half is not in doubt;
  the certificate you named is. Re-count the mean offspring.
- **Finite-domain data (chars, enums)** → the walk leaves a fact about a literal list; `decide` /
  `native_decide` on it directly (see `ArbChar.lean`).

## Prior Art

For the *theory* behind the termination recipe — the least-fixed-point criterion and its
certificates — see `Basalt/SPMF/Termination.lean` (the tactic is `Basalt/Tactic/MassFixpoint.lean`);
for the ranking-function certificate and why critical generators have infinite expected size,
`Basalt/SPMF/Ranking.lean`.
