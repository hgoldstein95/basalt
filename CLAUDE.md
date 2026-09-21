# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## What this is

Basalt is a Lean 4 library: **a foundational representation of random data generators for
property-based testing**, plus machine-checked proofs about them. A generator is a term polymorphic
in its monad (`def myGen [Gen G] : G α`) — the same term runs at `Plausible.Gen`/`IO` and is
reasoned about at `SPMF`. Research code; APIs are unstable.

`README.md` is the user-facing reference and is kept accurate — it owns the build commands, the
repository layout, the interpretation table, and the correctness-law vocabulary. Read it before
changing public behavior, and update it when you do.
[Palamedes](https://github.com/hgoldstein95/palamedes-lean), the flagship client, synthesizes
Basalt generators and emits laws under Basalt's naming convention.

## Commands

Build targets and the directory layout are `README.md`'s. **There is no separate test framework.**
Examples and tests elaborate their proofs and `#guard_msgs` pins during `lake build`, so
`lake build` *is* the test suite and a regression is a build failure.

## Where things live

- **Writing a generator and proving it correct** — `WORKFLOW.md`: a recipe for each of the three
  obligations (support, termination, cost) as a skeleton with named holes, the table of judgments
  (observation, algebra, direction, who supplies the induction), the unfolding-idiom table, and a
  when-stuck table. [BasaltExamples/](BasaltExamples/) holds the worked instances
  each recipe names. Start there for any per-generator work; do not improvise a proof shape.
- **The laws** (`IsSoundAndComplete` and its halves `IsSound` and `IsCompleteFor`,
  `IsAlmostSurelyTerminating`, `IsCostBounded`, `IsFilterFree`, `IsProductive`) and their
  introduction lemmas — [Basalt/Laws.lean](Basalt/Laws.lean).
- **The `Gen` bundle** — [Basalt/Gen.lean](Basalt/Gen.lean).
- **Observations** — the layer every per-combinator lemma is derived from. `Obs`, the one
  `Obs.map_*` lemma per combinator, the specification monads and the presentation of each shape of
  choice: [Basalt/Obs/](Basalt/Obs/). An observation lives with its interpretation — the
  expectation one in [Basalt/SPMF/Expect/Obs.lean](Basalt/SPMF/Expect/Obs.lean), may and always in
  [Basalt/SPMF/Support.lean](Basalt/SPMF/Support.lean), the cost ones and erasure in
  [Basalt/SPMF/Cost.lean](Basalt/SPMF/Cost.lean). A new combinator needs its `map_` lemma and
  nothing per judgment; [BasaltTest/Obs.lean](BasaltTest/Obs.lean) is the tour.
- **Support** — a support law is two walks: soundness, a lower bound on `SPMF.alwaysObs` in the
  demonic algebra (`sound_bound`, [Basalt/SPMF/SoundBound.lean](Basalt/SPMF/SoundBound.lean), and
  `sound_fixpoint`, [Basalt/SPMF/SoundFixpoint.lean](Basalt/SPMF/SoundFixpoint.lean), pinned by
  [BasaltTest/SoundBound.lean](BasaltTest/SoundBound.lean)); and completeness, a lower bound on
  `SPMF.mayObs` in the angelic one, under an induction the user chooses (`complete_bound` and
  `IsCompleteFor.of_measure`, [Basalt/SPMF/CompleteBound.lean](Basalt/SPMF/CompleteBound.lean),
  pinned by [BasaltTest/CompleteBound.lean](BasaltTest/CompleteBound.lean)). The practical entry is
  WORKFLOW.md's Recipe 1. Support inversion outside a law (`mem_support_*_iff`, for a probability
  goal or a support equation) — [Basalt/SPMF/Support.lean](Basalt/SPMF/Support.lean); the
  `support_simp` / `cost_support_simp` wrappers — [Basalt/Tactics.lean](Basalt/Tactics.lean).
- **Termination** — the criterion (`IsPMF_of_lfp_eq_one`) and its `LfpIsOne` certificates:
  [Basalt/SPMF/Termination.lean](Basalt/SPMF/Termination.lean); the `mass_fixpoint` tactic:
  [Basalt/SPMF/MassFixpoint.lean](Basalt/SPMF/MassFixpoint.lean), contract
  pinned by [BasaltTest/Termination.lean](BasaltTest/Termination.lean). Ranking functions and
  expected size: [Basalt/SPMF/Ranking.lean](Basalt/SPMF/Ranking.lean). The equations of `mass`:
  [Basalt/SPMF/Mass.lean](Basalt/SPMF/Mass.lean). The practical entry is WORKFLOW.md's Recipe 2.
- **The generator walker** — one walk proves every judgment, each stated on an observation as a
  bound `O.spec g post ≤ b` or `b ≤ O.spec g post` that the walk computes from the postcondition. A
  combinator has no rule: its `@[gen_map]` lemma is applied and rewritten (`@[spec_apply]`) into a
  *shape of choice* in the algebra. The `@[gen_rule]` rules are for the host constructs, once for
  every monotone observation ([Basalt/Obs/Ordered.lean](Basalt/Obs/Ordered.lean)), for the shapes,
  per algebra and direction ([Basalt/SPMF/AverageBound.lean](Basalt/SPMF/AverageBound.lean) for
  expectations; the demonic and angelic ones beside the presentations they are derived from, in
  [Basalt/Obs/Presentation.lean](Basalt/Obs/Presentation.lean); the `sup` ones in
  [Basalt/SPMF/CostBound.lean](Basalt/SPMF/CostBound.lean)), and for bridging a recursive
  combinator's law. The judgments, the per-observation leaves, and the registries are
  [Basalt/SPMF/Walk/Attr.lean](Basalt/SPMF/Walk/Attr.lean); the walk and its side-goal solvers are
  [Basalt/SPMF/Walk.lean](Basalt/SPMF/Walk.lean). What an entry tactic is made of — `computeBound`,
  `fixpointStep`, and the residual handlers — is
  [Basalt/SPMF/Walk/Entry.lean](Basalt/SPMF/Walk/Entry.lean): a `_bound` tactic restates its goal
  and relates the computed bound to it, and a `_fixpoint` tactic is `fixpointStep` and its `_bound`
  (`mass_fixpoint` excepted, which goes through the `LfpIsOne` criterion). The entry tactics are
  `sound_bound` and `complete_bound` (above), `mass_bound`
  ([Basalt/SPMF/MassBound.lean](Basalt/SPMF/MassBound.lean), pinned by
  [BasaltTest/MassBound.lean](BasaltTest/MassBound.lean)), `cost_bound`
  ([Basalt/SPMF/CostBound.lean](Basalt/SPMF/CostBound.lean), pinned by
  [BasaltTest/CostBound.lean](BasaltTest/CostBound.lean)), and `expect_bound`
  ([Basalt/SPMF/ExpectBound.lean](Basalt/SPMF/ExpectBound.lean), pinned by
  [BasaltTest/ExpectBound.lean](BasaltTest/ExpectBound.lean)), each but `complete_bound` with its
  `_fixpoint`.
  [BasaltTest/Obs.lean](BasaltTest/Obs.lean) is the tour, and fails the build when one of the
  combinators it names loses its `@[gen_map]` lemma or a list combinator loses a bridge — it checks
  that list, not the registry, so a *new* combinator with no lemma is not caught. Nothing else in a
  termination, cost, or expectation proof mentions combinators.
- **Expected values and event probabilities** (`expect`, `prob`, Markov, `admissible_expect_le`) —
  [Basalt/SPMF/Expect/Basic.lean](Basalt/SPMF/Expect/Basic.lean); each combinator's equation —
  [Basalt/SPMF/Expect/Obs.lean](Basalt/SPMF/Expect/Obs.lean); the list combinators' —
  [Basalt/SPMF/Expect.lean](Basalt/SPMF/Expect.lean). The practical entry for a bound is
  WORKFLOW.md's Recipe 4.
- **Cost** — the interpretation (`SPMF.Cost`, `IsBounded`, its support inversion, expected cost):
  [Basalt/SPMF/Cost.lean](Basalt/SPMF/Cost.lean); the `cost_fixpoint` tactic:
  [Basalt/SPMF/CostFixpoint.lean](Basalt/SPMF/CostFixpoint.lean), contract pinned by
  [BasaltTest/CostFixpoint.lean](BasaltTest/CostFixpoint.lean). The practical entry is
  WORKFLOW.md's Recipe 3.
- **ENNReal arithmetic** — `ennreal_to_real` in [Basalt/ENNRealAuto.lean](Basalt/ENNRealAuto.lean).
- **`@[tunable]`** — the contract (emitted declarations, weight/depth rules) is
  [Basalt/Tuning/Attr.lean](Basalt/Tuning/Attr.lean)'s module docstring;
  [BasaltTest/Tuning.lean](BasaltTest/Tuning.lean) is the full tour.
- **`#genstats`** — options on the command's declarations in
  [Basalt/GenStats/Command.lean](Basalt/GenStats/Command.lean); the law-discovery contract is on
  `lawProved` there, guarded by [BasaltTest/LawLine.lean](BasaltTest/LawLine.lean).
- **Stating and running a property** — [Basalt/PBT/](Basalt/PBT/), guarded by
  [BasaltTest/PBT.lean](BasaltTest/PBT.lean), which is the tour. Nothing there may name an
  interpretation: a runner that needs one belongs with that interpretation and tags itself
  `@[basalt_backend]`.
- **Coverage-guided fuzzing** (`FuzzGen`, the libFuzzer bridge, the opt-in `basalt-fuzz` executable)
  — [fuzz-run/README.md](fuzz-run/README.md) owns the design, the per-platform build contract, and
  the measured comparison between backends. This is the repo's only FFI and native-link config. The
  code under test lives in the `BasaltFuzz` library, which is the only instrumented one — a generator
  or property that wants coverage feedback belongs there and nowhere else. The default build
  type-checks it but emits no C, so a change to the *native* half (bridge, runtime detection, link) is
  caught only by `fuzz-run/build.sh` and the `basalt-fuzz` CI workflow; a drift from the proved
  `genBST` is caught by `BasaltTest/Fuzz.lean`. Anything added to the Mathlib-free link closure must
  stay Mathlib-free: import the narrowest module, not an umbrella.

## Gotchas (symptom → cause → pointer)

- **A `partial_fixpoint` definition fails to elaborate**, complaining about monotonicity rather
  than about any combinator — a combinator in the recursive body has no
  `@[partial_fixpoint_monotone]` lemma. The tagged lemmas in
  [Basalt/Combinators.lean](Basalt/Combinators.lean) (and
  [RandomChoice.lean](Basalt/RandomChoice.lean)) are the models. The same applies inside a
  `@[tunable]` body: the attribute rebuilds the fixpoint's monotonicity proof
  ([Basalt/Tuning/Attr.lean](Basalt/Tuning/Attr.lean)).
- **`rw [gen]` (or another unfolding) fails or gives a confusing error in a correctness proof** —
  wrong unfolding idiom for the context; the four-idiom table is in `WORKFLOW.md`
  ("Unfolding: one idiom per context").
- **`#genstats` reports `— (not proved)` for a law you proved** — the theorem is not under the
  `<gen>.sound_complete` / `.terminates` / … naming convention, or its statement is not the law
  (both halves are checked). WORKFLOW.md Part 2 owns the convention;
  [Basalt/GenStats/Command.lean](Basalt/GenStats/Command.lean)'s `lawProved` implements the check.
- **Drawing from a generator inside a property fails with `failed to synthesize instance Gen
  (PropM G)`** — `PropM G` is deliberately not a `Gen`, so a bare `←` on a generator elaborates it at
  the ambient `PropM G` instead of lifting it. Wrap the draw in `generate`
  ([Basalt/PBT/Property.lean](Basalt/PBT/Property.lean)), or use `forAll`. The error names the
  missing instance, not the missing combinator, so it reads as a gap in `Basalt/Gen.lean`.
- **A `do` block that binds a property with `←` reports a nonsense error somewhere else** (e.g.
  "unknown constant `Unit.ok`" at a later `match`) — `PropM G Unit` is *definitionally*
  `G TestOutcome`, so `←` on a property inside a `PropM G` block unifies before the automatic lift
  is tried and silently yields the property's `Unit` instead of its outcome. Go through
  `runProp` ([Basalt/PBT/Property.lean](Basalt/PBT/Property.lean)) to observe an outcome. The same
  defeq means a runner's `IO TestOutcome` argument does not determine `G`: ascribe the
  interpretation (`(prop : PropM IO Unit)`) at the call site.

- **A walk ignores the hypothesis you have about a combinator term** (`ih : IsBounded (vectorOf n g) …`
  is in context, and the goal comes back stated through `vectorOf`'s own bridge) — for a generator
  headed by a combinator the walker tries the combinator's rule or `@[gen_map]` lemma before any
  fact. `generalize` the term to a variable first, as `isBounded_vectorOf` does in
  [Basalt/SPMF/CostBound.lean](Basalt/SPMF/CostBound.lean).

- **`ring`/`linarith` fail on an `ℝ≥0∞` goal** — they don't exist there; transfer with
  `ennreal_to_real` ([Basalt/ENNRealAuto.lean](Basalt/ENNRealAuto.lean)) and finish over `ℝ`.

## Documentation rules

1. One owner per fact. Every fact lives in exactly one place; other mentions are a pointer. The
   owner is the file whose edit would falsify the fact — a number, name, or list set in code is
   documented where it is set, never quoted elsewhere.
2. CLAUDE.md is a map, not a mirror: workflow, architecture no single file owns, routing to worked
   examples, and these rules. No fact a code edit can falsify.
3. The default is no comment. The compiler, a test, or a pin is the fence wherever it can be — a
   mistake that fails loudly and locally needs no warning, however tempting the edit.
4. A warning comment must be backed by a failure that actually happened (or a symptom that cannot
   be traced locally) AND that was silent, delayed, or misattributed. Hypothetical mistakes get no
   fence.
5. A fence is two sentences: the forbidden edit, the observed symptom. Only a misattributed
   failure also earns an entry in CLAUDE.md's gotcha section (symptom → cause → pointer), because
   its victim is looking at the wrong file.
6. No process narration ("the probe", "previously we") — git history holds the story; comments
   hold the contract.
7. When a hazard can be made a build failure, build the check and delete the prose. A fence
   comment is the fallback, not the goal.
8. Module docstrings are 1–3 sentences: what the module is, the invariant it protects. Hazard
   prose lives on the declaration that carries the hazard.
9. An edit that fans out into many mechanical fixes is a design signal: stop and reconsider the
   approach; do not qualify or patch through the errors.
10. Background theory is cited, not taught. A fact about Lean, Mathlib, or type theory is owned
    upstream: state its local consequence (the lemma that cannot exist, the tactic that cannot be
    used here) and name the concept so a reader can find the real treatment ("a free theorem";
    "tactic-mode `cases` elaborates to the recursor"). Explain a mechanism only when it has no
    citable name — version-specific or undocumented behavior — and then as a rule-4 fence.

## Conventions

- Every module opens with the MIT copyright header and a `/-! # … -/` module docstring, sized and
  scoped per the documentation rules above.
- Declaration docstrings explain design tension, not just signature — where rule 4 admits one.
- `BasaltExamples/` files are cookbook entries: a generator plus proofs of the correctness
  properties that apply to it, nothing else — no `#eval`/`#guard_msgs`. Anything pinned or run
  for effect belongs in `BasaltTest/`; anything with a `sorry` belongs in `BasaltExperiments/`.
- Lean toolchain is pinned in `lean-toolchain`; deps in `lakefile.toml` / `lake-manifest.json`.
