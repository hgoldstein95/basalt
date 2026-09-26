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
Basalt generators and proves their laws with Basalt's tactics.

## Commands

Build targets and the directory layout are `README.md`'s. **There is no separate test framework.**
Examples and tests elaborate their proofs and `#guard_msgs` pins during `lake build`, so
`lake build` *is* the test suite and a regression is a build failure.

## Where things live

- **Writing a generator and proving it correct** — `WORKFLOW.md`: a recipe for each of the three
  obligations (support, termination, cost) as a skeleton with named holes, the table of judgments
  (the lemma that restates each on its observation, algebra, direction, who supplies the induction),
  the unfolding-idiom table, and a when-stuck table. [BasaltExamples/](BasaltExamples/) holds the
  worked instances each recipe names. Start there for any per-generator work; do not improvise a
  proof shape.
- **The laws** (`IsSoundAndComplete` and its halves `IsSoundFor` and `IsCompleteFor`,
  `IsAlmostSurelyTerminating`, `IsCostBounded`), each but the bundle restated on its observation
  (`iff_obs`, and `.obs` for a fact), and their introduction lemmas —
  [Basalt/Laws.lean](Basalt/Laws.lean); `IsFaithful`, which relates `IO` to `SPMF` and so has no
  observation — [Basalt/IO/Laws.lean](Basalt/IO/Laws.lean).
- **The `Gen` bundle** — [Basalt/Gen.lean](Basalt/Gen.lean).
- **Compiled choice** (`oneOf!`, `frequency!`) — the `compiled_choice` section of
  [Basalt/Combinators.lean](Basalt/Combinators.lean). Its contract (no list in the compiled code, the
  walk its model gets) is pinned by [BasaltTest/Combinators.lean](BasaltTest/Combinators.lean), and
  `@[tunable]`'s handling of it by [BasaltTest/Tuning.lean](BasaltTest/Tuning.lean).
- **Observations** — the layer every per-combinator lemma is derived from. `Obs`, the one
  `Obs.map_*` lemma per combinator, the specification monads and the presentation of each shape of
  choice: [Basalt/Obs/](Basalt/Obs/). An observation lives with its interpretation — the
  expectation one in [Basalt/SPMF/Expect/Obs.lean](Basalt/SPMF/Expect/Obs.lean), may and always in
  [Basalt/SPMF/Support.lean](Basalt/SPMF/Support.lean), the cost ones in
  [Basalt/SPMF/Cost.lean](Basalt/SPMF/Cost.lean). A new combinator needs its `map_` lemma and
  nothing per judgment; [BasaltTest/Obs.lean](BasaltTest/Obs.lean) is the tour.
- **Support** — a support law is two walks: soundness, a lower bound on `SPMF.alwaysObs` in the
  demonic algebra ([Basalt/Walk/Sound.lean](Basalt/Walk/Sound.lean), pinned by
  [BasaltTest/Walk/Sound.lean](BasaltTest/Walk/Sound.lean)); and completeness, a lower bound on
  `SPMF.mayObs` in the angelic one, under an induction the user chooses (`IsCompleteFor.of_measure`
  or their own; [Basalt/Walk/Complete.lean](Basalt/Walk/Complete.lean), pinned by
  [BasaltTest/Walk/Complete.lean](BasaltTest/Walk/Complete.lean)). The practical entry is
  WORKFLOW.md's Recipe 1. Support inversion outside a law (`mem_support_*_iff`, for a probability
  goal or a support equation) — [Basalt/SPMF/Support.lean](Basalt/SPMF/Support.lean); the
  `support_simp` / `cost_support_simp` wrappers —
  [Basalt/Tactic/Support.lean](Basalt/Tactic/Support.lean).
- **Termination** — the criterion (`IsAlmostSurelyTerminating.of_lfpIsOne`, in
  [Basalt/Laws.lean](Basalt/Laws.lean), on `SPMF.mass_eq_one_of_lfpIsOne`) and its `LfpIsOne`
  certificates: [Basalt/SPMF/Termination.lean](Basalt/SPMF/Termination.lean); what the walk needs
  of a mass bound:
  [Basalt/Walk/Mass.lean](Basalt/Walk/Mass.lean), pinned by
  [BasaltTest/Walk/Mass.lean](BasaltTest/Walk/Mass.lean); the `mass_fixpoint` tactic:
  [Basalt/Tactic/MassFixpoint.lean](Basalt/Tactic/MassFixpoint.lean), contract pinned by
  [BasaltTest/Tactic/MassFixpoint.lean](BasaltTest/Tactic/MassFixpoint.lean). Ranking functions and
  expected size: [Basalt/SPMF/Ranking.lean](Basalt/SPMF/Ranking.lean). The equations of `mass`:
  [Basalt/SPMF/Mass.lean](Basalt/SPMF/Mass.lean). The practical entry is WORKFLOW.md's Recipe 2.
- **The generator walker** — one walk proves every judgment, each stated on an observation as a
  bound `O.spec g post ≤ b` or `b ≤ O.spec g post` that the walk computes from the postcondition. A
  combinator has no rule: its `@[gen_map]` lemma is applied and rewritten (`@[spec_apply]`) into a
  *shape of choice* in the algebra. The `@[gen_rule]` rules are for the host constructs, once for
  every monotone observation ([Basalt/Obs/Ordered.lean](Basalt/Obs/Ordered.lean)), for the shapes,
  per algebra and direction ([Basalt/Walk/Average.lean](Basalt/Walk/Average.lean) for expectations;
  the demonic and angelic ones beside the presentations they are derived from, in
  [Basalt/Obs/Presentation.lean](Basalt/Obs/Presentation.lean); the `sup` ones in
  [Basalt/Walk/Cost.lean](Basalt/Walk/Cost.lean)), and for bridging a recursive combinator's law.
  What closes a leaf of a bound on one observation is tagged `@[obs_leaf]`. The registries are
  [Basalt/Walk/Attr.lean](Basalt/Walk/Attr.lean); the walk and its side-goal solvers are
  [Basalt/Walk/Basic.lean](Basalt/Walk/Basic.lean), and the names it gives what it leaves
  [Basalt/Walk/Names.lean](Basalt/Walk/Names.lean). The one entry tactic, `walk`, is
  [Basalt/Walk/Entry.lean](Basalt/Walk/Entry.lean): it reads the observation and direction off a
  goal stated on an observation, finishes by the algebra (one goal per path, a pruned precondition,
  or one inequality), and `walk fixpoint` first inducts, admissible by the observation's
  `admissible`/`admissible_le` or the relation's `admissible`. What the walk knows of each judgment
  — its leaves, its list-combinator rules, its admissibility — is one file per judgment in
  [Basalt/Walk/](Basalt/Walk/); each bound's is pinned by its namesake in
  [BasaltTest/Walk/](BasaltTest/Walk/). [Basalt/Tactic/](Basalt/Tactic/) holds, besides the
  `support_simp` and `ennreal_to_real` helpers, the tactics that do more than walk: `mass_fixpoint`
  (above) and `faithful_fixpoint`. Two judgments relate a generator at two monads instead of
  bounding it, tagged `@[walk_rel]`: `src.Below` ([Basalt/Walk/Ideal.lean](Basalt/Walk/Ideal.lean))
  and `IOModel.Approx` ([Basalt/Walk/IO.lean](Basalt/Walk/IO.lean)), for which the walk unfolds any
  combinator with no rule; `faithful_fixpoint`
  ([Basalt/Tactic/Faithful.lean](Basalt/Tactic/Faithful.lean), pinned by
  [BasaltTest/Tactic/Faithful.lean](BasaltTest/Tactic/Faithful.lean)) walks both. Their combinator
  rules are instances of [Basalt/GenRel.lean](Basalt/GenRel.lean).
  [BasaltTest/Obs.lean](BasaltTest/Obs.lean) is the tour, and fails the build when one of the
  combinators it names loses its `@[gen_map]` lemma or a list combinator loses a bridge — it checks
  that list, not the registry, so a *new* combinator with no lemma is not caught. Nothing else in a
  termination, cost, or expectation proof mentions combinators.
- **Expected values and event probabilities** (`expect`, `prob`, Markov, `admissible_expect_le`) —
  [Basalt/SPMF/Expect/Basic.lean](Basalt/SPMF/Expect/Basic.lean); each combinator's equation —
  [Basalt/SPMF/Expect/Obs.lean](Basalt/SPMF/Expect/Obs.lean); the list combinators' —
  [Basalt/SPMF/Expect/Combinators.lean](Basalt/SPMF/Expect/Combinators.lean). The practical entry
  for a bound is WORKFLOW.md's Recipe 4.
- **Cost** — the interpretation (`SPMF.Cost` and its support inversion):
  [Basalt/SPMF/Cost.lean](Basalt/SPMF/Cost.lean); what the walk needs of it:
  [Basalt/Walk/Cost.lean](Basalt/Walk/Cost.lean), pinned by
  [BasaltTest/Walk/Cost.lean](BasaltTest/Walk/Cost.lean) and, for `walk fixpoint`,
  [BasaltTest/Walk/CostFixpoint.lean](BasaltTest/Walk/CostFixpoint.lean). The practical entry is
  WORKFLOW.md's Recipe 3.
- **ENNReal arithmetic** — `ennreal_to_real` in
  [Basalt/Tactic/ENNReal.lean](Basalt/Tactic/ENNReal.lean).
- **`@[tunable]`** — the contract (emitted declarations, weight/depth rules) is
  [Basalt/Tuning/Attr.lean](Basalt/Tuning/Attr.lean)'s module docstring;
  [BasaltTest/Tuning.lean](BasaltTest/Tuning.lean) is the full tour.
- **`#genstats`** — options on the command's declarations in
  [Basalt/GenStats/Command.lean](Basalt/GenStats/Command.lean).
- **What an `IO` run means** — `idealized_faithful`
  ([Basalt/IO/Faithful.lean](Basalt/IO/Faithful.lean)) states the chain from `IO` to `SPMF` and owns
  what the library assumes of it. Its links: `IOModel` and `toIO` —
  [Basalt/IO.lean](Basalt/IO.lean); `WordModel σ`, SplitMix's range reduction over any source of
  words — [Basalt/IO/SplitMix.lean](Basalt/IO/SplitMix.lean); that `IO` runs `IOModel`
  (`IOModel.Approx`, `IOModel.IOGenLaws`) — [Basalt/IO/Approx.lean](Basalt/IO/Approx.lean), with
  the compiled C checked against the model by [BasaltTest/IO.lean](BasaltTest/IO.lean); that
  `WordModel σ` on an `IdealSource` has the `SPMF` distribution —
  [Basalt/IO/Ideal.lean](Basalt/IO/Ideal.lean), with a draw's case in
  [Basalt/IO/Choose.lean](Basalt/IO/Choose.lean) and an ideal source in
  [Basalt/IO/Stream.lean](Basalt/IO/Stream.lean). WORKFLOW.md's Recipe 5 is the practical entry.
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
  `@[partial_fixpoint_monotone]` lemma *in scope where the definition is elaborated*: either none
  is tagged, or the tagged one comes later in the same file. The tagged lemmas in
  [Basalt/Combinators.lean](Basalt/Combinators.lean) are the models, and that file's own recursive
  combinators sit after them for this reason. The same applies inside a `@[tunable]` body: the
  attribute rebuilds the fixpoint's monotonicity proof
  ([Basalt/Tuning/Attr.lean](Basalt/Tuning/Attr.lean)).
- **`rw [gen]` (or another unfolding) fails or gives a confusing error in a correctness proof** —
  wrong unfolding idiom for the context; the unfolding-idiom table is in `WORKFLOW.md`
  ("Unfolding: one idiom per context").
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

- **A walk reports that nothing bounds a recursive occurrence you have an induction hypothesis
  for** — the hypothesis is stated as a law (`IsSoundFor …`), and a walk uses a hypothesis only when
  it is stated on an observation, so it skips this one silently. Pass it as `walk [ih.obs]`
  (WORKFLOW.md, When Stuck).

- **A walk ignores the hypothesis you have about a combinator term**
  (`ih : SPMF.Cost.alwaysObs.spec (vectorOf n g) …` is in context, and the goal comes back stated
  through `vectorOf`'s own bridge) — for a generator headed by a combinator the walker tries the
  combinator's rule or `@[gen_map]` lemma before any fact. `generalize` the term to a variable
  first, as `always_vectorOf` does in [Basalt/Walk/Cost.lean](Basalt/Walk/Cost.lean).

- **`rw [support_oneOf]` (or `prob_frequency`, …) finds no occurrence in a goal that shows
  `oneOf! [...]`** — `oneOf!`/`frequency!` elaborate to `oneOfWith`/`frequencyWith`, which only
  display as the source form. Rewrite with `oneOfWith_eq`/`frequencyWith_eq` first, or use `simp`,
  which applies them ([Basalt/Combinators.lean](Basalt/Combinators.lean)).

- **`ring`/`linarith` fail on an `ℝ≥0∞` goal** — they don't exist there; transfer with
  `ennreal_to_real` ([Basalt/Tactic/ENNReal.lean](Basalt/Tactic/ENNReal.lean)) and finish over `ℝ`.

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
- Imports: the narrowest module that supplies what the file names, never an umbrella — `Basalt.lean`
  is the only wholesale import of the library and nothing inside the library may import it. Upstream
  imports (`Lean`, `Batteries`, `Mathlib`, `Plausible`) come first, then Basalt's, each block
  alphabetical. An import whose only use is inside a macro body or a `@[gen_rule]` registry is
  load-bearing at the tactic's *use* sites, so it stays even though the module compiles without it.
- Declaration docstrings explain design tension, not just signature — where rule 4 admits one.
- `BasaltExamples/` files are cookbook entries: a generator plus proofs of the correctness
  properties that apply to it, nothing else — no `#eval`/`#guard_msgs`. Anything pinned or run
  for effect belongs in `BasaltTest/`; nothing built has a `sorry`.
- Lean toolchain is pinned in `lean-toolchain`; deps in `lakefile.toml` / `lake-manifest.json`.
