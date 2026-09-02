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
  obligations (support, termination, cost) as a skeleton with named holes, the unfolding-idiom
  table, and a when-stuck table. [BasaltExamples/](BasaltExamples/) holds the worked instances
  each recipe names. Start there for any per-generator work; do not improvise a proof shape.
- **The laws** (`IsSoundAndComplete`, `IsAlmostSurelyTerminating`, `IsCostBounded`,
  `IsFilterFree`, `IsProductive`) and their introduction lemmas — [Basalt/Laws.lean](Basalt/Laws.lean).
- **The `Gen` bundle** — [Basalt/Gen.lean](Basalt/Gen.lean).
- **Support inversion** (`mem_support_*_iff`) — [Basalt/SPMF/Support.lean](Basalt/SPMF/Support.lean);
  the `support_simp` / `cost_support_simp` wrappers — [Basalt/Tactics.lean](Basalt/Tactics.lean).
- **Termination theory** (seed regimes, ranking functions, expected size) —
  [Basalt/SPMF/Ranking.lean](Basalt/SPMF/Ranking.lean); the practical entry is WORKFLOW.md's Recipe 2.
- **Expected values and event probabilities** (`expect`, `prob`, Markov, `admissible_expect_le`) —
  [Basalt/SPMF/Expect.lean](Basalt/SPMF/Expect.lean).
- **Cost** (`SPMF.Cost`, `IsBounded` and its algebra) — [Basalt/SPMF/Cost.lean](Basalt/SPMF/Cost.lean).
- **ENNReal arithmetic** — `ennreal_to_real` in [Basalt/ENNRealAuto.lean](Basalt/ENNRealAuto.lean).
- **`@[tunable]`** — the contract (emitted declarations, weight/depth rules) is
  [Basalt/Tuning/Attr.lean](Basalt/Tuning/Attr.lean)'s module docstring;
  [BasaltTest/Tuning.lean](BasaltTest/Tuning.lean) is the full tour.
- **`#genstats`** — options on the command's declarations in
  [Basalt/GenStats/Command.lean](Basalt/GenStats/Command.lean); the law-discovery contract is on
  `lawProved` there, guarded by [BasaltTest/LawLine.lean](BasaltTest/LawLine.lean).
- **Running a property** — the `TestOutcome`/`forAll` vocabulary, campaigns, and the
  `Backend`/`dispatch` command line are [Basalt/PBT/](Basalt/PBT/), guarded by
  [BasaltTest/PBT.lean](BasaltTest/PBT.lean). Nothing there may name an interpretation: a runner that
  needs one belongs with that interpretation and registers itself as a `Backend`.

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
- **`simp`/`support_simp` refuses a callee's `.sound_complete` law** — the law is a semireducible
  `def`, so `simp` cannot see the `↔` inside it; pass the raw `<callee>_mem_support` fact instead.
  WORKFLOW.md's Recipe 1 notes own this, with the worked examples.
- **`#genstats` reports `— (not proved)` for a law you proved** — the theorem is not under the
  `<gen>.sound_complete` / `.terminates` / … naming convention, or its statement is not the law
  (both halves are checked). WORKFLOW.md Part 2 owns the convention;
  [Basalt/GenStats/Command.lean](Basalt/GenStats/Command.lean)'s `lawProved` implements the check.
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
