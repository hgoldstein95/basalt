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

- each `pick` is 1 choice;
- each `chooseNat` / `choose` / `elements` is 1 choice;
- each `oneOf` / `frequency` is 1 choice *plus* the cost of the selected branch;
- a call to another generator costs whatever that generator's bound says.

For a list generator that flips a coin per element, the bound is `fun xs => xs.length + 1` (one
`pick` per cons, one for the nil). When a generated *value* feeds a later recursion (e.g.
`Nat.arbitrary` producing an `n` by counting coin flips), the value itself shows up in the bound
(`fun n => n + 1`).

Keep the bound *tight*: a precise bound is what catches accidental backtracking or other
inefficiency, and (see the cost recipe) a too-tight bound now fails as a legible `omega` goal that
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
  `⟨⟨n, ⟨hge, hle⟩⟩⟩` destructuring in every proof. `chooseNat` returns a bare `Nat`, and its
  inversion lemmas produce plain inequalities that `omega` consumes directly.
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

Each has a fixed recipe. All three start the same way — unfold one step of the recursion, invert
what one step can produce, then do logic/arithmetic — and they differ only in which interpretation
they invert at.

**A generator that post-processes another** (`let x ← g; return f x`) has no recursion to unfold,
and all three obligations reduce to composition instead: `support_simp` plus a fact about `f`,
`SPMF.IsPMF_bind_pure`, and `IsBounded_bind`. `List.genSortedBySorting`
(`SortedList/BySorting.lean`) is the worked instance — it sorts a `List.arbitrary` draw, and each
law follows from the corresponding law of `List.arbitrary` plus one fact about `f`: that sorting
sorts, that it fixes a sorted list, that it is a permutation. Cost is the obligation that can fail
outright for this shape (Step 2).

**Name the laws `<GEN>.sound_complete`, `<GEN>.terminates`, `<GEN>.cost_bounded`.** The dot is not
cosmetic: `#genstats` discovers laws by exactly this naming convention and reports which ones a
generator carries beside the statistics it merely *measured* (`Basalt/GenStats/Command.lean`,
`lawSlots`). A law under any other name is invisible to the report — the generator will show
`— (not proved)` for something you proved. The statement is checked too, not just the name, so a
conventionally-named theorem that says something else cannot be laundered into a ✓. Automated
synthesis that emits the same convention reports identically to hand-written generators.
(`IsFilterFree`/`IsProductive`, for filtering generators, are `.filter_free` and `.productive`.)

### Unfolding: one idiom per context

`partial_fixpoint` definitions unfold four ways, and picking the wrong one gives confusing errors:

| Context | Idiom |
|---|---|
| Support proof, goal `x ∈ support gen ↔ P` | `rw [gen]` (the equation lemma) |
| Termination step (rewrite only one side of `≤`/`≥`) | `conv_rhs => rw [gen]` (or `conv_lhs`) |
| Cost proof, before `fix_induct` (must expose `fix`) | `delta gen` |
| Under binders where `rw` fails | `unfold gen` |

### Recipe 1: Support

Worked instances: `Tree.genHeap.sound_complete` (`Heap.lean`) is the recipe verbatim;
`genAllTwos.sound_complete` (`AllTwoList.lean`) is the short form where `simp` finishes outright.

```lean
theorem <GEN>.sound_complete : IsSoundAndComplete (<GEN> <IDX>) (<PRED> <IDX>) := by
  intro x
  -- 1. Induct on the generated value, generalizing any index the recursion changes.
  induction x generalizing <IDX> with
  | <base case> =>
    rw [<GEN>]                        -- 2. unfold one step
    simp [<PRED>]                     --    base cases usually close by simp
  | <recursive case> ... ih... =>
    rw [<GEN>]                        -- 2. unfold one step
    -- 3. Invert "what can one step produce": the standard support set, plus the validity
    --    predicate, constructor `injEq` lemmas, and callee support lemmas.
    support_simp [<PRED>, <CTOR>.injEq, <callee>_mem_support]
    -- 4. Two directions.
    constructor
    · rintro ⟨...witnesses...⟩        -- forward: destruct, apply the IHs
      exact ⟨by omega, ih₁.mp ‹_›, ih₂.mp ‹_›⟩
    · rintro ⟨...facts...⟩            -- backward: supply witnesses
      -- The only creative step in the whole proof: inverting the index arithmetic —
      -- if the recursion ran at `lo + d` and you know `lo ≤ x`, the witness is `x - lo`.
      refine ⟨x - lo, ..., rfl, by omega, rfl⟩
      · rw [show lo + (x - lo) = x by omega]; exact ih₁.mpr ‹_›
```

Notes:

- `support_simp [extra, lemmas]` is `simp only` with the `mem_support_*_iff` set (`pick`, `bind`,
  `pure`, `map`, `chooseNat`, `ite`/`dite`, `elements`, `oneOf`, `frequency`, …). It fires on real
  generator goals — the set is stated on monad notation. It also takes `at h`.
- **A callee's `.sound_complete` law is not a `simp` lemma.** `IsSoundAndComplete` is a semireducible
  `def`, so `simp` cannot see the `↔` inside it. A generator whose support fact is consumed by
  *other* proofs therefore states both: `<callee>_mem_support` (the raw `↔`, what you pass to
  `support_simp`) and `<callee>.sound_complete` (the law, a one-line corollary). See `Nat.arbitrary`
  (`ArbNat.lean`) and `Char.arbitrary` (`ArbChar.lean`).
- An *alternative* opener when the predicate (not the value) drives the case split:
  `fun_induction <PRED> <;> rw [<GEN>] <;> split <;> simp <;> grind` — see `Tree.genBST.sound_complete`
  (`BST.lean`). Elegant when it works; when it doesn't, fall back to the explicit recipe, which
  fails at a specific step with a specific goal.
- `grind` is the documented *fallback for the endgame* (after `support_simp`), never the whole
  proof. `List.genSortedGt.sound_complete` (`SortedList.lean`) shows endgame grinds that must find
  witnesses.

### Recipe 2: Termination

First read the **regime** off the generator — what does one unfolding do to the seed (the
generator's arguments)?

| Regime | How to recognize it | Target lemma |
|---|---|---|
| Static seed, mean offspring `m < 1` | Arguments inert; expected number of recursive calls per step `< 1` | `SPMF.IsPMF_of_subcritical_mass` |
| … and the recursion *re-indexes* the seed | e.g. recursing at `m + delta` | `SPMF.IsPMF_of_subcritical_mass_family` |
| Static seed, `m = 1` exactly | e.g. uniform `pick` with two recursive calls | `SPMF.IsPMF_of_critical`(`_family`) |
| Shrinking seed | Recursive calls partition/shrink the seed | `SPMF.IsPMF_of_ranking` |

`m` is weights-on-recursive-branches over total weights, counting each branch once per recursive
call: a uniform `pick` with one recursive branch has `m = 1/2`; `frequency [(2, leaf…), (1, node…)]`
with two calls in `node` has `m = 2·(1/3) = 2/3`. **A critical generator (`m = 1`) terminates but
has infinite expected size** (`AllTwoTree.genTree_expectedSteps_infinite`) — reweight it if you can.

Outside the ranking regime the proof is the same three steps, and only the arithmetic is yours:

```lean
theorem <GEN>.terminates : IsAlmostSurelyTerminating (<GEN> <IDX>) := by
  -- the step argument of every criterion: `c` bounds the generator (family) below, `hrec` says so,
  -- and `<IDX>` is there only in the `_family` forms
  refine SPMF.IsPMF_of_<REGIME> … (fun c hrec <IDX> => ?_)
  conv_rhs => rw [<GEN>]    -- 1. unfold one step, RHS only
  mass_bound                -- 2. compute this step's mass from below
  simp                      -- 3. whatever is left is ℝ≥0∞ arithmetic
```

**Step 1** is the unfolding idiom for `≤` goals (see the table above): only the side being bounded
may be unfolded, or the recursive occurrences unfold with it.

**Step 2, `mass_bound`, is the whole structural argument.** It walks the unfolded generator and
*computes* a lower bound on its mass — one `@[mass_bound]` rule per combinator, so the bound comes
out in the shape of the do-block (`Basalt/SPMF/MassBound.lean` owns the rules and the walk;
`BasaltTest/MassBound.lean` shows a generator that uses every one of them). Nothing about the
generator is yours to supply:

- a **recursive occurrence** is discharged from the local context — that is what `hrec` is for, and
  the recursive occurrences are the only places that need it. It need not be named: anything in
  scope that `apply` closes the goal with will do.
- a **callee** is discharged by its own `<callee>.terminates` law, found by the naming convention
  (Part 2 above) — `Nat.arbitrary` inside a body needs no mention. Any other fact is passed
  explicitly: `mass_bound [h₁, h₂]`.
- an **`if`/`dite`** is no different from any other combinator: the bound is the `min` of the
  branches', which step 3 either simplifies away (`min 1 1`) or splits with `le_min`.
  `Tree.genLeftist` (`LeftistHeap.lean`) ends its recursive branch in an `if` that orders the two
  children and `Tree.genHeap` (`Heap.lean`) does not; their termination proofs are otherwise the
  same text. `Tree.genBST` (`BST.lean`) shortcuts on an exhausted interval, and that `dite` is the
  `le_min` case.

**Step 3** is pure `ℝ≥0∞` arithmetic: your `F`/`m` on the left, the computed bound on the right, and
no generator in sight. Try `simp` (`ArbNat.lean`, `SortedList.lean`), then `simp` with the
identities the goal needs (`simp [sq, ENNReal.div_eq_inv_mul, mul_add]` in `LeftistHeap.lean`), then
`ennreal_to_real` (`Basalt/ENNRealAuto.lean`) and `nlinarith` when the inequality is genuinely
strict (`genWeightedTree.terminates`, `AllTwoTree.lean`). If it looks *false*, your `m` or `F` is
wrong, not your proof.

The one adjustment the step sometimes needs, and it is one line: **a seed the criterion had to
tuple.** A family is an `ι → SPMF α`, so a two-argument generator is indexed by a pair and `hrec`
arrives about `<GEN> j.1 j.2`, which `apply` cannot match against `<GEN> lo (x - 1)`. Re-curry it —
`have hrec : ∀ lo hi, c ≤ (<GEN> lo hi : SPMF _).mass := fun lo hi => hrec (lo, hi)` — before
`mass_bound` (`Tree.genBST.terminates`, `BST.lean`).

**Shrinking seed** (`Tree.genWeightedBST`, `BST/Weighted.lean`) is the one regime with real
content, and the one where the step is not a constant: you supply a ranking function
`φ : Seed → ℝ≥0∞` (with `φ ≥ 1`) whose expected value drops by `ε` at every step, and
`SPMF.IsPMF_of_ranking` returns termination *plus* `E[#steps] ≤ φ/ε`. The proof splits into a
`LevelOp` (three algebra laws), a drift lemma (`A φ + ε ≤ φ` — pure arithmetic about your rank), and
a step lemma (one unfolding, using `ENNReal.one_sub_le_mul_one_sub`, `one_sub_sum_div_le`,
`one_sub_mul_le_add` to push the deficit through the branches). The unfolding inside the step lemma
is still `mass_bound`, but each child is bounded by *its own* mass rather than by a constant, so it
is passed `SPMF.le_mass_self`; a uniform pivot is averaged over with
`SPMF.mass_bind_chooseInt_ge` (`chooseNat`: `mass_bind_chooseNat_ge`; raw `choose`:
`mass_bind_choose_ge`) before `mass_bound` takes over. Follow
`genWeightedBST_drift`/`genWeightedBST_step`/`genWeightedBST.terminates`.
Two things to know:

- Candidate `φ`s, in order: the seed measure; `≡ const` (that's the static-seed case); seed measure
  plus a depth term. Evaluate the drift in the seed's *actual* arithmetic: `bstRank` is the plain
  interval measure and the children's ranks sum to the parent's at every pivot, but that holds
  because the bounds are `Int`. Under `Nat` bounds the `lo = 0` pivot has an unshrunk child and the
  same `φ` fails its drift check — a truncating seed costs you a correction term in the rank.
- A wrong `φ` is a *failed drift check*, never a wrong theorem. Guess freely.

### Recipe 3: Cost

Worked instances: `Nat.arbitrary.cost_bounded` (`ArbNat.lean`) is the minimal case; `Tree.genHeap.cost_bounded`
(`Heap.lean`) has a callee and two recursive calls; `Tree.genBST.cost_bounded` (`BST.lean`) shows `dite`
and `chooseNat`, and `Tree.genWeightedBST.cost_bounded` (`BST/Weighted.lean`) adds `frequency`.

```lean
theorem <GEN>.cost_bounded : IsCostBounded <GEN> <COST> := by
  open Lean.Order in
  delta <GEN>                        -- 1. expose the `fix`
  apply fix_induct (motive := fun (g : SPMF.Cost <α>) => IsBounded g <COST>) _ ?admissible ?step
  -- (indexed generators: motive `fun g => ∀ i, IsBounded (g i) <COST>` and
  --  `admissible_pi_apply _ fun _ => admissible_IsBounded _`)
  case admissible => apply admissible_IsBounded
  case step =>
    intro <GEN>_rec ih
    rw [IsBounded_iff]
    rintro ⟨v, n⟩ hmem
    -- 2. Invert "(value, cost) came from one step" into arithmetic facts.
    cost_support_simp at hmem
    -- 3. Destructure. Name the cost equations (hn, hm, …) and let `omega` consume them —
    --    deeply nested `rfl` patterns fail in ways that are hard to diagnose.
    obtain ⟨m, rfl, h | h⟩ := hmem            -- a `pick`: 1 + m, branch left/right
    · obtain ⟨rfl, rfl⟩ := h                  -- base branch
      simp [<COST>]
    · obtain ⟨x, n1, n2, hx, ⟨...⟩, hm⟩ := h  -- recursive branch
      -- 4. One line per callee / recursive call: bring its bound into scope.
      have hhead : n1 ≤ <callee bound> := IsBounded_iff.mp <callee>.cost_bounded (x, n1) hx
      have htail : n3 ≤ <COST> tl := ih (tl, n3) htl
      -- 5. State the goal in constructor form and finish with omega.
      show 1 + m ≤ <COST> (<CTOR> x tl)
      simp only [<COST>, List.length_cons]    -- unfold the cost function one constructor
      omega
```

If `omega` fails here, your bound is too tight — the failing goal displays exactly the linear
inequality that doesn't hold, with each sub-cost as a named hypothesis. Adjust the bound in Step 2
and re-run; nothing else in the proof changes.

For straight-line (non-recursive) generators skip `fix_induct` entirely and use the compositional
algebra: `IsBounded_pure`, `IsBounded_choose`, `IsBounded_pick`, `IsBounded_bind`,
`IsBounded_elements`, `IsBounded_map`, `IsBounded_mono` — see `Char.arbitrary.cost_bounded`
(`ArbChar.lean`). Don't use the combinator path for recursive generators: under `fix_induct` the
inversion path above is uniform and the combinator side conditions just reintroduce the same work.

## When Stuck

- **`rw [gen]` fails** → wrong unfolding idiom for the context; see the table above.
- **A `mem_support` fact won't simplify** → you are probably looking at a combinator without an
  inversion lemma in the set; `unfold` the combinator, or check the `support_simp` /
  `cost_support_simp` docstrings (`Basalt/Tactics.lean`) for what the sets contain.
- **`support_simp` leaves existential/propositional juggling** → that's the endgame; `grind` is the
  documented fallback there (and only there).
- **The backward direction of a support proof needs a witness** → it is almost always the inverse of
  the index arithmetic (`x - lo` when the recursion ran at `lo + d`), plus
  `rw [show lo + (x - lo) = x by omega]`.
- **`omega` fails in a cost proof** → read the goal: it is the exact inequality your bound must
  satisfy. Either a `have` for some callee's bound is missing, or the bound is too tight.
- **`mass_bound` says nothing bounds the mass of a sub-generator** → it is a combinator with no
  `@[mass_bound]` rule (tag one), a callee whose termination law is under another name (pass it:
  `mass_bound [h]`), or a recursive occurrence whose bound cannot escape the binder it sits under —
  see the two adjustments in Recipe 2.
- **`mass_bound` leaves an arithmetic goal that is false** → the structural half is not in doubt;
  the `m` or `F` you claimed is. Re-count the mean offspring.
- **`fix_induct` fails to apply** → the motive must mention the *bare* fixpoint value; for an
  indexed generator quantify the indices in the motive (see the BST cost proofs).
- **Finite-domain data (chars, enums)** → skip the machinery: `decide` / `native_decide` on the
  support fact directly (see `ArbChar.lean`).

## Prior Art

For the *theory* behind the termination recipes — the ranking-function theorem, the three seed
regimes, and why critical generators have infinite expected size — see `Basalt/SPMF/Ranking.lean`.
