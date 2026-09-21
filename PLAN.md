# PLAN: one lemma per combinator

A working plan for restructuring Basalt's proof infrastructure. It is written for an agent who has
not seen the design discussion. Delete this file when the work is finished; nothing else in the
repository should point at it.

Read `CLAUDE.md`, `README.md`, and `WORKFLOW.md` first. `CLAUDE.md`'s documentation rules and
conventions bind everything below (MIT header and short module docstring on every module, default is
no comment, `lake build` is the test suite, cookbook entries go in `BasaltExamples/`, anything pinned
goes in `BasaltTest/`).

## 1. The problem

Basalt proves several kinds of facts about a generator, each through its own machinery:

| Question | Statement | Machinery today |
|---|---|---|
| Which values can come out? | `a ∈ SPMF.support g ↔ P a` | `mem_support_*_iff` simp lemmas (`Basalt/SPMF/Support.lean`), `support_simp` |
| Does it terminate almost surely? | `SPMF.mass g = 1` | `le_mass_*` rules (`MassBound.lean`), `mass_bound`, `mass_fixpoint`, `LfpIsOne` certificates |
| Worst-case number of choices? | `IsBounded g c` / `SPMF.Cost.Always g Q` | `always_*` and `isBounded_*` rules (`CostBound.lean`), `cost_bound`, `cost_fixpoint` |
| Expected values, probabilities? | `SPMF.expect g f`, `SPMF.prob g E` | `expect_*` equations (`Expect.lean`, `Cost.lean`), applied by hand |

The generator walker (`Basalt/SPMF/Walk.lean`) drives the second and third with `@[gen_rule]` lemmas
keyed by (judgment, combinator). The consequence is that every combinator needs a separately stated
and separately proved fact for every kind of question, in each interpretation (`SPMF` and
`SPMF.Cost`). `pick` has eleven such facts. `oneOf`'s index selection is derived independently in
`support_oneOf`, `oneOf_apply`, and `always_oneOf`, and there is no `expect_oneOf` at all. This
combinators × judgments grid is the main maintenance cost, and adding a judgment (expected cost by
tactic, say) would add a column to it.

Three further symptoms come from the same root:

- **The mass walker is imprecise.** It computes bounds bottom-up, so a continuation's bound cannot
  be pushed into the draw that precedes it. That is why there are three bind rules
  (`le_mass_bind`, `le_mass_bind_chooseNat`/`Int`, `le_mass_bind_iInf`) and two conditional rules
  (`le_mass_ite`, `le_mass_ite_min`) tried as fallbacks. The fallbacks lose information. Appendix D
  is a repro: the same geometric loop written with `pick` yields the bound `1/2 * 1 + 1/2 * (c * 1)`,
  and written with `coin` yields `1 * min 1 (c * 1)`, for which no `LfpIsOne` certificate exists.
  WORKFLOW's claim that a false arithmetic goal means a wrong certificate is not true for such
  generators.
- **Expectation proofs are done by hand.** `Tree.genBST.expect_size_le` (`BasaltExamples/BST.lean`)
  and `Nat.arbitrary.expected_cost` (`BasaltExamples/ArbNat.lean`) are manual walks through the
  generator with `expect_bind`, `expect_add`, `expect_const`, `mass_le_one`.
- **Nothing relates the two interpretations.** There is no theorem that
  `Prod.fst <$> (g : SPMF.Cost α) = (g : SPMF α)`, so a fact proved at `SPMF` (expected size) cannot
  be combined with one proved at `SPMF.Cost` (`expectedCost_le_of_IsBounded`).

## 2. The idea

All of these questions are instances of one construction. Make that construction a Lean value, and
state each combinator's fact once against it.

**A judgment is a structure-preserving map out of the generator monad.** Call it an *observation*:

```lean
structure Obs (G W : Type → Type) [Monad G] [RandomChoice G] [Monad W] [RandomChoice W] where
  θ : ∀ {α}, G α → W α
  map_pure   : θ (Pure.pure a) = Pure.pure a
  map_bind   : θ (x >>= k) = θ x >>= fun a => θ (k a)
  map_choose : θ (choose lo hi h) = choose lo hi h
```

`G` is `SPMF` or `SPMF.Cost`. `W` is a *specification monad*: a continuation monad over some algebra
`Ω`, in two families that are both generic in `Ω`:

- `WP Ω α := (α → Ω) → Ω`, a transformer from a postcondition on values to an `Ω`.
- `WPC Ω α := (α → Nat → Ω) → Ω`, the same with a choice counter. Its `bind` adds counts and its
  `choose` charges 1.

`Ω` carries one operation, `Mix.mix`, saying what a uniform choice over `[lo, hi]` means in `Ω`.
The instances are the judgments:

| Observation | `G` | `W` | `θ g post` | `mix` is |
|---|---|---|---|---|
| expectation | `SPMF` | `WP ℝ≥0∞` | `SPMF.expect g post` | the average |
| always | `SPMF` | `WP Prop` | `∀ a ∈ support g, post a` | `∀` |
| may | `SPMF` | `WP Prop` | `∃ a ∈ support g, post a` | `∃` |
| cost versions of the three | `SPMF.Cost` | `WPC Ω` | the same, with `post a n` seeing the count | the same |
| erasure | `SPMF.Cost` | `SPMF` | `Prod.fst <$> g` | (target is `SPMF` itself) |

Every existing law is one of these at a particular postcondition: mass is expectation of `1`,
`prob g E` is expectation of an indicator, `IsBounded g c` is cost-always of `fun a n => n ≤ c a`,
support membership is may of `(· = a)`, soundness is always of `P`.

**Each combinator then needs one lemma: `θ` commutes with it.** For any observation, in either
interpretation:

```lean
theorem Obs.map_pick (O : Obs G W) (x y : Unit → G α) :
    O.θ (pick x y) = pick (fun u => O.θ (x u)) (fun u => O.θ (y u)) := by
  simp only [pick, O.map_bind, O.map_choose, O.map_ite]
```

The proof script is uniform: unfold the combinator, rewrite with the three laws.

**The real mathematical content moves to the algebra.** What remains to prove by hand is, per `Ω`,
how `mix` presents for each *shape* of choice: binary (`pick`), threshold (`coin`), plain range
(`chooseNat`), list index (`oneOf`, `elements`), weighted select (`frequency`). These are facts about
averages and quantifiers over lists, not about combinators, and new combinators reuse them.

The accounting changes from (combinators × judgments × interpretations) hand proofs to
(combinators) uniform one-liners + (judgments) × (three laws + about five presentation lemmas).

In PL terms, "every generator commutes with every observation" is the free theorem of the
tagless-final encoding `[Gen G] : G α`. Lean has no internal parametricity, so the `map_X` lemmas are
its cases, stated once, and the generator walker proves it one generator at a time.

## 3. What has been checked

The appendices are prototype files checked against the built library (`lake env lean <file>` from
the repo root, toolchain `leanprover/lean4:v4.33.0-rc2`). Appendices A and B elaborate with zero
errors; Appendix C elaborates except for one closing arithmetic goal, noted there; Appendix D is a
repro that ends in `sorry` by design. They are the starting point for the real modules. They were scratch files, so their style (names, docstrings,
proof polish) is not final.

- Appendix A: `Obs`, `WP`, `Mix`, the expectation and always observations on `SPMF`, the generic
  `Obs.map_map` and `Obs.map_oneOf`, the list-index presentation lemmas for `ℝ≥0∞` and `Prop`, and
  three corollaries whose proofs never mention `oneOf`'s definition: `expect_oneOf` (new to the
  library), `mass_oneOf`, and `always_oneOf`.
- Appendix B: `WPC`, the cost-always observation on `SPMF.Cost`, generic `map_ite`/`map_pick`/
  `map_coin`, and the derivation of both `pick` rules (plain and cost) from the one `map_pick`. The
  `fun a n => Q a (1 + n)` shift in the cost rule is produced by `WPC`'s `choose`; nobody states it.
- Appendix C: (a) support lemmas derived from expectation equations through
  `expect_pos_iff : 0 < expect p f ↔ ∃ a ∈ p.support, 0 < f a`; (b) backward-mode lower-bound
  rules (`b ≤ expect g f` with `f` an input and `b` an output) and the `coin` loop of Appendix D
  walked with them, giving `1/2 + 1/2 * c` up to normalization.
- Appendix D: the repro of the mass walker's imprecision.

Not yet checked, in decreasing order of risk:

1. **Residual goal quality in the walker** (Stage 2). Goals will arrive in terms of `Mix.mix` and
   need a presentation pass. Today's per-path goals and their binder names (`x`, `n_x`, `h_x`; see
   "Names" in `Walk.lean`) are tuned per rule and must be reproduced generically.
2. **`frequency`.** Its unreachable `else default` branch needs a law `θ default = default`, and its
   weighted-select presentation lemma is today's `sum_frequencySelect_apply` argument
   (`Support.lean`).
3. **`SPMF.Cost` has no `LawfulMonad` instance**, which the generic `Obs.map_map` uses. Either
   provide the instance or make `map_map` a fourth law of `Obs`.
4. **The may observation and the erasure observation.** Expected to be routine.
5. **Universe polymorphism.** The prototypes fix `Type → Type`; `RandomChoice` is polymorphic.

## 4. Decisions already made

- **Keep apply-style walker rules.** Using the equations as a rewriting set would collapse more
  lemmas but gives up the walker's binder naming, located errors, and control of normal forms.
- **Keep `SPMF.Cost.Always` and its `Prop`-valued goals** as the user-facing form of cost and
  soundness facts. The observation justifies the rules; it does not turn `omega` goals into
  `ℝ≥0∞` arithmetic.
- **Recursive combinators (`listOf`, `nonEmptyListOf`) are generators with laws, not `map_X`
  cases.** A `map_listOf` would need the specification monad to be a CCPO and a fixpoint-fusion
  lemma. Do not attempt it in Stage 1. Their facts stay as laws proved by fixpoint reasoning, and
  their walker rules stay as bridges from those laws, as `always_listOf` is today.
- **State the `W` side of a `map_X` lemma with `Monad` and `RandomChoice` operations only**, as
  `map_oneOf` does, so that `W` never has to be a `Gen`.
- **Expected cost is the expectation observation into `WPC ℝ≥0∞`.** An earlier idea, a transformer
  `ect g f := expect g (fun p => p.2 + f p.1)`, has a bind rule that is only an inequality
  (`SPMF (α × Nat)` forgets the cost of diverging runs), so it is not an observation.
- **Do not build on `Std.Do`/`mvcgen`.** It has the same architecture, but its `PredTrans` is
  `Prop`-valued and required to be conjunctive, which rules out expectation and may.
- **No change to** the law definitions in `Basalt/Laws.lean`, the law naming convention, `#genstats`,
  `support_simp`'s surface, or the `LfpIsOne` certificates.

## 5. Stage 1: a library layer under the existing lemmas

Goal: every per-combinator fact in the library is a corollary of one `map_X` lemma plus presentation
lemmas. **No statement that a user or a tactic depends on changes**, so the walkers, `support_simp`,
`BasaltExamples/`, and `BasaltTest/` keep building untouched. This stage is pure proof refactoring
plus new lemmas, and it is worth keeping even if Stage 2 is abandoned.

Suggested modules (adjust names to taste; keep imports narrow, and do not import any of these from
`Basalt/Gen.lean`, `Basalt/Combinators.lean`, or anything in the Mathlib-free fuzz link closure
described in `fuzz-run/README.md`):

- `Basalt/Obs/Basic.lean`: `Obs`; the generic lemmas for host constructs (`map_ite`, `map_dite`,
  `map_map`, commuting with a `match` on a drawn value).
- `Basalt/Obs/Spec.lean`: `Mix`, `WP`, `WPC`, their `Monad`/`LawfulMonad`/`RandomChoice` instances.
- `Basalt/Obs/Combinators.lean`: one `map_X` per combinator of `Basalt/Combinators.lean` and
  `Basalt/RandomChoice.lean`.
- `Basalt/SPMF/Obs.lean` (or split by observation): the instances and the presentation lemmas.

Steps, in order. Run `lake build` after each; a regression is a build failure.

1. **Land `Obs`, `WP`, `Mix`, and the expectation and always observations on `SPMF`** from
   Appendix A. The expectation observation's laws are `expect_pure`, `expect_bind`, and `rfl`
   (because the `ℝ≥0∞` `mix` is defined to be what `choose` does). This requires `Expect.lean`'s
   core (`expect`, `expect_pure`, `expect_bind`, `expect_mono`, …) to sit *before* `Support.lean`
   and `Mass.lean` in the import order; today it is after them. Split `Expect.lean` if needed.
2. **Land `WPC` and the cost observations** (Appendix B has cost-always). Resolve the
   `LawfulMonad SPMF.Cost` question here.
3. **Add the may observation** (`mix` is `∃`) on both interpretations, and the two transfer lemmas
   that connect the `Prop` observations to expectation: `expect_pos_iff` (Appendix C) and the
   existing `prob_eq_zero_iff`.
4. **Write `map_X` for the non-recursive combinators**: `pick`, `coin`, `chooseNat`, `chooseInt`,
   `elements`, `oneOf`, `frequency` (via a lemma for `Helpers.frequencySelect` by induction on the
   list, and the `θ default = default` law), `vectorOf` (through `vectorOf_succ`),
   `listOfMaxLength`, `biasedOptionGen`, `optionGen`. If the proof script really is uniform, note
   it; a deriving attribute is a possible later convenience, not part of this stage.
5. **Write the presentation lemmas**, one per (`Ω`, choice shape). The `ℝ≥0∞` list-index lemma is
   in Appendix A. The others re-home arguments that exist today: binary from `expect_pick`,
   threshold from `sum_ite_lt_num`/`expect_coin`, weighted select from
   `sum_frequencySelect_apply`, plain range from `expect_choose`/`tsum_subtype_Icc`.
6. **Re-prove the existing per-combinator facts as corollaries, keeping names and statements.**
   Work through `Support.lean` (`support_*`, `mem_support_*_iff`, `oneOf_apply`,
   `frequency_apply`), `Mass.lean` (`mass_*`), `Expect.lean` (`expect_pick`, `expect_frequency`,
   `expect_bind_chooseNat`/`Int`, `expect_coin`, `prob_*`), `Cost.lean`
   (`SPMF.Cost.mem_support_*_iff`, `SPMF.Cost.expect_*`), and the `always_*` rule proofs in
   `CostBound.lean`. Delete the hand derivations they replace. A useful check when done: `tsum`
   should appear only in `Core.lean`, the core of `Expect.lean`, the observation instances, and
   the presentation lemmas.
7. **Add the facts that now come for free and are missing today**: `expect_oneOf`,
   `expect_elements`, the `SPMF.Cost` expectation equations for every combinator, and the erasure
   observation `Obs SPMF.Cost SPMF` with `θ := (Prod.fst <$> ·)`, which yields an erasure equation
   per combinator from the same `map_X` lemmas.
8. **One continuity theorem.** Prove `expect (CCPO.csup hc) f = ⨆ p, ⨆ (_ : c p), expect p f` (the
   hard half is the `calc` inside `admissible_expect_le`) and derive `admissible_expect_le`,
   `admissible_Always`, and `mem_support_csup` from it.
9. **Pin the contract** in a new `BasaltTest/Obs.lean`: define a toy combinator in the test file,
   prove its one `map_` lemma, and obtain its support, always, cost-always, and expectation facts
   from it. This is the executable statement of "one lemma per combinator".
10. **Docs.** Add the new modules to `README.md`'s layout and one routing bullet to `CLAUDE.md`'s
    "Where things live". `WORKFLOW.md` does not change in Stage 1.

Stage 1 is done when `lake build` passes, steps 6 and 9 are complete, and no public statement
changed. Stop and report, rather than patching through, if `frequency` or the cost interpretation
needs a change to `Obs`'s shape beyond one added law: that is the design signal `CLAUDE.md`'s
documentation rule 9 describes.

Pitfalls met while prototyping:

- With `open SPMF`, a bare `pure` resolves to `SPMF.pure`. Write `Pure.pure` in generic statements.
- Take `[Gen G]` alone for the source monad when a lemma mentions a `Gen` combinator; adding
  `[Monad G]` beside it creates two unrelated `Monad` instances.
- `simp` will unfold `Pure.pure` on `SPMF` to `SPMF.pure` and then miss the support lemmas. In the
  observation instances, prefer `funext Q; apply propext` and explicit terms.
- `rw [tsum_subtype_Icc …]` can fail on a universe mismatch in `ULift`; use
  `refine (tsum_subtype_Icc …).trans ?_`.
- `choose` returns `ULift {x // lo ≤ x ∧ x ≤ hi}`. Define `Mix.mix` over that same type
  (Appendix A), not over the bare subtype (Appendix B), so `map_choose` stays `rfl`-cheap.

## 6. Stage 2: the walker

Start only after Stage 1. The aim is a `@[gen_rule]` registry keyed by combinator alone, with a
`Judgment` (`Basalt/SPMF/Walk/Attr.lean`) being an observation, a direction (`≤` or `≥` on `Ω`), a
goal recognizer, and its bridges.

1. **An ordered layer.** For an `Ω` with a preorder and a monotone `mix`, state each combinator's
   apply-rule once, generically: from bounds on `θ` of the sub-generators conclude the bound on
   `θ` of the combinator, in backward mode (the postcondition is an input, the bound an output).
   Appendix C has the concrete `ℝ≥0∞` versions of `pure`, `bind`, `ite`, `coin`, and the leaf rule
   `c ≤ mass x → c * d ≤ expect x (fun _ => d)`. The `?h a` pattern unification that
   `le_expect_bind` needs is the mechanism `le_mass_bind_chooseNat`'s `d a` already uses.
   Note that `refine` with named `?holes` creates synthetic-opaque metavariables that `apply`
   will not assign; use natural metavariables, as `mass_bound` does.
2. **First client: expectation upper bounds**, which has no incumbent to regress. Add
   `expect_bound` and `expect_fixpoint`; the latter is `cost_fixpoint` (`CostFixpoint.lean`) with
   admissibility taken from the continuity theorem. Re-prove `Nat.arbitrary.expected_cost` and
   `Tree.genBST.expect_size_le` in `BasaltTest/` first. The target shape is
   `expect_fixpoint; <arithmetic>`; for `Nat.arbitrary` the prototype's residual goal was
   `1 / 2 * (1 + 0) + 1 / 2 * (1 + 2) ≤ 2`, closed by `ennreal_to_real; norm_num`.
   Two pieces of real design work live here:
   - the **leaf rule** for a callee or recursive call under an expectation judgment: decompose the
     postcondition into an affine combination of quantities the callee has laws for
     (`expect x (fun a => k + h a) ≤ k + B` from `expect x h ≤ B`, using `mass ≤ 1`);
   - **postcondition normalization between rules**: `(node l x r).size` must become
     `l.size + (1 + r.size)` under a cast before the leaf rule matches. `CostBound.tidy` is the
     hook; find out whether a fixed `simp`/`push_cast` set there is enough.
3. **Go/no-go gate.** Compare the generic path's residual goals with the pins in
   `BasaltTest/CostFixpoint.lean`, `BasaltTest/CostBound.lean`, and `BasaltTest/MassBound.lean`. If
   they are not at least as readable, stop: keep the per-judgment rule statements as thin wrappers
   over the `map_X` lemmas and report.
4. **Migrate `mass_bound`** to the lower-bound expectation judgment at postcondition `1`. Pin
   Appendix D's `coin` loop with its correct bound. Delete the fallback rules
   (`le_mass_bind_chooseNat`, `le_mass_bind_chooseInt`, `le_mass_bind_iInf`, `le_mass_ite_min`,
   `le_mass_dite_min`), the fallback loop in `Walk.lean`'s `bound`, and WORKFLOW's
   "`mass_bound` leaves `⨅ x, …`" entry. `expect_coin` states its weights through `Rat.num` and
   `Rat.den`, which `simp`/`norm_num` do not normalize for a literal like `1/2`; fix that
   presentation as part of this step.
5. **Migrate `cost_bound`** only if step 3 passed for it. Its rules are already backward and
   precise, so this is for uniformity, not repair.
6. **Docs.** Update `WORKFLOW.md` (a new recipe for expected cost; the termination notes that
   change), `README.md`, and `CLAUDE.md`'s routing and gotchas. The coverage check in
   `BasaltTest/CostBound.lean` that fails the build when a combinator has a rule for one judgment
   and not the other has nothing left to check once the registry is keyed by combinator; replace
   it with a check that every combinator has its `map_X`.

Later, and optional:

- The soundness half of `sound_complete` by the always walker, leaving completeness to Recipe 1.
- A divergence-deficit judgment (`1 - mass`, which is exactly linear under bind:
  `div (x >>= k) = div x + expect x (div ∘ k)`) so that `mass_fixpoint per_seed` computes the level
  operator that `BasaltExamples/BST/Weighted.lean` transcribes by hand as `bstLevel`, and the
  `ENNReal.one_sub_*` lemmas become rule proofs instead of user steps.
- A relational walk that proves erasure for a whole generator.

## 7. Background, for orientation only

Cite, do not teach (documentation rule 10). The expectation observation is the weakest
pre-expectation transformer (Kozen; McIver and Morgan). Observations as monad morphisms into
specification monads is the "Dijkstra monads for all" view (Maillard et al.). Upper bounds on a
fixpoint go by Park induction (`fix_induct`); lower bounds do not, which is why termination needs
`LfpIsOne` or a ranking argument (Hark et al., "Aiming low is harder"). Soundness plus completeness
is a Hoare triple plus a reverse-Hoare (incorrectness) triple.

## Appendix A: observations, `oneOf`, and the expectation instance (elaborates)

```lean
import Basalt
open RandomChoice SPMF ENNReal

namespace Proto3

structure Obs (G W : Type → Type) [Monad G] [RandomChoice G] [Monad W] [RandomChoice W] where
  θ : ∀ {α}, G α → W α
  map_pure : ∀ {α} (a : α), θ (Pure.pure a) = Pure.pure a
  map_bind : ∀ {α β} (x : G α) (k : α → G β), θ (x >>= k) = θ x >>= fun a => θ (k a)
  map_choose : ∀ lo hi h, θ (choose lo hi h) = choose lo hi h

variable {G W : Type → Type} [Gen G] [LawfulMonad G] [Monad W] [RandomChoice W] [LawfulMonad W]

theorem Obs.map_map (O : Obs G W) (f : α → β) (x : G α) : O.θ (f <$> x) = f <$> O.θ x := by
  rw [← bind_pure_comp, O.map_bind, ← bind_pure_comp]
  simp only [O.map_pure]

private theorem idx_lt {gs : List γ} (hne : gs ≠ []) {i : Nat} (h : 0 ≤ i ∧ i ≤ gs.length - 1) :
    i < gs.length := by
  have := List.length_pos_iff.mpr hne; omega

/-- The ONE lemma about `oneOf`, for every observation and both interpretations. -/
theorem Obs.map_oneOf (O : Obs G W) (gs : List (Unit → G α)) (hne : gs ≠ []) :
    O.θ (oneOf gs hne) =
      (ULift.down <$> choose 0 (gs.length - 1) (Nat.zero_le _)) >>= fun i =>
        O.θ ((gs[i.val]'(idx_lt hne i.property)) ()) := by
  unfold oneOf Helpers.oneOfAux
  rw [O.map_bind, O.map_map, O.map_choose]
  congr 1
  funext ⟨i, h1, h2⟩
  rfl

/-! ## Spec monad and algebras -/

class Mix (Ω : Type) where
  mix : (lo hi : Nat) → (ULift.{0} {x : Nat // lo ≤ x ∧ x ≤ hi} → Ω) → Ω

def WP (Ω : Type) (α : Type) : Type := (α → Ω) → Ω
instance : Monad (WP Ω) where
  pure a := fun f => f a
  bind m k := fun f => m (fun a => k a f)
instance : LawfulMonad (WP Ω) := LawfulMonad.mk' _
  (id_map := fun _ => rfl) (pure_bind := fun _ _ => rfl) (bind_assoc := fun _ _ _ => rfl)
instance [Mix Ω] : RandomChoice (WP Ω) where
  choose lo hi _ := fun f => Mix.mix lo hi f

instance : Mix Prop where mix _ _ F := ∀ x, F x
noncomputable instance : Mix ℝ≥0∞ where
  mix lo hi F := ∑' a, (1 / ((hi - lo + 1 : ℕ) : ℝ≥0∞)) * F a

/-! ## Two observations: three laws each -/

noncomputable def expectObs : Obs SPMF (WP ℝ≥0∞) where
  θ g := fun f => expect g f
  map_pure a := by funext f; exact expect_pure a f
  map_bind x k := by funext f; exact expect_bind x k f
  map_choose lo hi h := rfl

def alwaysObs : Obs SPMF (WP Prop) where
  θ g := fun Q => ∀ a ∈ g.support, Q a
  map_pure a := by
    funext Q; apply propext
    exact ⟨fun h => h a (mem_support_pure_iff.mpr rfl), fun h b hb => mem_support_pure_iff.mp hb ▸ h⟩
  map_bind x k := by
    funext Q; apply propext
    show (∀ b ∈ (x >>= k).support, Q b) ↔ ∀ a ∈ x.support, ∀ b ∈ (k a).support, Q b
    simp only [mem_support_bind_iff]
    exact ⟨fun h a ha b hb => h b ⟨a, ha, hb⟩, fun h b ⟨a, ha, hb⟩ => h a ha b hb⟩
  map_choose lo hi h := by
    funext Q; apply propext
    exact ⟨fun hq x => hq x (mem_support_choose_iff.mpr trivial), fun hq a _ => hq a⟩

/-! ## Presentation of the "list index" choice shape: one lemma per algebra, none per combinator -/

theorem mix_index_prop {γ : Type} (l : List γ) (hne : l ≠ []) (F : γ → Prop) :
    (∀ a : ULift.{0} {x : Nat // 0 ≤ x ∧ x ≤ l.length - 1},
      F (l[a.down.val]'(idx_lt hne a.down.property))) ↔ ∀ g ∈ l, F g := by
  constructor
  · intro h g hg
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hg
    exact h ⟨⟨i, by omega, by omega⟩⟩
  · intro h a; exact h _ (List.getElem_mem _)

private theorem sum_range_getD (l : List ℝ≥0∞) :
    ∑ n ∈ Finset.range l.length, l.getD n 0 = l.sum := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    rw [List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, ih, List.sum_cons]
    exact add_comm _ _

theorem mix_index_ennreal {γ : Type} (l : List γ) (hne : l ≠ []) (F : γ → ℝ≥0∞) :
    (∑' a : ULift.{0} {x : Nat // 0 ≤ x ∧ x ≤ l.length - 1},
      (1 / ((l.length - 1 - 0 + 1 : ℕ) : ℝ≥0∞)) * F (l[a.down.val]'(idx_lt hne a.down.property)))
      = (l.map F).sum / (l.length : ℝ≥0∞) := by
  have hlen := List.length_pos_iff.mpr hne
  have hT : l.length - 1 - 0 + 1 = l.length := by omega
  trans ∑' a : ULift.{0} {x : Nat // 0 ≤ x ∧ x ≤ l.length - 1},
      (fun n : Nat => (1 / ((l.length - 1 - 0 + 1 : ℕ) : ℝ≥0∞)) * (l.map F).getD n 0) a.down.val
  · refine tsum_congr fun ⟨⟨i, _, hi⟩⟩ => ?_
    have hi' : i < l.length := by omega
    simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi']
  · refine (tsum_subtype_Icc 0 (l.length - 1) (fun n : Nat =>
      (1 / ((l.length - 1 - 0 + 1 : ℕ) : ℝ≥0∞)) * (l.map F).getD n 0)).trans ?_
    have hIcc : Finset.Icc 0 (l.length - 1) = Finset.range (l.map F).length := by
      ext n; simp only [Finset.mem_Icc, Finset.mem_range, List.length_map]; omega
    rw [hIcc, hT, ← Finset.mul_sum, sum_range_getD, one_div, div_eq_mul_inv, mul_comm]

/-! ## Payoff: three facts about `oneOf`, none proved about `oneOf` -/

theorem expect_oneOf {α : Type} (gs : List (Unit → SPMF α)) (hne : gs ≠ []) (f : α → ℝ≥0∞) :
    expect (oneOf gs hne) f = (gs.map fun g => expect (g ()) f).sum / (gs.length : ℝ≥0∞) := by
  have h := congrFun (expectObs.map_oneOf gs hne) f
  exact h.trans (mix_index_ennreal gs hne fun g => expect (g ()) f)

theorem mass_oneOf' {α : Type} (gs : List (Unit → SPMF α)) (hne : gs ≠ []) :
    (oneOf gs hne).mass = (gs.map fun g => (g ()).mass).sum / (gs.length : ℝ≥0∞) := by
  simpa only [expect_one] using expect_oneOf gs hne (fun _ => 1)

theorem always_oneOf' {α : Type} (gs : List (Unit → SPMF α)) (hne : gs ≠ []) (Q : α → Prop) :
    (∀ a ∈ (oneOf gs hne).support, Q a) ↔ ∀ g ∈ gs, ∀ a ∈ (g ()).support, Q a := by
  have h := congrFun (alwaysObs.map_oneOf gs hne) Q
  exact (iff_of_eq h).trans (mix_index_prop gs hne fun g => ∀ a ∈ (g ()).support, Q a)

end Proto3
```

## Appendix B: the cost family and `pick` at two judgments (elaborates)

This file predates Appendix A and defines `Mix.mix` over the bare subtype; prefer Appendix A's
`ULift` form.

```lean
import Basalt
open RandomChoice SPMF ENNReal

namespace Proto2

/-- A `choose`-preserving monad morphism between two generator monads. -/
structure Obs (G W : Type → Type) [Monad G] [RandomChoice G] [Monad W] [RandomChoice W] where
  θ : ∀ {α}, G α → W α
  map_pure : ∀ {α} (a : α), θ (Pure.pure a) = Pure.pure a
  map_bind : ∀ {α β} (x : G α) (k : α → G β), θ (x >>= k) = θ x >>= fun a => θ (k a)
  map_choose : ∀ lo hi h, θ (choose lo hi h) = choose lo hi h

variable {G W : Type → Type} [Monad G] [RandomChoice G] [Monad W] [RandomChoice W]

/-! ## One lemma per combinator, for every observation at once -/

theorem Obs.map_ite (O : Obs G W) (p : Prop) [Decidable p] (x y : G α) :
    O.θ (if p then x else y) = if p then O.θ x else O.θ y := by split <;> rfl

theorem Obs.map_pick (O : Obs G W) (x y : Unit → G α) :
    O.θ (pick x y) = pick (fun u => O.θ (x u)) (fun u => O.θ (y u)) := by
  simp only [pick, O.map_bind, O.map_choose, O.map_ite]

theorem Obs.map_coin (O : Obs G W) (r : Rat) : O.θ (coin r) = coin r := by
  simp only [coin, O.map_bind, O.map_choose, O.map_ite, O.map_pure]

/-! ## The spec monads: continuation monads over an algebra with a "mix" -/

class Mix (Ω : Type) where
  mix : (lo hi : Nat) → ({x : Nat // lo ≤ x ∧ x ≤ hi} → Ω) → Ω

/-- Plain predicate/expectation transformers. -/
def WP (Ω : Type) (α : Type) : Type := (α → Ω) → Ω
instance : Monad (WP Ω) where
  pure a := fun f => f a
  bind m k := fun f => m (fun a => k a f)
instance [Mix Ω] : RandomChoice (WP Ω) where
  choose lo hi _ := fun f => Mix.mix lo hi (fun x => f ⟨x⟩)

/-- Cost-tracking transformers: the post also sees the number of choices. -/
def WPC (Ω : Type) (α : Type) : Type := (α → Nat → Ω) → Ω
instance : Monad (WPC Ω) where
  pure a := fun f => f a 0
  bind m k := fun f => m (fun a n => k a (fun b m' => f b (n + m')))
instance [Mix Ω] : RandomChoice (WPC Ω) where
  choose lo hi _ := fun f => Mix.mix lo hi (fun x => f ⟨x⟩ 1)

/-! ## The algebras: one instance per *kind* of judgment -/

/-- "Always": mix is ∀. -/
instance : Mix Prop where mix _ _ F := ∀ x, F x

/-- Expectation: mix is the average. -/
noncomputable instance : Mix ℝ≥0∞ where
  mix lo hi F := (∑' x, F x) / ((hi - lo + 1 : ℕ) : ℝ≥0∞)

/-! ## The observations: their three laws are the only per-judgment proofs -/

def alwaysObs : Obs SPMF (WP Prop) where
  θ g := fun Q => ∀ a ∈ g.support, Q a
  map_pure a := by
    funext Q; apply propext
    exact ⟨fun h => h a (mem_support_pure_iff.mpr rfl), fun h b hb => mem_support_pure_iff.mp hb ▸ h⟩
  map_bind x k := by
    funext Q; apply propext
    show (∀ b ∈ (x >>= k).support, Q b) ↔ ∀ a ∈ x.support, ∀ b ∈ (k a).support, Q b
    simp only [mem_support_bind_iff]
    constructor
    · intro h a ha b hb; exact h b ⟨a, ha, hb⟩
    · rintro h b ⟨a, ha, hb⟩; exact h a ha b hb
  map_choose lo hi h := by
    funext Q; apply propext
    constructor
    · intro hq x; exact hq ⟨x⟩ (mem_support_choose_iff.mpr trivial)
    · intro hq a _; exact hq a.down

def alwaysCostObs : Obs SPMF.Cost (WPC Prop) where
  θ g := fun Q => SPMF.Cost.Always g Q
  map_pure a := by
    funext Q
    simp only [Pure.pure, WPC, eq_iff_iff]
    exact ⟨fun h => h (a, 0) (SPMF.Cost.mem_support_pure_iff.mpr ⟨rfl, rfl⟩),
      SPMF.Cost.always_pure⟩
  map_bind x k := by
    funext Q
    simp only [eq_iff_iff]
    constructor
    · intro h p hp q hq
      exact h (q.1, p.2 + q.2) (SPMF.Cost.mem_support_bind_iff.mpr ⟨p.1, p.2, q.2, hp, hq, rfl⟩)
    · exact SPMF.Cost.always_bind
  map_choose lo hi h := by
    funext Q
    simp only [eq_iff_iff]
    constructor
    · intro hq x; exact hq (⟨x⟩, 1) (SPMF.Cost.mem_support_choose_iff.mpr rfl)
    · intro hq; exact SPMF.Cost.always_choose fun x hx => hq ⟨x, hx⟩

/-! ## Payoff: `pick` at two judgments from the ONE lemma `Obs.map_pick` -/

theorem pick_presentation_prop (F : {x : Nat // 0 ≤ x ∧ x ≤ 1} → Prop) :
    (∀ x, F x) ↔ F ⟨0, by omega⟩ ∧ F ⟨1, by omega⟩ := by
  constructor
  · intro h; exact ⟨h _, h _⟩
  · rintro ⟨h0, h1⟩ ⟨x, hx⟩
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hx.2 with rfl | rfl
    exacts [h0, h1]

example {α : Type} (x y : Unit → SPMF α) (Q : α → Prop) :
    (∀ a ∈ (pick x y).support, Q a)
      ↔ (∀ a ∈ (x ()).support, Q a) ∧ (∀ a ∈ (y ()).support, Q a) := by
  have := congrFun (alwaysObs.map_pick x y) Q
  simp only [alwaysObs] at this
  rw [this]
  simp only [pick, Bind.bind, RandomChoice.choose, Mix.mix]
  rw [pick_presentation_prop]
  simp

example {α : Type} (x y : Unit → SPMF.Cost α) (Q : α → Nat → Prop) :
    SPMF.Cost.Always (pick x y) Q
      ↔ SPMF.Cost.Always (x ()) (fun a n => Q a (1 + n))
        ∧ SPMF.Cost.Always (y ()) (fun a n => Q a (1 + n)) := by
  have := congrFun (alwaysCostObs.map_pick x y) Q
  simp only [alwaysCostObs] at this
  rw [this]
  simp only [pick, Bind.bind, RandomChoice.choose, Mix.mix]
  rw [pick_presentation_prop]
  simp

end Proto2
```

## Appendix C: derived support lemmas and backward lower-bound rules (elaborates, except one arithmetic goal)

Excerpt; it sits under `import Basalt`, `open RandomChoice SPMF ENNReal`. The final `norm_num` of
the `coin` example fails: it leaves `(1/2 : ℚ).num`/`.den` unnormalized, which is the
`expect_coin` presentation problem noted in Stage 2 step 4. Everything before that line, the
structural part, elaborates.

```lean
/-! ## A. Shadows: support lemmas derived from expectation equations -/

theorem expect_pos_iff {p : SPMF α} {f : α → ℝ≥0∞} :
    0 < expect p f ↔ ∃ a ∈ p.support, 0 < f a := by
  unfold expect
  rw [pos_iff_ne_zero, ne_eq, ENNReal.tsum_eq_zero, not_forall]
  constructor
  · rintro ⟨a, ha⟩
    have := mul_ne_zero_iff.mp ha
    exact ⟨a, this.1, pos_iff_ne_zero.mpr this.2⟩
  · rintro ⟨a, ha, hf⟩
    exact ⟨a, mul_ne_zero ha hf.ne'⟩

theorem mem_support_iff_prob_pos {p : SPMF α} {a : α} : a ∈ p.support ↔ 0 < prob p {a} := by
  rw [prob_singleton]; exact (apply_pos_iff p a).symm

theorem mem_support_bind' {x : SPMF α} {k : α → SPMF β} {b : β} :
    b ∈ (x >>= k).support ↔ ∃ a ∈ x.support, b ∈ (k a).support := by
  rw [mem_support_iff_prob_pos, prob_bind, expect_pos_iff]
  simp only [← mem_support_iff_prob_pos]

theorem mem_support_pick' {x y : SPMF α} {a : α} :
    a ∈ (pick (fun () => x) (fun () => y)).support ↔ a ∈ x.support ∨ a ∈ y.support := by
  simp only [mem_support_iff_prob_pos, prob_pick]
  simp [pos_iff_ne_zero]
  tauto

/-! ## B. Backward lower-bound rules (`b ≤ wp g f`, `f` in, `b` out) -/

theorem le_expect_pure {a : α} {f : α → ℝ≥0∞} : f a ≤ expect (Pure.pure a : SPMF α) f :=
  (expect_pure a f).ge

theorem le_expect_bind {x : SPMF α} {k : α → SPMF β} {f : β → ℝ≥0∞} {h : α → ℝ≥0∞} {b : ℝ≥0∞}
    (hk : ∀ a, h a ≤ expect (k a) f) (hx : b ≤ expect x h) : b ≤ expect (x >>= k) f := by
  rw [expect_bind]; exact hx.trans (expect_mono hk)

theorem le_expect_coin {r : Rat} (h0 : 0 ≤ r) (h1 : r ≤ 1) {f : Bool → ℝ≥0∞} :
    (r.num.toNat : ℝ≥0∞) / (r.den : ℝ≥0∞) * f true
      + ((r.den - r.num.toNat : ℕ) : ℝ≥0∞) / (r.den : ℝ≥0∞) * f false
      ≤ expect (coin r : SPMF Bool) f := (expect_coin h0 h1 f).ge

theorem le_expect_ite {p : Prop} [Decidable p] {x y : SPMF α} {f : α → ℝ≥0∞} {c d : ℝ≥0∞}
    (hx : p → c ≤ expect x f) (hy : ¬p → d ≤ expect y f) :
    (if p then c else d) ≤ expect (if p then x else y) f := by
  split <;> simp_all

/-- Leaf: a fact about the mass, used at a constant postexpectation. -/
theorem le_expect_const_of_le_mass {x : SPMF α} {c d : ℝ≥0∞} (hx : c ≤ x.mass) :
    c * d ≤ expect x (fun _ => d) := by
  rw [expect_const]; gcongr

/-- The `coin` loop of the experiment, one step, by the backward rules. -/
example (rec : SPMF Nat) (c : ℝ≥0∞) (hrec : c ≤ rec.mass) :
    1/2 + 1/2 * c ≤ expect (coin (1/2) >>= fun b =>
      if b then (Pure.pure 0 : SPMF Nat) else rec >>= fun n => Pure.pure (n + 1)) (fun _ => 1) := by
  apply le_trans ?arith ?structural
  case structural =>
    apply le_expect_bind
    · intro b
      apply le_expect_ite
      · intro _; exact le_expect_pure
      · intro _
        apply le_expect_bind
        · intro n; exact le_expect_pure
        · exact le_expect_const_of_le_mass hrec
    · apply le_expect_coin <;> norm_num
  norm_num [ENNReal.div_eq_inv_mul]
```

## Appendix D: repro of the mass walker's imprecision

Both examples end in `sorry` on purpose; read the traced goals. The first prints
`LfpIsOne fun c => 1 / 2 * 1 + 1 / 2 * (c * 1)`, the second `LfpIsOne fun c => 1 * min 1 (c * 1)`.

```lean
import Basalt
open RandomChoice SPMF

def coinLoop [Gen G] : G Nat := do
  let b ← coin (1/2)
  if b then pure 0 else do
    let n ← coinLoop
    pure (n + 1)
partial_fixpoint

-- same loop, written with pick
def pickLoop [Gen G] : G Nat :=
  pick (fun () => pure 0) (fun () => do let n ← pickLoop; pure (n + 1))
partial_fixpoint

example : IsAlmostSurelyTerminating (pickLoop) := by
  mass_fixpoint
  trace_state
  sorry

example : IsAlmostSurelyTerminating (coinLoop) := by
  mass_fixpoint
  trace_state
  sorry
```
