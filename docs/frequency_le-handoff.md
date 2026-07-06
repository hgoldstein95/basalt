# Handoff: proving `frequency_le` (monotonicity of the `frequency` combinator)

**Goal:** finish the `frequency` monotonicity machinery in `Basalt/Combinators.lean` so
recursive generators built with `frequency` can be defined via `partial_fixpoint`.

## ⚠️ Current repo state (read first)

Branch: **`frequency_monotone`**. All scaffolding is **committed and building**; the file
has exactly **one remaining `sorry`** — the body of **`frequency_le`** (Combinators.lean
~line 338). `monotone_frequency` already calls `frequency_le`, so closing that one `sorry`
completes the feature.

Everything below is present and compiling:

| Piece | Location | Status |
|---|---|---|
| `Helpers.frequencySelect` (renamed traversal) | Combinators.lean ~33 | ✅ done |
| `Helpers.frequencyAux` (bound-parameterized wrapper) | ~69 | ✅ done |
| `frequency` delegates to wrapper | ~101 | ✅ done |
| `PartialOrder (List α)` (generic) | ~108 | ✅ done |
| `PartialOrder (Nat × α)` (discrete weight + `⊑` on snd) | ~147 | ✅ done |
| `List.monotone_cons` | ~176 | ✅ done (`@[partial_fixpoint_monotone]`) |
| `le_of_eq` | ~200 | ✅ done |
| `frequencyAux_congr` | ~216 | ✅ done |
| `frequencySelect_le` | ~228 | ✅ done, `lean_verify` clean |
| `sumOfWeights_le` (equal weights ⇒ equal totals) | ~269 | ✅ done, `lean_verify` clean |
| `monotone_pair_snd` | ~328 | ✅ done (`@[partial_fixpoint_monotone]`) |
| **`frequency_le`** | **~338** | **❌ `sorry` — THE TASK** |
| `monotone_frequency` | ~347 | ✅ done (`@[partial_fixpoint_monotone]`), depends on `frequency_le` |

`Basalt/SPMF/Support.lean` is already fully migrated: traversal refs renamed to
`frequencySelect` / `frequencySelect_mem` / `frequencySelect_n_exists`, and
`Helpers.frequencyAux` added to the two `simp only [frequency, ...]` sets (lines ~334, ~347)
so the support proofs still see through the wrapper. Do not re-do this.

Note: the design chose the **element-level `Prod` instance + generic `List.instPartialOrder`**
route (not a bespoke `List (Nat × α)` instance), so there is no instance diamond and
`monotone_cons` + `monotone_pair_snd` compose on `frequency` literals for free.

## THE TASK: prove `frequency_le`

Current statement + stub (Combinators.lean ~338):

```lean
theorem frequency_le [Gen G] {l1 l2 : List (Nat × (Unit → G α))} (h : l1 ⊑ l2)
    (h1 : 0 < List.sum (List.map Prod.fst l1))
    (h2 : 0 < List.sum (List.map Prod.fst l2)) :
    frequency l1 h1 ⊑ frequency l2 h2 := by
  sorry
```

### Proof strategy (mirror of `oneOf_le`, which is right below it ~line 287)

Let `total₁ = sum (map Prod.fst l1)`, `total₂ = sum (map Prod.fst l2)`. Unfolding
`frequency`, each side is `frequencyAux lᵢ totalᵢ rfl`. The two calls differ in BOTH
`l` and `total`, so relate them through the intermediate `frequencyAux l2 total₁ htotal`
(fix the total to `total₁`, change the list first; then reconcile the total). The needed
`htotal : total₁ = sum (map Prod.fst l2)` is exactly **`sumOfWeights_le h`**.

```lean
  apply PartialOrder.rel_trans
    (y := Helpers.frequencyAux l2 (List.sum (List.map Prod.fst l1)) (sumOfWeights_le h))
```

**Leg 1** — `frequencyAux l1 total₁ ⊑ frequencyAux l2 total₁` (same total, list changes):
- `simp only [frequency, Helpers.frequencyAux]`
- `apply MonoBind.bind_mono_right` — discharges the shared `choose 0 (total₁ - 1)` bind
  (this is exactly the move in `oneOf_le` leg 1).
- Introduce the drawn index; goal becomes a `dite` on `n < total₁` on BOTH sides with the
  SAME condition (same total), so `split` (or `split_ifs`) gives:
  - then-branch: `frequencySelect l1 n _ ⊑ frequencySelect l2 n _` → `exact frequencySelect_le h _ _`
  - else-branch: `default ⊑ default` → `exact PartialOrder.rel_refl` (or `le_of_eq rfl`)

**Leg 2** — `frequencyAux l2 total₁ ⊑ frequencyAux l2 total₂` (same list, total changes):
- `apply le_of_eq` (turn `⊑` into `=`), then `apply frequencyAux_congr`.
- `frequencyAux_congr` needs `hn : total₁ = total₂` — supply `sumOfWeights_le h`; the two
  `heqᵢ` sum-proofs are `rfl`-shaped. `apply frequencyAux_congr <;> first | exact sumOfWeights_le h | rfl`
  (or `apply frequencyAux_congr (sumOfWeights_le h)`).

This is the exact `oneOf_le` skeleton (transitivity → `bind_mono_right` leg → `le_of_eq` +
congruence leg). See `oneOf_le` ~287 and `oneOfAux_congr` ~208 for the mirror.

### The ONE new wrinkle vs `oneOf_le`

`oneOf`'s continuation was a bare `l[i] ()`, so leg 1 finished with a single `apply hle`.
`frequency`'s continuation is a **`dite (n < total₁)`**, so leg 1 needs the extra `split`
producing then (`frequencySelect_le`) and else (`rel_refl`) branches. After
`bind_mono_right`, confirm the two `dite` conditions are the *same* `n < total₁` term so a
single `split` governs both — they should be, since the intermediate deliberately fixes the
total to `total₁`.

### Things that may need fiddling (don't be surprised)

- After `simp only [frequency, Helpers.frequencyAux]` the `dite`/`bind` may need `dsimp` or
  a slightly different simp set to expose `MonoBind.bind_mono_right`. Compare against how
  `oneOf_le` line ~296 unfolds (`simp only [oneOf, Helpers.oneOfAux]`).
- `frequencySelect_le` takes the ORDER hyp `h : l1 ⊑ l2` plus the two in-range proofs; the
  in-range proofs at the drawn `n` come from the `then`-branch's `hn : n < total₁` combined
  with the totals — `omega` / the branch hypothesis should discharge them, possibly needing
  `htotal` to convert `total₁` to `sum (map Prod.fst l2)`.
- The bind on the two sides binds a `ULift`-wrapped subtype; `bind_mono_right` expects you to
  intro that value. Mirror `oneOf_le`'s `intro ⟨i, hge, hle_i⟩` shape if needed.

## Validation once `frequency_le` is closed

1. `lean_diagnostic_messages` on Combinators.lean → expect **zero** `sorry` warnings.
2. `lean_verify frequency_le` and `lean_verify monotone_frequency` → expect axioms
   `propext`, `Quot.sound` only (no `sorryAx`).
3. `lake build` (full) — Support.lean depends on Combinators; expect clean, no warnings.
4. End-to-end: add a recursive `frequency`-based generator closed by `partial_fixpoint`
   (analogue of `myGen` at the bottom of the file) and confirm it elaborates — this exercises
   the whole `monotone_frequency` → `monotone_cons` → `monotone_pair_snd` automation chain:
   ```lean
   def myFreqGen [Gen G] : Unit → G Nat := fun _ =>
     frequency [(1, fun _ => pure 0), (2, fun _ => do let n ← myFreqGen (); pure (n + 1))]
   partial_fixpoint
   ```
   If `partial_fixpoint` succeeds, the attribute chain is wired correctly. (If it fails to
   find monotonicity, check that `monotone_pair_snd` and `monotone_frequency` are both tagged
   `@[partial_fixpoint_monotone]` — they are — and that the pair/list order instances resolve.)

## Session-verified facts to trust

- `frequencySelect_le` and `sumOfWeights_le` compile and pass `lean_verify` (`propext`,
  `Quot.sound`).
- Combinators.lean builds with a single `sorry` warning at `frequency_le`.
- Support.lean migration (renames + `Helpers.frequencyAux` in the two simp sets) is done.
- Not yet validated: `frequency_le` itself and the end-to-end `partial_fixpoint` test.
