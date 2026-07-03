# `oneOf_le` Proof Notes

## Status

**Resolved — no remaining `sorry`.** Everything compiles:
- `List.instPartialOrder`
- `List.monotone_cons`
- `oneOf_le` (via `Helpers.oneOfAux` / `oneOfAux_congr`, see below)
- `monotone_oneOf` (fixed statement: added `hne : ∀ x, gs x ≠ []`)
- `myGen` end-to-end test with `partial_fixpoint`

## Design

`oneOf` is a thin wrapper around `Helpers.oneOfAux`, which is the same
combinator with the upper bound of the random index draw exposed as a
parameter `n`:

```lean
def oneOfAux [Gen G] (l : List (Unit → G α)) (n : Nat)
    (hlt : ∀ i, i ≤ n → i < l.length) : G α := do
  let ⟨i, _, hle_i⟩ ← ULift.down <$> RandomChoice.choose 0 n (Nat.zero_le n)
  (l[i]'(hlt i hle_i)) ()

def oneOf [Gen G] (gs : List (Unit → G α)) (hne : gs ≠ []) : G α :=
  Helpers.oneOfAux gs (gs.length - 1) fun i hi => by ...
```

There is deliberately only **one** `do`-block: every fact about `oneOf` is
really a fact about `oneOfAux`, so proofs never have to unify two
independently elaborated `do`-blocks (see "matcher identity" below).
Proofs elsewhere that unfold `oneOf` (e.g. `support_oneOf`,
`IsPMF_oneOf` in `Basalt/SPMF/`) unfold `Helpers.oneOfAux` alongside it.

## Proof Structure

```
oneOf l1 h1 ⊑ oneOf l2 h2
```

Split via `PartialOrder.rel_trans` through the intermediate
`Helpers.oneOfAux l2 (l1.length - 1) _` — indexing into `l2`, but drawing the
index with `l1`'s bound:

- **Case 1:** `oneOf l1 h1 ⊑ oneOfAux l2 (l1.length - 1) _`. After unfolding,
  both sides bind the *same* `choose` call, so `MonoBind.bind_mono_right`
  reduces the goal to comparing continuations (`l1[i] ()` vs `l2[i] ()`),
  closed by the element-wise hypothesis from the list order.

- **Case 2:** `oneOfAux l2 (l1.length - 1) _ ⊑ oneOf l2 h2`. This is a
  propositional *equality*, lifted to `⊑` by `rel_of_eq`:

  ```lean
  private theorem oneOfAux_congr ... (hn : n₁ = n₂) ... :
      Helpers.oneOfAux l n₁ hlt₁ = Helpers.oneOfAux l n₂ hlt₂ := by
    subst hn
    rfl
  ```

  Because the bound is a *variable* of `oneOfAux`, `subst hn` transports the
  equality `l1.length - 1 = l2.length - 1` (which follows from the equal
  lengths in the list order) across the subtype bound baked into the return
  type of `RandomChoice.choose`. The in-bounds hypotheses `hlt₁`/`hlt₂` are
  propositions, so proof irrelevance lets `rfl` close the rest.

## Root Cause (why this needed care)

`RandomChoice.choose` returns `m (ULift {x : Nat // lo ≤ x ∧ x ≤ hi})`. The bound
`hi` is baked into the *type* of the result. When comparing `oneOf l1` vs `oneOf l2`:

- LHS choose returns `G (ULift {x // 0 ≤ x ∧ x ≤ l1.length - 1})`
- RHS choose returns `G (ULift {x // 0 ≤ x ∧ x ≤ l2.length - 1})`

These types are propositionally equal (via `l1.length = l2.length`) but **not
definitionally equal** — the length equality is a hypothesis, not a reduction.
(An earlier version of these notes said the sides were "definitionally equal by
proof irrelevance"; that was wrong. Proof irrelevance handles the *proof terms*,
but the bound `l1.length - 1` vs `l2.length - 1` is a data-level difference
inside a type, which only `subst` on a variable can transport.)

There were actually **two** independent obstacles:

1. **The dependent bound** — solved by generalizing the bound to a variable
   (`oneOfAux`'s parameter `n`) so `subst` applies. No rewrite works in place
   because the return type of `choose` depends on the bound.

2. **Matcher identity** — each `do`-block with a destructuring bind elaborates
   to its own anonymous matcher constant (e.g. `oneOf.match_1`), and Lean's
   unifier refuses to equate two *distinct* matcher constants even when they
   are structurally identical: goals can pretty-print character-for-character
   the same and still fail `rfl`, `exact`, and even `with_unfolding_all rfl`.
   Solved structurally: `oneOf` *is* `oneOfAux`, so there is only one
   `do`-block (hence one matcher) in the first place, and `oneOfAux_congr`
   relates two instances of the same constant.

## What Doesn't Work

| Approach | Why it fails |
|----------|-------------|
| `rw` / `simp` | Can't rewrite `l1.length - 1` → `l2.length - 1` inside `choose` because the return type depends on it |
| `subst` in place | `l1.length - 1 = l2.length - 1` is not of the form `x = t` (not a free variable) |
| `cases` on the equality | Dependent elimination fails |
| `generalize` | Result is not type-correct (other terms depend on `l1.length`) |
| `▸` | Can't compute the motive (proof term dependency) |
| `congr` alone | Produces `HEq` goals between the `choose` calls that are equally hard |
| Helper lemma stating both `do`-blocks (old `oneOf_choose_irrelevant`) + `exact`/`▸` | Dies on matcher identity: the lemma's `do`-block and the goal's elaborate to different matcher constants (and even `let` vs `have` for the same source syntax), so defeq fails despite identical pretty-printing |
| Separate `oneOfAux` duplicating `oneOf`'s `do`-block | Works, but needs a `congr 1; funext ⟨i, _, hle_i⟩; rfl` dance to cross the matcher-identity gap between the two `do`-blocks (applying both matchers to an explicit constructor forces iota-reduction). Superseded by defining `oneOf` *in terms of* `oneOfAux`, which makes the equality a `subst; rfl`. |
| Raw `HEq` transport (old "Option B") | `choose_congr` itself is trivial (`subst h; rfl`), but *consuming* the `HEq` needs `bind`/`map` congruence across different type arguments plus `Function.hfunext` for the continuations — which does not exist in core Lean and would have to be hand-rolled. And even with all that plumbing, the matcher-identity obstacle (#2 above) remains. Prototyped and abandoned. |

## Takeaways

- When a bound/index is baked into a dependent type, don't try to rewrite it at
  the use site — parameterize the definition over the bound, prove the
  congruence with `subst`, and instantiate.
- When two syntactically identical `do`-blocks refuse to unify, suspect matcher
  constants. Best fix: don't have two `do`-blocks (define one in terms of the
  other). Fallback: force iota-reduction by applying both matchers to an
  explicit constructor (`funext ⟨...⟩` / destructuring `intro`).
- `HEq` was never needed: both sides of the final equation live at the same
  type `G α`; heterogeneity only appears *inside* the bind, and
  parameterize-then-`subst` dissolves it before any comparison happens.
