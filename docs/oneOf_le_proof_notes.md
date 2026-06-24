# `oneOf_le` Proof Notes

## Status

`oneOf_le` has a remaining `sorry` in its second case. Everything else compiles:
- `List.instPartialOrder`
- `List.monotone_cons`
- `monotone_oneOf` (fixed statement: added `hne : ∀ x, gs x ≠ []`)
- `myGen` end-to-end test

## Proof Structure

```
oneOf l1 h1 ⊑ oneOf l2 h2
```

Split via `PartialOrder.rel_trans` through an intermediate:

```
do let ⟨i, hge, hle_i⟩ ← ULift.down <$> RandomChoice.choose 0 (l1.length - 1) ...
   let g := l2[i]'(by omega)
   g ()
```

- **Case 1 (done):** LHS ⊑ intermediate. Uses `MonoBind.bind_mono_right` — same `choose` call, different continuations (`l1[i]` vs `l2[i]`). Closed by the element-wise hypothesis `hle`.

- **Case 2 (sorry):** Intermediate ⊑ RHS. Same continuation (`l2[i] ()`), but `choose 0 (l1.length - 1) ⋯` vs `choose 0 (l2.length - 1) ⋯`. These are *definitionally equal* by proof irrelevance (the only difference is internal proof terms of type `i < l2.length`), but no surface-level tactic can close it.

## Root Cause

`RandomChoice.choose` returns `m (ULift {x : Nat // lo ≤ x ∧ x ≤ hi})`. The bound `hi` is baked into the *type* of the result. When comparing `oneOf l1` vs `oneOf l2`:

- LHS choose returns `G (ULift {x // 0 ≤ x ∧ x ≤ l1.length - 1})`
- RHS choose returns `G (ULift {x // 0 ≤ x ∧ x ≤ l2.length - 1})`

These are different types when `l1.length ≠ l2.length` definitionally. After the bind, the continuations use `getElem` with proofs derived from the subtype bound, creating terms that are definitionally equal (by proof irrelevance) but syntactically different.

## What Doesn't Work

| Tactic | Why it fails |
|--------|-------------|
| `rw` / `simp` | Can't rewrite `l1.length - 1` → `l2.length - 1` inside `choose` because the return type depends on it |
| `subst` | `l1.length - 1 = l2.length - 1` is not of the form `x = t` (not a free variable) |
| `cases` on the equality | Dependent elimination fails |
| `generalize` | Result is not type-correct (other terms depend on `l1.length`) |
| `▸` | Can't compute the motive (proof term dependency) |
| `congr` | Produces `HEq` goals between the `choose` calls that are equally hard |
| Helper lemma + `▸` | `▸` does syntactic matching including proof subterms; even after `dsimp`, the `getElem` proof terms differ |

## Solutions (pick one)

### Option A: Change `oneOf` to project `.val` before binding

```lean
def oneOf [Gen G] (gs : List (Unit → G α)) (hne : gs ≠ []) : G α := do
  let i ← (·.down.val) <$> RandomChoice.choose 0 (gs.length - 1) (by omega)
  gs[i]! ()
```

This makes both sides of `oneOf_le` produce `G Nat` from the bind (no subtype), so `bind_mono_right` applies directly. The proof then mirrors `Mwe.lean` exactly (using `getElem!_pos`/`getElem!_neg`).

### Option B: Add a `@[simp]` lemma for `RandomChoice.choose` equality

```lean
theorem RandomChoice.choose_congr [RandomChoice m] (h : n₁ = n₂) (h₁ : lo ≤ n₁) (h₂ : lo ≤ n₂) :
    HEq (RandomChoice.choose lo n₁ h₁) (RandomChoice.choose lo n₂ h₂) := by
  subst h; exact HEq.rfl
```

Then use `HEq`-based reasoning to transport across the dependent types.

### Option C: Reformulate `oneOf` to take the bound explicitly

```lean
def oneOf [Gen G] (gs : List (Unit → G α)) (n : Nat) (hn : n = gs.length - 1) (hne : gs ≠ []) : G α := ...
```

Then `oneOf_le` can generalize over `n` and use `subst`.

### Recommended: Option A

Option A is the simplest and matches the working `Mwe.lean` approach. The `hne` proof ensures the list is non-empty, so `gs[i]!` will always be in-bounds at runtime (out-of-bounds returns `default` which is fine for the monotonicity proof).
