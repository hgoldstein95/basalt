/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
module

public import Basalt.Enum.Finite
public import Std.Data.HashMap

/-!
# Memoized Enumeration

An enumeration of a recursive generator wants each recursive call computed once. A generator written
in open-recursion form, where a call may consult only smaller arguments, can be closed off two ways:
by recursing (`fix`), or with a table, so that each recursive call is a lookup. The generator is the
same either way; only how its recursion is closed changes, and only at an interpretation whose
values are data, like `Finite`, does the sharing save work.

* `SizedStep`: recursion on a size, tabled in an array built left to right. `table_eq_fix`: the
  table is `fix`, at every interpretation.
* `KeyedStep`: recursion on keys of decreasing rank (a context and a type as well as a size, say),
  tabled in a hash map threaded through the run as state (`MemoM`). Nothing is trusted: `memoPure`
  is an ordinary total function, as fast as a mutable table, because the table is used linearly
  and Lean updates it in place.

Not yet proved: `memoPure` is `fix`, key for key. It relates one generic step at two
interpretations, so it is proved per generator, as every relation between interpretations is.
-/

@[expose] public section

namespace Basalt

/-! ## Recursion on a size -/

/-- A sized generator in open-recursion form: size `n` may consult only smaller sizes. -/
abbrev SizedStep (G : Type → Type) (α : Type) : Type :=
  (n : Nat) → ((k : Nat) → k < n → G α) → G α

namespace SizedStep

variable {G : Type → Type} {α : Type}

/-- Close the recursion by recursing. -/
def fix (step : SizedStep G α) (n : Nat) : G α :=
  step n fun k _ => fix step k

/-- The slices `0, …, n` of `step`, each computed once from the ones before it. -/
def table (step : SizedStep G α) : (n : Nat) → { t : Array (G α) // t.size = n + 1 }
  | 0 => ⟨#[step 0 fun _ h => absurd h (Nat.not_lt_zero _)], rfl⟩
  | n + 1 =>
    let t := table step n
    ⟨t.1.push (step (n + 1) fun k h => t.1[k]'(by have := t.2; omega)), by simp [t.2]⟩

theorem fix_eq (step : SizedStep G α) (n : Nat) : fix step n = step n fun k _ => fix step k := by
  rw [fix]

/-- Memoizing changes nothing but the work done. -/
theorem table_eq_fix (step : SizedStep G α) (n k : Nat) (hk : k < (table step n).1.size) :
    (table step n).1[k] = fix step k := by
  induction n generalizing k with
  | zero =>
    have : k = 0 := by simp [table] at hk; omega
    subst this
    simp only [table, List.getElem_toArray, List.getElem_cons_zero]
    rw [fix_eq]
    congr
    funext j hj
    exact absurd hj (Nat.not_lt_zero _)
  | succ n ih =>
    simp only [table] at hk ⊢
    rw [Array.getElem_push]
    split
    · exact ih k _
    · have : k = n + 1 := by simp at hk; have := (table step n).2; omega
      subst this
      rw [fix_eq]
      congr
      funext j hj
      exact ih j _

end SizedStep

/-- A step that is defined whenever its recursive calls are has every slice defined: by induction on
the size. -/
theorem SizedStep.fix_defined {α : Type} (step : SizedStep Finite α)
    (h : ∀ n (rec : (k : Nat) → k < n → Finite α), (∀ k hk, rec k hk ≠ .undef) →
      step n rec ≠ .undef) (n : Nat) : SizedStep.fix step n ≠ .undef := by
  induction n using Nat.strongRecOn with
  | _ n ih => rw [SizedStep.fix_eq]; exact h n _ fun k hk => ih k hk

/-- The tiers `0, …, n` of an exactly-sized generator, run at `Finite`, each computed once. -/
def SizedStep.tiers (step : SizedStep Finite α) (n : Nat) : Array (Finite α) := (table step n).1

/-! ## Recursion on keys -/

/-- A generator in open-recursion form over keys `κ`: at key `k` it may consult only keys of smaller
`rank`. -/
abbrev KeyedStep (κ : Type) (rank : κ → Nat) (G : Type → Type) (α : Type) : Type :=
  (k : κ) → ((k' : κ) → rank k' < rank k → G α) → G α

namespace KeyedStep

variable {κ : Type} {rank : κ → Nat} {G : Type → Type} {α : Type}

/-- Close the recursion by recursing. -/
def fix (step : KeyedStep κ rank G α) (k : κ) : G α :=
  step k fun k' _ => fix step k'
termination_by rank k

/-- A step that is defined whenever its recursive calls are is defined at every key: by induction on
the rank. -/
theorem fix_defined {α : Type} (step : KeyedStep κ rank Finite α)
    (h : ∀ k (rec : (k' : κ) → rank k' < rank k → Finite α), (∀ k' hk, rec k' hk ≠ .undef) →
      step k rec ≠ .undef) (k : κ) : fix step k ≠ .undef := by
  suffices ∀ n k, rank k = n → fix step k ≠ .undef from this _ k rfl
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro k hk
    rw [fix]
    exact h k _ fun k' hlt => ih _ (hk ▸ hlt) k' rfl

/-- A recursion relates itself at two interpretations under any relation, if one step does whenever
its recursive calls are related: by induction on the rank. -/
theorem fix_rel {M N : Type → Type} {α : Type} (R : M α → N α → Prop)
    (stepM : KeyedStep κ rank M α) (stepN : KeyedStep κ rank N α)
    (h : ∀ k (recM : (k' : κ) → rank k' < rank k → M α) (recN : (k' : κ) → rank k' < rank k → N α),
      (∀ k' hk, R (recM k' hk) (recN k' hk)) → R (stepM k recM) (stepN k recN)) (k : κ) :
    R (fix stepM k) (fix stepN k) := by
  suffices ∀ n k, rank k = n → R (fix stepM k) (fix stepN k) from this _ k rfl
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro k hk
    rw [fix, fix]
    exact h k _ _ fun k' hlt => ih _ (hk ▸ hlt) k' rfl

end KeyedStep

/-- `Finite`, with a table of the recursion's results so far passed from each step to the next. -/
def MemoM (κ α : Type) [BEq κ] [Hashable κ] (β : Type) : Type :=
  Std.HashMap κ (Finite α) → Finite β × Std.HashMap κ (Finite α)

namespace MemoM

variable {κ α : Type} [BEq κ] [Hashable κ]

/-- The continuations' results over `x`'s entries, most recent first, the table passed through each
in turn. -/
def parts {n : Nat} (f : β → MemoM κ α γ) (idx : Fin n → β) (c : Std.HashMap κ (Finite α)) :
    List (Finite γ) × Std.HashMap κ (Finite α) :=
  Fin.foldl n (fun (acc, c) i => let (y, c) := f (idx i) c; (y :: acc, c)) ([], c)

/-- `Finite.bind`, the table passed through each continuation in turn. -/
def bind (x : MemoM κ α β) (f : β → MemoM κ α γ) : MemoM κ α γ := fun c =>
  match x c with
  | (.undef, c) => (.undef, c)
  | (.mk _ idx, c) =>
    let (ps, c) := parts f idx c
    (Finite.flatten ps.reverse, c)

instance : Monad (MemoM κ α) where
  pure b c := (Finite.singleton b, c)
  bind := MemoM.bind
  map g x c := let (y, c) := x c; (y.map g, c)
  seq f x c := let (g, c) := f c; let (y, c) := x () c; (Finite.seq g y, c)

instance : RandomChoice (MemoM κ α) where
  choose lo hi h c := (RandomChoice.choose (m := Finite) lo hi h, c)

instance : Fail (MemoM κ α) := ⟨fun c => (Finite.empty, c)⟩

end MemoM

namespace KeyedStep

variable {κ : Type} {rank : κ → Nat} {α : Type} [BEq κ] [Hashable κ]

/-- `fix`, each key looked up in the table before it is computed, and recorded after. -/
def memoFix (step : KeyedStep κ rank (MemoM κ α) α) (k : κ) : MemoM κ α α := fun c =>
  match c[k]? with
  | some v => (v, c)
  | none =>
    let (v, c) := step k (fun k' _ => memoFix step k') c
    (v, c.insert k v)
termination_by rank k

/-- `fix` at each key, sharing one table. -/
def memoPure (step : KeyedStep κ rank (MemoM κ α) α) (ks : List κ) : List (Finite α) :=
  (ks.foldl (fun (vs, c) k => let (v, c) := memoFix step k c; (v :: vs, c)) ([], {})).1.reverse

end KeyedStep

end Basalt
