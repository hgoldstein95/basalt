/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
module

public import Basalt.Enum
public import BasaltExamples.STLC.GenTerm

/-!
# Enumerating Well-Typed STLC Terms by Exact Size

`termStep` is an exactly-sized generator of the terms of type `τ` in context `Γ`, in open-recursion
form over the key `(Γ, τ, n)`. Run at `Finite` and memoized on the whole key, it is an enumeration:
tier `n` is every well-typed term of size `n`, each computed once.

The only choice the continuation of an application depends on is the argument type, which is drawn
before either subterm; given it, the function and the argument are independent, and `<*>` pairs
them without visiting either. The argument type is drawn from every type up to a bound, almost all
of them uninhabited at that size, which is where the time goes at larger sizes: drawing only from
types with a term of the right size is the obvious next step.
-/

@[expose] public section

namespace STLC

open Basalt RandomChoice

deriving instance Hashable for Ty

/-- The number of constructors in a term, counting its type annotations. Counting the annotations
is what makes each size finite: otherwise `λx:τ. true` would have the same size for every `τ`. -/
def Term.size : Term → Nat
  | .Bool _ => 1
  | .Var _ => 1
  | .App e1 e2 => 1 + e1.size + e2.size
  | .Abs τ e => 1 + τ.size + e.size

/-- The types of size exactly `j`. -/
def tysOfSize (j : Nat) : List Ty :=
  if j = 1 then [.Bool] else
    (List.range j).flatMap fun a =>
      if h : 1 ≤ a ∧ a + 1 < j then
        (tysOfSize a).flatMap fun l => (tysOfSize (j - 1 - a)).map (.Fun l ·)
      else []
termination_by j
decreasing_by all_goals omega

/-- The types of size at most `b`. -/
def tysUpTo (b : Nat) : List Ty := (List.range (b + 1)).flatMap tysOfSize

/-- The size of the largest type in a context. -/
def Ctx.maxSize (Γ : Ctx) : Nat := Γ.foldl (fun m τ => max m τ.size) 0

/-- What a recursive call is about: the context, the type, and the exact size. -/
abbrev Key := Ctx × Ty × Nat

/-- The well-typed terms of type `τ` in `Γ` of size exactly `n`.

A term of size `m` has a type of size at most `2m + |Γ| - 1` (where `|Γ|` is `Γ.maxSize`); bounding
the argument type of an application by that, for both the argument and the function, is what keeps
the draw of the argument type finite. -/
def termStep [Monad G] [RandomChoice G] [Fail G] : KeyedStep Key (·.2.2) G Term :=
  fun ⟨Γ, τ, n⟩ rec =>
  match n, rec with
  | 0, _ => Fail.fail
  | 1, _ => do
    if (← choose 0 1 (by omega)).down.val = 0 then
      if τ == .Bool then pickFrom [.Bool true, .Bool false] else Fail.fail
    else pickFrom (varsWithType Γ τ)
  | n + 2, rec => do
    if (← choose 0 1 (by omega)).down.val = 0 then
      match τ with
      | .Fun τ1 τ2 =>
        if τ1.size ≤ n then
          Term.Abs τ1 <$> rec (τ1 :: Γ, τ2, n + 1 - τ1.size) (by simp; omega)
        else Fail.fail
      | .Bool => Fail.fail
    else
      if hn : 1 ≤ n then do
        let ⟨k, hk⟩ := (← choose 1 n hn).down
        let m := n + 1 - k
        let b := min (2 * m + Γ.maxSize - 1) (2 * k + Γ.maxSize - 2 - τ.size)
        let argTy ← pickFrom (tysUpTo b)
        Term.App <$> rec (Γ, .Fun argTy τ, k) (by simp; omega) <*> rec (Γ, argTy, m) (by simp; omega)
      else Fail.fail

/-- Tiers `0, …, n` of the closed terms of type `τ`, sharing one table. -/
def enumClosed (τ : Ty) (n : Nat) : List (Basalt.Finite Term) :=
  KeyedStep.memoPure (termStep (G := MemoM _ _)) ((List.range (n + 1)).map fun k => ([], τ, k))

/-! ## End to end -/

/-- Every tier is defined. -/
theorem termTier_defined (k : Key) : KeyedStep.fix (G := Basalt.Finite) termStep k ≠ .undef := by
  refine KeyedStep.fix_defined _ (fun ⟨Γ, τ, n⟩ rec hrec => ?_) _
  rcases n with _ | _ | n
  · exact Finite.fail_ne_undef
  · dsimp only [termStep]
    refine Finite.bind_defined (Finite.choose_ne_undef _ _ _) fun _ _ => ?_
    split
    · split
      · exact Finite.pickFrom_defined _
      · exact Finite.fail_ne_undef
    · exact Finite.pickFrom_defined _
  · dsimp only [termStep]
    refine Finite.bind_defined (Finite.choose_ne_undef _ _ _) fun _ _ => ?_
    split
    · cases τ with
      | Fun τ1 τ2 =>
        dsimp only
        split
        · exact Finite.map_defined _ (hrec _ _)
        · exact Finite.fail_ne_undef
      | Bool => exact Finite.fail_ne_undef
    · split
      · refine Finite.bind_defined (Finite.choose_ne_undef _ _ _) fun ⟨⟨k, hk⟩⟩ _ => ?_
        exact Finite.bind_defined (Finite.pickFrom_defined _) fun _ _ =>
          Finite.seq_defined (Finite.map_defined _ (hrec _ _)) (hrec _ _)
      · exact Finite.fail_ne_undef

/-- Every tier lists exactly the terms the exact-size generator, run with failure as `OptionT SPMF`,
can succeed with at that key. -/
theorem termTier_enumerates (k : Key) :
    EnumeratesSome (KeyedStep.fix (G := Basalt.Finite) termStep k)
      (KeyedStep.fix (G := OptionT SPMF) termStep k) := by
  refine KeyedStep.fix_rel (@EnumeratesSome _) _ _ (fun ⟨Γ, τ, n⟩ recM recN hrec => ?_) _
  rcases n with _ | _ | n
  · exact EnumeratesSome.fail
  · dsimp only [termStep]
    refine EnumeratesSome.bind (fun _ => ?_) (EnumeratesSome.choose _ _ _)
    refine genRel_enumeratesSome.ite (fun _ => ?_) (fun _ => EnumeratesSome.pickFrom _)
    exact genRel_enumeratesSome.ite (fun _ => EnumeratesSome.pickFrom _) (fun _ => EnumeratesSome.fail)
  · dsimp only [termStep]
    refine EnumeratesSome.bind (fun _ => ?_) (EnumeratesSome.choose _ _ _)
    refine genRel_enumeratesSome.ite (fun _ => ?_) (fun _ => ?_)
    · cases τ with
      | Fun τ1 τ2 =>
        exact genRel_enumeratesSome.ite (fun _ => EnumeratesSome.map _ (hrec _ _))
          (fun _ => EnumeratesSome.fail)
      | Bool => exact EnumeratesSome.fail
    · refine genRel_enumeratesSome.dite (fun _ => ?_) (fun _ => EnumeratesSome.fail)
      refine EnumeratesSome.bind (fun ⟨⟨k, hk⟩⟩ => ?_) (EnumeratesSome.choose _ _ _)
      exact EnumeratesSome.bind (fun _ => EnumeratesSome.seq (EnumeratesSome.map _ (hrec _ _))
        (hrec _ _)) (EnumeratesSome.pickFrom _)

/-- Memoizing changes nothing: the tiers `enumClosed` computes are `fix`'s. -/
theorem enumClosed_eq (τ : Ty) (n : Nat) :
    enumClosed τ n = (List.range (n + 1)).map
      fun k => KeyedStep.fix (G := Basalt.Finite) termStep ([], τ, k) := by
  unfold enumClosed
  rw [KeyedStep.memoPure_eq _ (termStep (G := Basalt.Finite))
    (fun V ⟨Γ, τ, n⟩ recM recF hrec => ?_)]
  · simp only [List.map_map, Function.comp_def]
  rcases n with _ | _ | n
  · exact MemoM.rel_fail
  · dsimp only [termStep]
    refine MemoM.rel_bind (fun _ => ?_) (MemoM.rel_choose _ _ _)
    refine MemoM.rel_ite (fun _ => ?_) (fun _ => MemoM.rel_pickFrom _)
    exact MemoM.rel_ite (fun _ => MemoM.rel_pickFrom _) (fun _ => MemoM.rel_fail)
  · dsimp only [termStep]
    refine MemoM.rel_bind (fun _ => ?_) (MemoM.rel_choose _ _ _)
    refine MemoM.rel_ite (fun _ => ?_) (fun _ => ?_)
    · cases τ with
      | Fun τ1 τ2 =>
        exact MemoM.rel_ite (fun _ => MemoM.rel_map _ (hrec _ _)) (fun _ => MemoM.rel_fail)
      | Bool => exact MemoM.rel_fail
    · refine MemoM.rel_dite (fun _ => ?_) (fun _ => MemoM.rel_fail)
      refine MemoM.rel_bind (fun ⟨⟨k, hk⟩⟩ => ?_) (MemoM.rel_choose _ _ _)
      exact MemoM.rel_bind (fun _ => MemoM.rel_seq (MemoM.rel_map _ (hrec _ _)) (hrec _ _))
        (MemoM.rel_pickFrom _)

/-- The memoized enumeration, end to end: tier `k` of `enumClosed τ n` is defined, and its entries are
exactly the closed terms of type `τ` that the exact-size generator succeeds with at size `k`. -/
theorem enumClosed_mem_iff (τ : Ty) {n k : Nat} (hk : k ≤ n) (e : Term) :
    ((enumClosed τ n)[k]'(by simp [enumClosed_eq]; omega)).Mem e ↔
      some e ∈ ((KeyedStep.fix (G := OptionT SPMF) termStep ([], τ, k)).run).support := by
  simp only [enumClosed_eq, List.getElem_map, List.getElem_range]
  exact termTier_enumerates _ (termTier_defined _) e

/-- The same tiers, recursing instead of looking up. -/
def enumClosedNaive (τ : Ty) (n : Nat) : List (Basalt.Finite Term) :=
  (List.range (n + 1)).map fun k => KeyedStep.fix (G := Basalt.Finite) termStep ([], τ, k)

/-! ## Brute force, to check against -/

/-- Every term of size exactly `n` whose variables are bound by one of `d` enclosing binders. -/
def rawTerms (d n : Nat) : List Term :=
  match n with
  | 0 => []
  | 1 => [.Bool true, .Bool false] ++ (List.range d).map .Var
  | n + 2 =>
    ((List.range (n + 1)).flatMap fun a =>
      if h : 1 ≤ a then
        (tysOfSize a).flatMap fun τ1 => (rawTerms (d + 1) (n + 1 - a)).map (.Abs τ1)
      else []) ++
    ((List.range (n + 1)).flatMap fun k =>
      if h : 1 ≤ k ∧ k ≤ n then
        (rawTerms d k).flatMap fun e1 => (rawTerms d (n + 1 - k)).map (.App e1)
      else [])
termination_by n
decreasing_by all_goals omega

end STLC
