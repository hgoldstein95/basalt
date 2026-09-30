/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt.Combinators.WithSize

/-!
# QuickCheck's Combinators

The combinators of QuickCheck 2.15's `Test.QuickCheck.Gen`, each with its QuickCheck distribution at
every size. Those whose distribution Basalt's own already has — `elements`, `oneOf`, `frequency`,
`vectorOf`, `chooseNat`, `chooseInt` — are not redefined; `listOf` and `suchThat` are `protected`,
since Basalt's own are different generators. Evaluated at a size, each is a combinator that reads no
size (`size_erasure`), which is what its laws are proved about.
-/

open Lean.Order

namespace QuickCheck

export Sized (sized resize)

section combinators

variable {G : Type → Type} {α β : Type}

/-- `g` at the size `f n`, where `n` is the ambient size. -/
def scale [Sized G] (f : Nat → Nat) (g : G α) : G α :=
  sized fun n => resize (f n) g

/-- A list whose length is uniform in `[0, n]` at size `n`. -/
protected def listOf [Gen G] [Sized G] (g : G α) : G (List α) :=
  sized fun n => listOfMaxLength n g

/-- A non-empty list whose length is uniform in `[1, max 1 n]` at size `n`. -/
def listOf1 [Gen G] [Sized G] (g : G α) : G (List α) :=
  sized fun n => do
    let k ← chooseNat 1 (max 1 n) (Nat.le_max_left 1 n)
    vectorOf k g

/-- Each entry of `xs` kept or dropped by a fair coin, in order. -/
def sublistOf [Gen G] : List α → G (List α)
  | [] => pure []
  | x :: xs => do
    let keep ← chooseNat 0 1
    let ys ← sublistOf xs
    pure (if keep = 1 then x :: ys else ys)

/-- `xs` sorted, stably, by a uniform 64-bit key drawn for each entry. Keys that tie keep their
entries in order, so this is not exactly uniform; `permutationOf` is. -/
def shuffle [Gen G] (xs : List α) : G (List α) := do
  let ks ← vectorOf xs.length (chooseInt (-9223372036854775808) 9223372036854775807 (by decide))
  pure (((ks.zip xs).mergeSort fun a b => decide (a.1 ≤ b.1)).map Prod.snd)

/-- Haskell's `round . log . fromIntegral` at `Double`, into `Nat`: `log 0` is `-∞`, taken to `0`.
GHC's own result there depends on which of its rounding paths runs. -/
def logRound (n : Nat) : Nat :=
  (Float.ofNat n).log.round.toUInt64.toNat

/-- An entry of a prefix of `xs` that grows logarithmically with the size, from one entry to all of
`xs` at size `100`. -/
def growingElements [Gen G] [Sized G] (xs : List α) (hne : xs ≠ [] := by gen_side_condition) :
    G α :=
  sized fun n =>
    let k := (logRound n + 1) * xs.length / logRound 100
    elements (xs.take (max 1 k)) (by
      simp only [ne_eq, List.take_eq_nil_iff, not_or]
      exact ⟨by omega, hne⟩)

/-- `gs m`, `gs (m + 1)`, …, `gs (m + k - 1)` in turn, until `f` of a value drawn is `some`. -/
def trySizes [Gen G] (gs : Nat → G α) (f : α → Option β) (m : Nat) : Nat → G (Option β)
  | 0 => pure none
  | k + 1 => do
    let a ← gs m
    if (f a).isSome then pure (f a) else trySizes gs f (m + 1) k

/-- `g` at the sizes `n` through `2 * n`, for size `n`, until a value satisfies `p`; `none` if none
does. -/
def suchThatMaybe [Gen G] [Sized G] (g : G α) (p : α → Bool) : G (Option α) :=
  sized fun n => trySizes (resize · g) (Option.guard p) n (n + 1)

end combinators

section monotonicity

variable {G : Type → Type} [Gen G] {α β : Type} {γ : Sort w} [PartialOrder γ]

@[partial_fixpoint_monotone]
theorem monotone_trySizes (gs : γ → Nat → G α) (f : α → Option β) (m k : Nat)
    (hgs : monotone gs) : monotone fun x => trySizes (gs x) f m k := by
  induction k generalizing m with
  | zero => exact monotone_const _
  | succ k ih =>
    refine monotone_bind _ _ _ (monotone_apply m gs hgs)
      (monotone_of_monotone_apply _ fun a => ?_)
    split
    · exact monotone_const _
    · exact ih (m + 1)

variable [Sized G] [MonoSized G]

/-- `resize · g` as a family, monotone in `g`. -/
private theorem monotone_resizes (g : γ → G α) (hg : monotone g) :
    monotone fun x m => resize m (g x) :=
  monotone_of_monotone_apply _ fun m => monotone_resize G m g hg

@[partial_fixpoint_monotone]
theorem monotone_scale (f : Nat → Nat) (g : γ → G α) (hg : monotone g) :
    monotone fun x => scale f (g x) :=
  monotone_sized G _ (monotone_of_monotone_apply _ fun n => monotone_resize G (f n) g hg)

@[partial_fixpoint_monotone]
theorem monotone_listOf (g : γ → G α) (hg : monotone g) :
    monotone fun x => QuickCheck.listOf (g x) :=
  monotone_sized G _ (monotone_of_monotone_apply _ fun n => monotone_listOfMaxLength n g hg)

@[partial_fixpoint_monotone]
theorem monotone_listOf1 (g : γ → G α) (hg : monotone g) :
    monotone fun x => listOf1 (g x) :=
  monotone_sized G _ (monotone_of_monotone_apply _ fun _ =>
    monotone_bind _ _ _ (monotone_const _)
      (monotone_of_monotone_apply _ fun k => monotone_vectorOf k g hg))

@[partial_fixpoint_monotone]
theorem monotone_suchThatMaybe (g : γ → G α) (p : α → Bool) (hg : monotone g) :
    monotone fun x => suchThatMaybe (g x) p :=
  monotone_sized G _ (monotone_of_monotone_apply _ fun n =>
    monotone_trySizes _ _ n (n + 1) (monotone_resizes g hg))

end monotonicity

section recursive_combinators

variable {G : Type → Type} {α β : Type}

/-- `trySizes gs f n (n + 1)`, then again from `n + 1`, `n + 2`, … until it succeeds. -/
def suchThatFrom [Gen G] (gs : Nat → G α) (f : α → Option β) (n : Nat) : G β := do
  match ← trySizes gs f n (n + 1) with
  | some b => pure b
  | none => suchThatFrom gs f (n + 1)
partial_fixpoint

/-- `admissible` for a bound above by a fixed generator. -/
private theorem admissible_rel_le {δ : Sort u} [CCPO δ] (w : δ) : admissible fun x : δ => x ⊑ w :=
  fun _ hc h => csup_le hc h

@[partial_fixpoint_monotone]
theorem monotone_suchThatFrom [Gen G] {γ : Sort w} [PartialOrder γ] (gs : γ → Nat → G α)
    (f : α → Option β) (n : Nat) (hgs : monotone gs) :
    monotone fun x => suchThatFrom (gs x) f n := by
  intro x y hxy
  refine suchThatFrom.fixpoint_induct (gs x) f (fun z => ∀ n, z n ⊑ suchThatFrom (gs y) f n)
    (admissible_pi_apply _ fun n => admissible_rel_le _) (fun z ih n => ?_) n
  conv => right; rw [suchThatFrom]
  apply PartialOrder.rel_trans
    (MonoBind.bind_mono_left (monotone_trySizes gs f n (n + 1) hgs x y hxy))
  apply MonoBind.bind_mono_right
  rintro (_ | b)
  · exact ih (n + 1)
  · exact PartialOrder.rel_refl

/-- `suchThatMaybe g p` at size `n`, then at `n + 1`, `n + 2`, … until it succeeds. -/
protected def suchThat [Gen G] [Sized G] (g : G α) (p : α → Bool) : G α :=
  sized fun n => suchThatFrom (resize · g) (Option.guard p) n

/-- `suchThat` on `f` of each value drawn, until `f` gives `some`. -/
def suchThatMap [Gen G] [Sized G] (g : G α) (f : α → Option β) : G β :=
  sized fun n => suchThatFrom (resize · g) f n

variable [Gen G] [Sized G] [MonoSized G] {γ : Sort w} [PartialOrder γ]

@[partial_fixpoint_monotone]
theorem monotone_suchThat (g : γ → G α) (p : α → Bool) (hg : monotone g) :
    monotone fun x => QuickCheck.suchThat (g x) p :=
  monotone_sized G _ (monotone_of_monotone_apply _ fun n =>
    monotone_suchThatFrom _ _ n (monotone_resizes g hg))

@[partial_fixpoint_monotone]
theorem monotone_suchThatMap (g : γ → G α) (f : α → Option β) (hg : monotone g) :
    monotone fun x => suchThatMap (g x) f :=
  monotone_sized G _ (monotone_of_monotone_apply _ fun n =>
    monotone_suchThatFrom _ _ n (monotone_resizes g hg))

end recursive_combinators

/-! ## At a size

Each combinator evaluated at a size, as one that reads no size. -/

section size_erasure

open WithSize

variable {G : Type → Type} [Gen G] {α β : Type} (n : Nat)

@[size_erasure]
theorem scale_apply (f : Nat → Nat) (g : WithSize G α) : (scale f g) n = g (f n) := rfl

@[size_erasure]
theorem listOf_apply (g : WithSize G α) :
    (QuickCheck.listOf g : WithSize G (List α)) n = listOfMaxLength n (g n) :=
  listOfMaxLength_apply n n g

@[size_erasure]
theorem listOf1_apply (g : WithSize G α) :
    (listOf1 g : WithSize G (List α)) n
      = chooseNat 1 (max 1 n) (Nat.le_max_left 1 n) >>= fun k => vectorOf k (g n) := by
  show (_ >>= _ : WithSize G _) n = _
  rw [bind_apply, chooseNat_apply]
  congr 1
  funext k
  exact vectorOf_apply n k g

@[size_erasure]
theorem sublistOf_apply (xs : List α) : (sublistOf xs : WithSize G (List α)) n = sublistOf xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    unfold sublistOf
    rw [bind_apply, chooseNat_apply]
    congr 1
    funext keep
    rw [bind_apply, ih]
    rfl

@[size_erasure]
theorem shuffle_apply (xs : List α) : (shuffle xs : WithSize G (List α)) n = shuffle xs := by
  unfold shuffle
  rw [bind_apply, vectorOf_apply, chooseInt_apply]
  rfl

@[size_erasure]
theorem growingElements_apply (xs : List α) (hne : xs ≠ []) :
    (growingElements xs hne : WithSize G α) n
      = elements (xs.take (max 1 ((logRound n + 1) * xs.length / logRound 100))) (by
          simp only [ne_eq, List.take_eq_nil_iff, not_or]
          exact ⟨by omega, hne⟩) :=
  elements_apply n _ _

@[size_erasure]
theorem trySizes_apply (gs : Nat → WithSize G α) (f : α → Option β) (m k : Nat) :
    (trySizes gs f m k : WithSize G (Option β)) n = trySizes (fun j => gs j n) f m k := by
  induction k generalizing m with
  | zero => rfl
  | succ k ih =>
    unfold trySizes
    rw [bind_apply]
    congr 1
    funext a
    rw [ite_apply, ih]
    rfl

@[size_erasure]
theorem suchThatMaybe_apply (g : WithSize G α) (p : α → Bool) :
    (suchThatMaybe g p : WithSize G (Option α)) n = trySizes g (Option.guard p) n (n + 1) :=
  trySizes_apply n _ _ _ _

@[size_erasure]
theorem suchThatFrom_apply (gs : Nat → WithSize G α) (f : α → Option β) (k : Nat) :
    (suchThatFrom gs f k : WithSize G β) n = suchThatFrom (fun j => gs j n) f k := by
  apply PartialOrder.rel_antisymm
  · refine suchThatFrom.fixpoint_induct (G := WithSize G) gs f
      (fun z => ∀ k, z k n ⊑ suchThatFrom (fun j => gs j n) f k)
      (admissible_pi_apply (fun k (y : WithSize G β) => y n ⊑ suchThatFrom (fun j => gs j n) f k)
        fun k => admissible_apply (fun _ y => y ⊑ suchThatFrom (fun j => gs j n) f k) n
          (admissible_rel_le _))
      (fun z ih k => ?_) k
    conv => right; rw [suchThatFrom]
    simp only [bind_apply, trySizes_apply]
    apply MonoBind.bind_mono_right
    rintro (_ | b)
    · exact ih (k + 1)
    · exact PartialOrder.rel_refl
  · refine suchThatFrom.fixpoint_induct (G := G) (fun j => gs j n) f
      (fun z => ∀ k, z k ⊑ (suchThatFrom gs f k : WithSize G β) n)
      (admissible_pi_apply _ fun k => admissible_rel_le _) (fun z ih k => ?_) k
    conv => right; rw [suchThatFrom]
    simp only [bind_apply, trySizes_apply]
    apply MonoBind.bind_mono_right
    rintro (_ | b)
    · exact ih (k + 1)
    · exact PartialOrder.rel_refl

@[size_erasure]
theorem suchThat_apply (g : WithSize G α) (p : α → Bool) :
    (QuickCheck.suchThat g p : WithSize G α) n = suchThatFrom g (Option.guard p) n :=
  suchThatFrom_apply n _ _ _

@[size_erasure]
theorem suchThatMap_apply (g : WithSize G α) (f : α → Option β) :
    (suchThatMap g f : WithSize G β) n = suchThatFrom g f n :=
  suchThatFrom_apply n _ _ _

end size_erasure

end QuickCheck
