/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt

/-!
# Evaluating at a Size

Pins `Basalt/GenHom.lean` and `Basalt/SizeErasure.lean`: `simp only [size_erasure]` evaluates
`g.run n` through every host construct and combinator, leaving `.run` only on the generators the
term is built from, and what it leaves is walked as any other generator.
-/


namespace SizeErasureTest

variable {α β : Type} (n : Nat)

/-! ## The size -/

example (g : WithSize SPMF α) : (Sized.resize 3 g).run n = g.run 3 := by
  simp only [size_erasure]

example (f : Nat → WithSize SPMF α) : (Sized.sized f).run n = (f n).run n := by
  simp only [size_erasure]

example : (getSize : WithSize SPMF Nat).run n = pure n := by
  simp only [size_erasure]

/-- A draw that reads no size is lifted by `←`, and evaluates to itself. -/
example (h : SPMF Nat) :
    (do let x ← h; let k ← getSize; pure (x + k) : WithSize SPMF Nat).run n
      = (do let x ← h; let k ← pure n; pure (x + k)) := by
  simp only [size_erasure]

/-! ## Combinators

One equation per combinator: each fails if the combinator loses its `GenHom.map_` lemma. -/

example (lo hi : Nat) (h : lo ≤ hi) :
    (chooseNat lo hi h : WithSize SPMF Nat).run n = chooseNat lo hi h := by
  simp only [size_erasure]

example (lo hi : Int) (h : lo ≤ hi) :
    (chooseInt lo hi h : WithSize SPMF Int).run n = chooseInt lo hi h := by
  simp only [size_erasure]

example (r : Rat) : (RandomChoice.coin r : WithSize SPMF Bool).run n = RandomChoice.coin r := by
  simp only [size_erasure]

example (xs : List α) (hne : xs ≠ []) :
    (elements xs hne : WithSize SPMF α).run n = elements xs hne := by
  simp only [size_erasure]

example (k : Nat) (g : WithSize SPMF α) : (vectorOf k g).run n = vectorOf k (g.run n) := by
  simp only [size_erasure]

example (k : Nat) (g : WithSize SPMF α) :
    (listOfMaxLength k g).run n = listOfMaxLength k (g.run n) := by
  simp only [size_erasure]

example (xs : List α) :
    (permutationOf xs : WithSize SPMF _).run n = permutationOf xs := by
  simp only [size_erasure]

example (g : WithSize SPMF α) : (geometricListOf g).run n = geometricListOf (g.run n) := by
  simp only [size_erasure]

example (g : WithSize SPMF α) : (nonEmptyListOf g).run n = nonEmptyListOf (g.run n) := by
  simp only [size_erasure]

example (g : WithSize SPMF α) (p : α → Bool) :
    (rejectUntil g p).run n = rejectUntil (g.run n) p := by
  simp only [size_erasure]

example (xs : List α) : (sublistOf xs : WithSize SPMF _).run n = sublistOf xs := by
  simp only [size_erasure]

example (xs : List α) : (shuffle xs : WithSize SPMF _).run n = shuffle xs := by
  simp only [size_erasure]

example (gs : Nat → WithSize SPMF α) (f : α → Option β) (m k : Nat) :
    (trySizes gs f m k).run n = trySizes (fun j => (gs j).run n) f m k := by
  simp only [size_erasure]

example (gs : Nat → WithSize SPMF α) (f : α → Option β) (m : Nat) :
    (suchThatFrom gs f m).run n = suchThatFrom (fun j => (gs j).run n) f m := by
  simp only [size_erasure]

/-- A literal choice is evaluated branch by branch, each at the size it runs at. -/
example (g : WithSize SPMF Nat) :
    (oneOf! [fun _ => pure 0, fun _ => g, fun _ => Sized.resize 3 g] : WithSize SPMF Nat).run n
      = oneOf [fun _ => pure 0, fun _ => g.run n, fun _ => g.run 3] := by
  simp only [size_erasure]

example (g : WithSize SPMF Nat) :
    (frequency! [(2, fun _ => getSize), (1, fun _ => if n = 0 then g else pure 1)] :
        WithSize SPMF Nat).run n
      = frequency [(2, fun _ => pure n), (1, fun _ => if n = 0 then g.run n else pure 1)] := by
  simp only [size_erasure]

example (g : WithSize SPMF α) : (listOf g).run n = listOfMaxLength n (g.run n) := by
  simp only [size_erasure]

/-- QuickCheck's sized combinators unfold to the size-agnostic cores. -/
example (f : Nat → Nat) (g : WithSize SPMF α) (p : α → Bool) :
    (scale f (suchThat g p)).run n
      = suchThatFrom (fun j => g.run j) (Option.guard p) (f n) := by
  simp only [size_erasure]

/-! ## Any homomorphism

Naturality asks no monad laws of the target, so a sized generator is evaluated at `IO` too. -/

example (k : Nat) (g : WithSize IO α) :
    (listOfMaxLength k g).run n = listOfMaxLength k (g.run n) := by
  simp only [size_erasure]

example {G H : Type → Type} [Gen G] [Gen H] (φ : GenHom G H) (g : G α) :
    φ.map (geometricListOf (vectorOf 3 g) >>= fun xss => pure xss.length)
      = geometricListOf (vectorOf 3 (φ.map g)) >>= fun xss => pure xss.length := by
  simp only [size_erasure]

/-! ## A recursive sized generator

Its law is by induction on the size; the recursive call comes out at the size it was resized to,
where the induction hypothesis bounds it. -/

/-- A list no longer than the size. -/
def boundedList [Gen G] [Sized G] [MonoSized G] : G (List Nat) :=
  Sized.sized fun
    | 0 => pure []
    | n + 1 =>
      frequency! [
        (1, fun _ => pure []),
        (3, fun _ => do
          let x ← chooseNat 0 9
          let xs ← Sized.resize n boundedList
          pure (x :: xs))]
partial_fixpoint

theorem boundedList.sound : IsSoundFor ((boundedList : WithSize SPMF _).run n) (·.length ≤ n) := by
  induction n with
  | zero =>
    rw [boundedList, IsSoundFor.iff_obs]; simp only [size_erasure]; walk
    simp_all
  | succ n ih =>
    rw [boundedList, IsSoundFor.iff_obs]; simp only [size_erasure]; walk [ih.obs]
    all_goals simp_all

end SizeErasureTest
