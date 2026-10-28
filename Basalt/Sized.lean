/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
module

public import Basalt.Gen
public import Basalt.Fail

/-!
# Size-Parameterized Generators

`Sized` gives a generator monad an ambient size parameter to branch on, and `WithSize G` adds a size
to any generator monad `G`; `OptionT` preserves both. `MonoSized` is the side condition that lets
`sized` and `resize` appear in the body of a `partial_fixpoint`.
-/

@[expose] public section

open Lean.Order

/-- A monad with an ambient size parameter. -/
class Sized (g : Type u → Type v) where
  sized {α : Type u} : (Nat → g α) → g α
  resize {α : Type u} : Nat → g α → g α

def getSize [Monad m] [Sized m] : m Nat := Sized.sized (fun n => pure n)

/-- The monotonicity facts `sized` and `resize` must satisfy for a recursive generator that uses
them to be definable by `partial_fixpoint`; the analogue of `MonoBind` for `Sized`. -/
class MonoSized (g : Type u → Type v) [Sized g] [∀ α, PartialOrder (g α)] where
  sized_mono {α : Type u} {f₁ f₂ : Nat → g α} (h : ∀ n, f₁ n ⊑ f₂ n) :
    Sized.sized f₁ ⊑ Sized.sized f₂
  resize_mono {α : Type u} {n : Nat} {x y : g α} (h : x ⊑ y) :
    Sized.resize n x ⊑ Sized.resize n y

/-- Lemma allowing us to use `sized` in functions marked as `partial_fixpoint` (the `monotonicity`
tactic is used under the hood by `partial_fixpoint`). -/
@[partial_fixpoint_monotone]
theorem monotone_sized (g : Type u → Type v) [Sized g] [∀ α, PartialOrder (g α)] [MonoSized g]
    {α : Type u} {γ : Sort w} [PartialOrder γ]
    (f : γ → Nat → g α) (hmono : monotone f) :
    monotone (fun x => Sized.sized (f x)) :=
  fun x y hxy => MonoSized.sized_mono (hmono x y hxy)

/-- Lemma allowing us to use `resize` in functions marked as `partial_fixpoint` (the `monotonicity`
tactic is used under the hood by `partial_fixpoint`). -/
@[partial_fixpoint_monotone]
theorem monotone_resize (g : Type u → Type v) [Sized g] [∀ α, PartialOrder (g α)] [MonoSized g]
    {α : Type u} {γ : Sort w} [PartialOrder γ] (n : Nat)
    (f : γ → g α) (hmono : monotone f) :
    monotone (fun x => Sized.resize n (f x)) :=
  fun x y hxy => MonoSized.resize_mono (hmono x y hxy)

/-- `G` equipped with an ambient size parameter. -/
def WithSize (G : Type → Type v) (α : Type) : Type v := ReaderT Nat G α

/-- Close over the size parameter, recovering a plain generator. -/
def WithSize.run (g : WithSize G α) (n : Nat) : G α := ReaderT.run g n

/-- Run a size-agnostic generator at any size. -/
def WithSize.lift (g : G α) : WithSize G α := fun _ => g

instance instMonadWithSize [Monad G] : Monad (WithSize G) := inferInstanceAs (Monad (ReaderT Nat G))

instance instMonadLiftWithSize : MonadLift G (WithSize G) := ⟨WithSize.lift⟩

instance instRandomChoiceWithSize [RandomChoice G] : RandomChoice (WithSize G) where
  choose lo hi h := fun _ => RandomChoice.choose lo hi h

instance instGenWithSize [Gen G] : Gen (WithSize G) where
  instInhabited := fun α => inferInstanceAs (Inhabited (Nat → G α))
  instMonad := instMonadWithSize
  instRandomChoice := instRandomChoiceWithSize
  instCCPO := fun α => inferInstanceAs (CCPO (Nat → G α))
  instMonoBind := inferInstanceAs (MonoBind (ReaderT Nat G))

instance instSizedWithSize [Monad G] : Sized (WithSize G) where
  sized f := fun n => f n n
  resize n g := fun _ => g n

instance instMonoSizedWithSize [Gen G] : MonoSized (WithSize G) where
  sized_mono h := fun n => h n n
  resize_mono h := fun _ => h _

instance instSizedOptionT [Sized G] : Sized (OptionT G) where
  sized f := OptionT.mk (Sized.sized fun n => (f n).run)
  resize n g := OptionT.mk (Sized.resize n g.run)

instance instMonoSizedOptionT [Sized G] [∀ α, PartialOrder (G α)] [MonoSized G] :
    MonoSized (OptionT G) where
  sized_mono h := MonoSized.sized_mono (g := G) h
  resize_mono h := MonoSized.resize_mono (g := G) h

instance instFailWithSize [Fail G] : Fail (WithSize G) := ⟨fun _ => Fail.fail⟩

/-! ## Size as a budget

`bind` at `WithSize` shares the size: both sides read the same `n`, which is right when size is a
bound or a control (QuickCheck's bias, SmallCheck's depth). Where size is a budget to be spent —
FEAT's exact sizes — it is split instead. `splitBind` and `done` are that second monad structure on
the same carrier, and `pay` charges for a step; all three are derived from `sized`, `resize` and
`choose`, so a FEAT-style generator is an ordinary sized generator, and its tiers are its sizes run
as an enumeration.

`done` matters: `pure` holds at every size, so `splitBind (pure a) f` is `f a` at every size up to
`n`, with repeats, and a tier would count what costs *at most* `n`. `done a` is at size `0` only,
and `splitBind (done a) f` is `f a`. -/

namespace Sized

variable {G : Type → Type} {α β : Type}

/-- Charge one: what costs `n` now costs `n + 1`, and nothing is free. -/
def pay [Monad G] [Sized G] [Fail G] (x : G α) : G α :=
  Sized.sized fun n => if n = 0 then Fail.fail else Sized.resize (n - 1) x

/-- A value that costs nothing: only at size `0`. The unit of `splitBind`. -/
def done [Monad G] [Sized G] [Fail G] (a : α) : G α :=
  Sized.sized fun n => if n = 0 then pure a else Fail.fail

open RandomChoice in
/-- Split the size between `x` and its continuation, every way: `x` at `k`, the rest at `n - k`.

The split is a `choose`, so when sampling it is a uniform draw of `k`, and a chain of them is a
stick broken again and again: the first part gets half the size on average, the next a quarter,
and so on. And it does not associate: nesting the other way gives the parts a different
distribution. For parts that should be treated alike, use `splitInto`. -/
def splitBind [Monad G] [RandomChoice G] [Sized G] (x : G α) (f : α → G β) : G β :=
  Sized.sized fun n => do
    let k := (← choose 0 n (Nat.zero_le _)).down.val
    Sized.resize (n - k) (f (← Sized.resize k x))

/-- How many ways `n` splits into `m` parts, each at least `0`: `C(n + m - 1, m - 1)`. -/
def splits (n m : Nat) : Nat :=
  match m with
  | 0 => if n = 0 then 1 else 0
  | m + 1 => (List.range (n + 1)).foldl (fun s j => s + splits (n - j) m) 0

/-- The first share of the `i`th split, and the index of the rest among the splits that follow it:
skip past the splits whose first share is `j`, there being `count (n - j)` of them. -/
def firstShare (n : Nat) (count : Nat → Nat) : Nat → Nat → Nat → Nat × Nat
  | 0, j, i => (j, i)
  | fuel + 1, j, i =>
    let c := count (n - j)
    if i < c then (j, i) else firstShare n count fuel (j + 1) (i - c)

/-- The `i`th split of `n` into `m` parts, in the order that puts smaller first shares first. -/
def unsplit (n : Nat) : Nat → Nat → List Nat
  | 0, _ => []
  | 1, _ => [n]
  | m + 2, i =>
    let (j, i') := firstShare n (fun r => splits r (m + 1)) (n + 1) 0 i
    j :: unsplit (n - j) (m + 1) i'

open RandomChoice in
/-- Split the size among parts, each at least its floor, every split equally likely: one share per
part, the shares adding up to the size. `fail` when the floors add up to more than the size.
Unlike a chain of `splitBind`s, no part is favoured; each part is then run at its share, with
`resize`. -/
def splitInto [Monad G] [RandomChoice G] [Sized G] [Fail G] (floors : List Nat) : G (List Nat) :=
  Sized.sized fun n =>
    let free := n - floors.sum
    if floors.sum ≤ n ∧ floors ≠ [] then do
      let c := splits free floors.length
      let i := (← choose 0 (c - 1) (Nat.zero_le _)).down.val
      pure ((unsplit free floors.length i).zipWith (· + ·) floors)
    else Fail.fail

@[partial_fixpoint_monotone]
theorem monotone_pay [Gen G] [Sized G] [MonoSized G] [Fail G] {γ : Sort w} [PartialOrder γ]
    (f : γ → G α) (hf : monotone f) : monotone fun c => pay (f c) := by
  intro c₁ c₂ h
  show pay (f c₁) ⊑ pay (f c₂)
  apply MonoSized.sized_mono
  intro n
  split
  · exact PartialOrder.rel_refl
  · exact MonoSized.resize_mono (hf _ _ h)

@[partial_fixpoint_monotone]
theorem monotone_splitBind [Gen G] [Sized G] [MonoSized G] {γ : Sort w} [PartialOrder γ]
    (x : γ → G α) (f : γ → α → G β) (hx : monotone x) (hf : monotone f) :
    monotone fun c => splitBind (x c) (f c) := by
  intro c₁ c₂ h
  show splitBind (x c₁) (f c₁) ⊑ splitBind (x c₂) (f c₂)
  apply MonoSized.sized_mono
  intro n
  apply MonoBind.bind_mono_right
  intro k
  exact PartialOrder.rel_trans (MonoBind.bind_mono_left (MonoSized.resize_mono (hx _ _ h)))
    (MonoBind.bind_mono_right fun a => MonoSized.resize_mono (hf _ _ h a))

end Sized
