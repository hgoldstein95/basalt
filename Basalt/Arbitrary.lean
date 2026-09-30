/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Segev Elazar Mittelman
-/
import Basalt.BacktrackGen
import Basalt.Combinators

/-!
# Generator Lookup Classes

Classes that find a generator by the type, or the type and property, it generates for — polymorphic in
the `Gen`, so what they resolve to both runs and is reasoned about — with instances for the base types.
-/

open Lean.Order RandomChoice

namespace Basalt

/-- An unconstrained generator for `α`.

Under `Basalt` rather than at the root: a root `Arbitrary` is ambiguous with `Plausible.Arbitrary` in any
file that opens `Plausible`, which broke `deriving instance Arbitrary` in downstream files. -/
class Arbitrary (α : Type) where
  arbitrary : ∀ {G : Type → Type} [Gen G], G α

/-- An unconstrained generator for `α` whose fuel bounds its recursion depth. -/
class ArbitraryFueled (α : Type) where
  arbitraryFueled : ∀ {G : Type → Type} [Gen G], Nat → G α

/-- An unfueled generator ignores the fuel. Low priority, so an instance that uses it wins. There is no
converse: an unfueled generator from a fueled one would have to choose a fuel. -/
instance (priority := low) [Arbitrary α] : ArbitraryFueled α where
  arbitraryFueled _ := Arbitrary.arbitrary

end Basalt

/-- A generator for `α` whose outputs satisfy `P`, and that always succeeds. -/
class GenFor (α : Type) (P : α → Prop) where
  gen : ∀ {G : Type → Type} [Gen G], G α

/-- A backtracking generator for `α` whose successful outputs satisfy `P`, taking a fuel. -/
class BacktrackGenFor (α : Type) (P : α → Prop) where
  gen : ∀ {G : Type → Type} [Gen G], Nat → BacktrackGen G α

namespace Basalt

instance [Arbitrary α] : GenFor α (fun _ => True) where
  gen := Arbitrary.arbitrary

/-! ## Base instances -/

/-- A geometric `Nat`: stop with probability `1/2` at each step. -/
protected def Nat.arbitraryGen [Gen G] : G Nat :=
  oneOf [fun () => pure 0, fun () => do let n ← Nat.arbitraryGen; pure (n + 1)]
partial_fixpoint

instance : Arbitrary Nat where
  arbitrary := Nat.arbitraryGen

instance : Arbitrary Bool where
  arbitrary := do pure ((← chooseNat 0 1) == 0)

instance : Arbitrary Unit where
  arbitrary := pure ()

instance : Arbitrary (Fin (n + 1)) where
  arbitrary := do
    let m ← choose 0 n (Nat.zero_le n)
    pure ⟨m.down.val, Nat.lt_succ_of_le m.down.property.2⟩

instance [Arbitrary α] : Arbitrary (Option α) where
  arbitrary := oneOf [fun () => pure none, fun () => some <$> Arbitrary.arbitrary]

instance [Arbitrary α] [Arbitrary β] : Arbitrary (α × β) where
  arbitrary := do
    let a ← Arbitrary.arbitrary
    let b ← Arbitrary.arbitrary
    pure (a, b)

instance [Arbitrary α] [Arbitrary β] : Arbitrary (α ⊕ β) where
  arbitrary := oneOf [fun () => Sum.inl <$> Arbitrary.arbitrary,
    fun () => Sum.inr <$> Arbitrary.arbitrary]

instance : Arbitrary Int where
  arbitrary := oneOf [fun () => Int.ofNat <$> Arbitrary.arbitrary,
    fun () => Int.negSucc <$> Arbitrary.arbitrary]

/-- Printable ASCII, `' '` through `'~'`: the full `Char` range is mostly unassigned code points and
surrogates, which make useless test data. -/
instance : Arbitrary Char where
  arbitrary := do pure (Char.ofNat (← chooseNat 32 126))

/-- A geometric-length list. -/
protected def List.arbitraryGen [Gen G] [Arbitrary α] : G (List α) :=
  oneOf [fun () => pure [], fun () => do
    let x ← Arbitrary.arbitrary
    let xs ← List.arbitraryGen
    pure (x :: xs)]
partial_fixpoint

instance [Arbitrary α] : Arbitrary (List α) where
  arbitrary := List.arbitraryGen

instance : Arbitrary String where
  arbitrary := do pure (String.ofList (← Arbitrary.arbitrary (α := List Char)))

/-! ## Fueled instances for compound types

Each exists because the `Arbitrary` instance for the compound type needs `Arbitrary` components, and a
type that only has `ArbitraryFueled` would otherwise have no generator for, say, its lists. Fuel passes
to each component unchanged: components are siblings, not nested. -/

/-- A list whose length is bounded by the fuel. Nil and cons are weighted `1 : n+1`, so the expected
length grows with the fuel; a fair coin would give mean length 1 at every fuel. -/
protected def List.arbitraryFueledGen [Gen G] [ArbitraryFueled α] : Nat → G (List α)
  | 0 => pure []
  | n + 1 =>
    frequency [(1, fun () => pure []), (n + 1, fun () => do
      let x ← ArbitraryFueled.arbitraryFueled (α := α) (n + 1)
      let xs ← List.arbitraryFueledGen n
      pure (x :: xs))] (by simp; omega)

instance [ArbitraryFueled α] : ArbitraryFueled (List α) where
  arbitraryFueled := List.arbitraryFueledGen

instance [ArbitraryFueled α] [ArbitraryFueled β] : ArbitraryFueled (α × β) where
  arbitraryFueled n := do
    let a ← ArbitraryFueled.arbitraryFueled (α := α) n
    let b ← ArbitraryFueled.arbitraryFueled (α := β) n
    pure (a, b)

instance [ArbitraryFueled α] : ArbitraryFueled (Option α) where
  arbitraryFueled n :=
    oneOf [fun () => pure none, fun () => some <$> ArbitraryFueled.arbitraryFueled (α := α) n]

instance [ArbitraryFueled α] [ArbitraryFueled β] : ArbitraryFueled (α ⊕ β) where
  arbitraryFueled n := oneOf [fun () => Sum.inl <$> ArbitraryFueled.arbitraryFueled (α := α) n,
    fun () => Sum.inr <$> ArbitraryFueled.arbitraryFueled (α := β) n]

end Basalt
