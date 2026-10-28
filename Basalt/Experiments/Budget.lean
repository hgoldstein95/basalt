/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
module

public import Basalt.Fail
public import Basalt.Gen

/-!
# Experiment: Size as a Budget That Is Spent

A third reading of size, next to `WithSize`'s shared bound and `Sized.splitBind`'s split decided up
front. Here the size is a counter the generator spends: each constructor `spend`s one, a part takes
what its own construction uses, and whatever it leaves goes on to the next part. Nothing is guessed
ahead, so no part is ever handed a size it cannot fill.

* `Budget.exact x n` keeps the runs that spend exactly `n`: as an enumeration, the trees of size `n`;
  as a sampler, rejection. Where each constructor is decided by one fair choice, every tree of a size
  has the same probability, so the accepted samples are uniform over the trees of that size, with
  no counting. A run stops as soon as it would overspend.
* `Budget.atMost x n` keeps every run that fits.

`Budget G` is `StateT Nat G`, and is a generator interpretation whenever `G` is.
-/

@[expose] public section

open Lean.Order

/-- A generator monad with a budget its constructors spend. -/
class Spend (G : Type → Type) where
  /-- Spend one; `fail` if nothing is left. -/
  spend : G PUnit

/-- `G`, with a budget passed from each step to the next. -/
def Budget (G : Type → Type) (α : Type) : Type := StateT Nat G α

namespace Budget

variable {G : Type → Type} {α : Type}

instance [Monad G] : Monad (Budget G) := inferInstanceAs (Monad (StateT Nat G))

instance [Monad G] [RandomChoice G] : RandomChoice (Budget G) where
  choose lo hi h := StateT.lift (RandomChoice.choose lo hi h)

instance [Monad G] [Fail G] : Fail (Budget G) := ⟨StateT.lift Fail.fail⟩

instance [Monad G] [Fail G] : Spend (Budget G) :=
  ⟨fun b => if b = 0 then Fail.fail else pure (⟨⟩, b - 1)⟩

instance [Gen G] : Inhabited (Budget G α) := ⟨fun _ => default⟩

instance instCCPO [Gen G] : CCPO (Budget G α) := inferInstanceAs (CCPO (StateT Nat G α))

instance [Gen G] : MonoBind (Budget G) := inferInstanceAs (MonoBind (StateT Nat G))

/-- The runs that spend exactly `n`. -/
def exact [Monad G] [Fail G] (x : Budget G α) (n : Nat) : G α := do
  let (a, left) ← StateT.run (m := G) x n
  if left = 0 then pure a else Fail.fail

/-- The runs that spend at most `n`. -/
def atMost [Monad G] (x : Budget G α) (n : Nat) : G α :=
  Prod.fst <$> StateT.run (m := G) x n

end Budget
