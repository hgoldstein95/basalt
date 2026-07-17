/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt.Gen

open Lean.Order RandomChoice

/-!
# Generic Lifting into `OptionT`

An explicit `Option` layer over *any* generator monad `G` is itself a generator monad.
-/

instance instRandomChoiceOptionT {G : Type → Type} [Monad G] [RandomChoice G] :
    RandomChoice (OptionT G) where
  choose lo hi h := OptionT.lift (RandomChoice.choose lo hi h)

instance instGenOptionT {G : Type → Type} [Gen G] : Gen (OptionT G) where
  instInhabited := fun _ => inferInstance
  instMonad := inferInstance
  instRandomChoice := instRandomChoiceOptionT
  instCCPO := fun _ => inferInstance
  instMonoBind := inferInstanceAs (MonoBind (OptionT G))
