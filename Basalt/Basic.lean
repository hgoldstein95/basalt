/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt.RandomChoice
import Basalt.Gen
import Basalt.OptionT
import Basalt.IO
import Basalt.PlausibleGen
import Basalt.SPMF
import Basalt.SPMF.Cost
import Basalt.SPMF.Failure
import Basalt.Tactics
import Basalt.Laws
import Basalt.Combinators
import Basalt.Tuning
import Basalt.Tuning.Attr
import Basalt.GenStats
import Basalt.GenStats.Command

/-!
# Basalt

For informaiton about how Basalt's generator representation relates to QuickCheck, QuickChick, and
free generators, see `docs/representation.md`.
-/
