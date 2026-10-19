/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Michael Hicks, Harrison Goldstein
-/
module

public import Basalt.IO
public import Basalt.PBT.Driver

/-!
# Testing a Property at `IO`
-/

public section

namespace Basalt.PBT

/-- Test `T` at the `IO` interpretation, where choices come from SplitMix via `ioGen`. -/
def ioCampaign (T : Property) (runs : Nat) (maxDiscardRatio : Nat := 10) : IO Unit :=
  campaign "IO" (runProp (T IO)) runs maxDiscardRatio

/-- Uniform random testing at `IO`. -/
@[basalt_backend]
def ioBackend : Backend where
  name := "io"
  campaign T argv := ioCampaign T (runsOf argv) (discardRatioOf argv)

end Basalt.PBT
