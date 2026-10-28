/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein, Segev Elazar-Mittelman
-/
module

public import Basalt.Enum.Finite
public import Basalt.Enum.Weighted
public import Basalt.Enum.Graded
public import Basalt.Enum.Memo
public import Basalt.Enum.Tabled
public import Basalt.Enum.Local
public import Basalt.Enum.Laws
public import Basalt.Enum.WeightLaws
public import Basalt.Enum.CostLaws
public import Basalt.Enum.FailLaws
public import Basalt.Enum.BacktrackLaws
public import Basalt.Enum.BacktrackCostLaws
public import Basalt.Enum.WeightedBacktrack
public import Basalt.Enum.BacktrackWeightLaws
public import Basalt.Enum.MemoLaws
public import Basalt.Enum.TabledLaws
public import Basalt.Sized
public import Basalt.Backtrack
public import Basalt.Pick

/-!
# Enumeration

An enumerator is an interpretation of a generator: the generator is written once, over `Gen`, and
read as everything it can produce rather than one random value.

* `Basalt.Enum.Finite`: every value, one entry per path, with arithmetic counts.
* `Basalt.Enum.Weighted`: the same, with each path's probability — the exact distribution.
* `Basalt.Enum.Graded`: bucketed by size (`WithSize Finite`) or by the number of choices made
  (`CostGraded`), so that a generator with an infinite support is enumerable bucket by
  bucket.
* `Basalt.Enum.Memo`: each recursive call computed once.
* `Basalt.Enum.Tabled`: the support of a recursion with no measure, finite whenever it is.
* `Basalt.Enum.Local`: enumerating a sub-generator inside a generator.

Failure is `Fail.fail`, read as `∅` here (`Basalt.Fail`); weighted backtracking is
`Backtrack.backtrack`, and a weighted draw without retry `Pick.pick`, both read as the union of their
branches (`Basalt.Backtrack`, `Basalt.Pick`), and `backtrack` at `WFinite` as each branch weighted by
the probability that the search reaches it (`Basalt.Enum.WeightedBacktrack`); FEAT's exact sizing is
`Sized.pay`, `Sized.splitBind` and `Sized.done` (`Basalt.Sized`).
-/
