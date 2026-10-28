/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Segev Elazar-Mittelman
-/
module

public import Basalt.Enum
meta import Basalt.Enum
public import Basalt.Experiments.PathTabling
meta import Basalt.Experiments.PathTabling
public import BasaltExamples.Enum.Compositions
meta import BasaltExamples.Enum.Compositions
public import BasaltExamples.Enum.BST
meta import BasaltExamples.Enum.BST
public import BasaltExamples.Enum.STLC
meta import BasaltExamples.Enum.STLC
public import BasaltExamples.STLC.TypeCheck
meta import BasaltExamples.STLC.TypeCheck
public import BasaltExamples.Enum.Sized
meta import BasaltExamples.Enum.Sized
public import BasaltExamples.Enum.Cost
meta import BasaltExamples.Enum.Cost
public import BasaltExamples.Enum.Local
meta import BasaltExamples.Enum.Local
public import BasaltExamples.Enum.Tabled
meta import BasaltExamples.Enum.Tabled
public import BasaltExamples.Enum.Outcome
meta import BasaltExamples.Enum.Outcome

/-!
# Enumeration, checked

Each enumeration against something computed another way: a closed form, a brute force, or the same
generator closed another way. All small enough to run on every build.
-/

@[expose] public section

open Basalt

/-! ## Backtracking -/

namespace Backtracking

/-- A choice among rules: one weighted branch per rule, `fail` where a rule does not apply. -/
def rules [Monad G] [RandomChoice G] [Fail G] [Backtrack G] (n : Nat) : G Nat :=
  Backtrack.backtrack
    [(3, fun _ => pickFrom [1, 2]), (0, fun _ => pure 9), (1, fun _ => if n = 0 then Fail.fail else pure 3)]

-- The union: each branch's values once, the weight-0 branch never.
#guard (rules (G := Basalt.Finite) 1).toList? == some [1, 2, 3]
#guard (rules (G := Basalt.Finite) 0).toList? == some [1, 2]

-- The search, enumerated: an entry per unit of weight.
#guard (rules (G := OptionT Basalt.Finite) 1).run.toList? ==
  some [some 1, some 2, some 1, some 2, some 1, some 2, some 3]

example (n : Nat) : EnumeratesSome (rules (G := Basalt.Finite) n) (rules (G := OptionT SPMF) n) :=
  EnumeratesSome.backtrack (.cons (EnumeratesSome.pickFrom _) (.cons (EnumeratesSome.pure _)
    (.cons (genRel_enumeratesSome.ite (fun _ => EnumeratesSome.fail) fun _ => EnumeratesSome.pure _)
      .nil)))

/-- The same at a size: each branch reads it. -/
def sizedRules [Monad G] [RandomChoice G] [Fail G] [Sized G] [Backtrack G] : G Nat :=
  Sized.sized fun n =>
    Backtrack.backtrack [(1, fun _ => pure n), (1, fun _ => if n = 0 then Fail.fail else pure (n + 10))]

#guard ((sizedRules (G := WithSize Basalt.Finite)).run 2).toList? == some [2, 12]
#guard ((sizedRules (G := WithSize Basalt.Finite)).run 0).toList? == some [0]

/-- The draw without retry: at an enumeration the same union as `backtrack`, where the draw itself,
enumerated, repeats each branch once per unit of weight. -/
def drawn [Monad G] [RandomChoice G] [Fail G] [Pick G] : G Nat :=
  Pick.pick [(3, fun _ => pickFrom [1, 2]), (0, fun _ => pure 9), (1, fun _ => pure 3)]

#guard (drawn (G := Basalt.Finite)).toList? == some [1, 2, 3]
#guard (drawn (G := OptionT Basalt.Finite)).run.toList? ==
  some [some 1, some 2, some 1, some 2, some 1, some 2, some 3]

-- Graded by cost, tier `n + 1` is each branch's tier `n`: `3` costs the pick alone, `pickFrom`'s
-- values one draw more.
#guard (List.range 4).map (rules (G := CostGraded Basalt.Finite) 1).tier? ==
  [some [], some [3], some [1, 2], some []]

/-- Unbounded recursion through `backtrack`: each bit costs a pick and a draw. -/
def bits [Gen G] [Fail G] [Backtrack G] [MonoBacktrack G] : G (List Bool) :=
  Backtrack.backtrack
    [(1, fun _ => pure []), (1, fun _ => do return (← pickFrom [true, false]) :: (← bits))]
partial_fixpoint

#guard (List.range 6).map (bits (G := CostGraded Basalt.Finite)).card? ==
  [some 0, some 1, some 0, some 2, some 0, some 4]
#guard (bits (G := CostGraded Basalt.Finite)).tier? 3 == some [[true], [false]]

#guard (List.range 4).map (drawn (G := CostGraded Basalt.Finite)).tier? ==
  [some [], some [3], some [1, 2], some []]

-- The exact distribution: each branch's entries weighted by the probability of reaching it.
#guard WFinite.entries? (rules (G := WFinite) 1) == some [(1, 3/8), (2, 3/8), (3, 1/4)]

/-- Three rules, each of which can fail, one always. -/
def failing [Monad G] [RandomChoice G] [Fail G] [Backtrack G] : G Nat :=
  Backtrack.backtrack [
    (2, fun _ => do
      let n := (← RandomChoice.choose 0 2 (by omega)).down.val
      if n = 0 then Fail.fail else pure n),
    (1, fun _ => Fail.fail),
    (3, fun _ => do
      if (← RandomChoice.choose 0 1 (by omega)).down.val = 0 then Fail.fail else pure 5)]

def byValue (l : List (Nat × Rat)) : List (Nat × Rat) := l.mergeSort fun a b => a.1 ≤ b.1

open Basalt.Examples.Enum.Local in
-- The search's distribution, and its probability of failing as what the weights leave of `1`.
#guard byValue (distOf (failing (G := WFinite))) ==
  byValue (failAndDist (failing (G := OptionT WFinite))).2
open Basalt.Examples.Enum.Local in
#guard 1 - ((WFinite.entries? (failing (G := WFinite))).getD []).foldl (fun s (_, w) => s + w) 0 ==
  (failAndDist (failing (G := OptionT WFinite))).1

-- An entry per value, where the search has one per order of retries.
#guard (WFinite.entries? (failing (G := WFinite))).map List.length == some 3
#guard (WFinite.entries? (failing (G := OptionT WFinite)).run).map List.length == some 104

/-- Ten rules, each failing half the time. -/
def coins [Monad G] [RandomChoice G] [Fail G] [Backtrack G] : G Nat :=
  Backtrack.backtrack ((List.range 10).map fun k => (k + 1, fun _ => do
    if (← RandomChoice.choose 0 1 (by omega)).down.val = 0 then Fail.fail else pure k))

-- The search fails only if every rule does.
#guard ((WFinite.entries? (coins (G := WFinite))).getD []).foldl (fun s (_, w) => s + w) 0 ==
  1 - 1 / 2 ^ 10

-- `pick` at `WFinite`: each branch weighted by its share, failure the weight left over.
#guard WFinite.entries? (drawn (G := WFinite)) == some [(1, 3/8), (2, 3/8), (3, 1/4)]

/-- `failing`'s rules, drawn once: no retry, so it fails more often. -/
def failingOnce [Monad G] [RandomChoice G] [Fail G] [Pick G] : G Nat :=
  Pick.pick [
    (2, fun _ => do
      let n := (← RandomChoice.choose 0 2 (by omega)).down.val
      if n = 0 then Fail.fail else pure n),
    (1, fun _ => Fail.fail),
    (3, fun _ => do
      if (← RandomChoice.choose 0 1 (by omega)).down.val = 0 then Fail.fail else pure 5)]

open Basalt.Examples.Enum.Local in
#guard byValue (distOf (failingOnce (G := WFinite))) ==
  byValue (failAndDist (failingOnce (G := OptionT WFinite))).2
open Basalt.Examples.Enum.Local in
#guard 1 - ((WFinite.entries? (failingOnce (G := WFinite))).getD []).foldl (fun s (_, w) => s + w) 0 ==
  (failAndDist (failingOnce (G := OptionT WFinite))).1

/-! ### Failures that say why -/

/-- A rule that refutes and a rule that could not decide. -/
def undecided [Monad G] [RandomChoice G] [Fail G] [FailWith Unit G] [Backtrack G] : G Nat :=
  Backtrack.backtrack [(1, fun _ => Fail.fail), (1, fun _ => FailWith.failWith ())]

/-- The same, with a rule that succeeds. -/
def decided [Monad G] [RandomChoice G] [Fail G] [FailWith Unit G] [Backtrack G] : G Nat :=
  Backtrack.backtrack
    [(1, fun _ => Fail.fail), (1, fun _ => FailWith.failWith ()), (1, fun _ => pure 7)]

-- The search ends with the label, never refuted: some branch could not decide.
#guard ((undecided (G := ExceptT Unit (OptionT Basalt.Finite))).run.run.toList?).map
  (·.all (· == some (Except.error ()))) == some true
-- With a rule that succeeds, the search retries past the label and always succeeds; the union
-- still lists the label, which says only that some branch could not decide.
#guard ((decided (G := ExceptT Unit (OptionT Basalt.Finite))).run.run.toList?).map
  (·.all (· == some (Except.ok 7))) == some true
#guard (decided (G := ExceptT Unit Basalt.Finite)).run.toList? == some [Except.error (), Except.ok 7]

end Backtracking

/-! ## Memoized tiers -/

namespace Compositions

open Basalt.Examples.Enum.Compositions

/-- info: some [[1, 1, 1, 1], [1, 1, 2], [1, 2, 1], [2, 1, 1], [2, 2]] -/
#guard_msgs in
#eval ((SizedStep.fix (compositions (G := Basalt.Finite))) 4).toList?

-- Fibonacci counts, from the table, and the same from recursing.
#guard (SizedStep.tiers compositions 9).toList.map Basalt.Finite.card? ==
  [some 1, some 1, some 2, some 3, some 5, some 8, some 13, some 21, some 34, some 55]
#guard (List.range 10).map (fun n => (SizedStep.fix (compositions (G := Basalt.Finite)) n).card?) ==
  (SizedStep.tiers compositions 9).toList.map Basalt.Finite.card?

end Compositions

namespace BSTs

open BST

def counts (ts : List (Basalt.Finite α)) : List Nat := ts.map (·.card?.getD 0)

-- The memoized exact-size tiers are `C(w, n) · Catalan(n)`.
#guard ([1, 4, 8, 12] : List Nat).all fun w =>
  counts (enumBSTs 0 ((w : Int) - 1)) == (List.range (w + 1)).map (expectedCount w)

-- So is the untouched `genBST` at `Finite`, bucketed by size.
#guard ([1, 4, 6] : List Nat).all fun w => bucketBySize (allBSTs 0 ((w : Int) - 1)) w ==
  (List.range (w + 1)).map (expectedCount w)

end BSTs

/-! ## Well-typed STLC terms, against a brute force -/

namespace STLCTerms

open STLC

def tys : List Ty := [.Bool, .Fun .Bool .Bool, .Fun (.Fun .Bool .Bool) .Bool]

/-- Tier `n` has as many terms as the brute force finds, each well-typed at size `n`, none twice. -/
def agrees (τ : Ty) (n : Nat) : Bool :=
  let tiers := enumClosed τ n
  (List.range (n + 1)).all fun k =>
    let es : List Term := ((tiers.getD k .empty).toList?).getD []
    es.length == ((rawTerms 0 k).filter fun e => typeCheck [] e == some τ).length &&
      es.all (fun e => typeCheck [] e == some τ && e.size == k) &&
      es.eraseDups.length == es.length

#guard tys.all (agrees · 7)

-- Memoizing changes nothing but the work.
#guard (enumClosed .Bool 11).map (·.card?) == (enumClosedNaive .Bool 11).map (·.card?)

end STLCTerms

/-! ## Exact sizes, and buckets that bias -/

namespace Sizes

open Basalt.Examples.Enum.Sizes

def tierCards (g : WithSize Basalt.Finite α) (n : Nat) : List (Option Nat) :=
  (List.range (n + 1)).map fun k => (g.run k).card?

-- A `pay` per constructor: tier `2k + 1` is the `Catalan k` trees with `k` nodes.
#guard tierCards treeSized 9 ==
  [some 0, some 1, some 0, some 1, some 0, some 2, some 0, some 5, some 0, some 14]

-- A part of size `k` pays `k`: the compositions of `n` into `1`s and `2`s.
#guard tierCards compSized 9 ==
  [some 1, some 1, some 2, some 3, some 5, some 8, some 13, some 21, some 34, some 55]

-- Three children: a chain of `splitBind`s, `splitInto`, and a spent budget enumerate the same trees.
#guard tierCards tree3Chain 10 == tierCards (tree3Even 1) 10
#guard [1, 4, 7, 10].map (fun n => (Budget.exact (tree3Spend (G := Budget Basalt.Finite)) n).card?) ==
  [some 1, some 1, some 3, some 12]

-- As samplers: the chain favours the first child; `splitInto` treats them alike.
#guard childMeans tree3Chain 7 == [5/2, 7/4, 7/4]
#guard childMeans (tree3Even 0) 7 == [2, 2, 2]

-- A floor of `1` rules out shares no tree can fill.
#guard failsAt (tree3Even 1) 7 < failsAt (tree3Even 0) 7

-- Spending a budget, the accepted trees of size `n` are uniform: at `10`, each of the `12` has `1/12`.
def spentAt (n : Nat) : List (T3 × Rat) :=
  WFinite.dist ((WFinite.entries? (Budget.exact (tree3Spend (G := Budget WFinite)) n)).getD [])
#guard (spentAt 10).map (·.2) == List.replicate 12 (3/256 / 12)

-- At size 2 a node has probability `2/3`, and each child is a node half the time.
#guard qtreeBucket 1 == [(0, 1/2), (1, 1/2)]
#guard qtreeBucket 2 == [(0, 1/3), (1, 1/6), (2, 1/3), (3, 1/6)]

end Sizes

/-! ## Graded by cost -/

namespace Cost

open Basalt.Examples.Enum.Cost

def cards (g : CostGraded Basalt.Finite α) (n : Nat) : List (Option Nat) := (List.range (n + 1)).map g.card?

#guard cards (genType (G := CostGraded Basalt.Finite)) 9 ==
  [some 0, some 1, some 0, some 1, some 0, some 2, some 0, some 5, some 0, some 14]
#guard ((genType (G := CostGraded Basalt.Finite)).tier? 7).getD [] |>.all (·.size == 7)
#guard cards (geomList (G := CostGraded Basalt.Finite)) 7 ==
  [some 0, some 1, some 0, some 2, some 0, some 4, some 0, some 8]
#guard cards (loop (G := CostGraded Basalt.Finite)) 5 == [some 0, some 1, some 1, some 1, some 1, some 1]

-- Basalt's own STLC `genType`, unchanged.
#guard cards (STLC.genType (G := CostGraded Basalt.Finite)) 9 ==
  [some 0, some 1, some 0, some 1, some 0, some 2, some 0, some 5, some 0, some 14]

end Cost

/-! ## Local backtracking -/

namespace Local

open Basalt.Examples.Enum.Local

-- Cost grading splits without weighting the split: `digits` has all its probability at cost 2, and
-- `geomList` has `31/32` of it within 9 choices (lengths up to 4).
def mass (es : Option (List (α × Rat))) : Rat := (es.getD []).foldl (fun s (_, w) => s + w) 0
#guard mass (CostGraded.upTo? (digits (CostGraded WFinite)) 2) == 1
#guard mass (CostGraded.upTo? (geomList (G := CostGraded WFinite)) 9) == 31/32

#guard distOf (exhaust (G := WFinite) 2 digits (fun (x, y) => x + y == 17)) ==
  [(.found (8, 9), 1/2), (.found (9, 8), 1/2)]
#guard distOf (exhaust (G := WFinite) 2 digits (fun (x, y) => x + y == 19)) == [(.refuted, 1)]
#guard distOf (exhaust (G := WFinite) 1 digits (fun (x, y) => x + y == 19)) == [(.exhausted, 1)]

-- Given the condition, length `k` has probability proportional to `4^-k`.
#guard distOf (exhaust (G := WFinite) 9 (fun _ _ => geomList) fun l => !l.isEmpty && l.all id) ==
  [(.found [true], 64/85), (.found [true, true], 16/85), (.found [true, true, true], 4/85),
   (.found [true, true, true, true], 1/85)]
#guard distOf (exhaust (G := WFinite) 9 (fun _ _ => geomList) fun l => l.length == 100) ==
  [(.exhausted, 1)]

-- The Specimen-shaped `genHasType`: the derived premise check fails when it draws `0`; `exhaust`
-- never fails; given success, they agree, `isPos n` for each `n ∈ 1..100` with probability `1/100`.
#guard failure? (genHasType (G := WFinite) isPosDerived .bool 0) == 1/101
#guard failure? (genHasType (G := WFinite) isPosExhaust .bool 0) == 0
#guard failure? (genHasType (G := WFinite) isPosDerived .bool 2) == 1/101
#guard failure? (genHasType (G := WFinite) isPosExhaust .bool 2) == 0
#guard given (genHasType (G := WFinite) isPosDerived .bool 2) ==
  (failAndDist (genHasType (G := WFinite) isPosExhaust .bool 2)).2
#guard (failAndDist (genHasType (G := WFinite) isPosExhaust .bool 2)).2 ==
  (List.range 100).map fun i => (.isPos (i + 1), 1/100)

end Local

/-! ## Supports of recursion with no measure -/

namespace Tabled

open Basalt.Examples.Enum.Tabled

def supp [BEq κ] [Hashable κ] [BEq α] (step : PolyStep κ α) (fuel : Nat) (ks : List κ) :
    List Nat × Bool :=
  let r := step.supports fuel ks
  (r.values.map List.length, r.complete)

#guard (PolyStep.supports (fun _ _ _ _ => loopStep) 10 [()]).values == [[0]]
-- The hypothesis `loop_succeeds_iff` takes: the run finishes with `[0]` at the one key.
#guard (PolyStep.supports loopPoly 10 [()]).complete &&
  (PolyStep.supports loopPoly 10 [()]).table[()]? == some [0]
#guard (PolyStep.supports (fun _ _ _ _ => loopStep) 10 [()]).complete
#guard (PolyStep.supports (fun _ _ _ _ => flipStep) 10 [()]).values == [[true, false]]
#guard (PolyStep.supports (fun _ _ _ _ => flipStep) 10 [()]).complete
#guard supp (fun _ _ _ _ => bstStep) 10 [(0, 2), (0, 3)] == ([15, 51], true)
#guard (supp (fun _ _ _ _ => listStep) 10 [()]).2 == false
#guard (supp (fun _ _ _ _ => growStep) 10 [0]).2 == false
#guard supp (fun _ _ _ _ => mixStep) 20 [2] == ([1], true)
#guard (supp (fun _ _ _ _ => mixStep) 20 [0, 1, 2]).2 == false

-- Counting paths instead (`Basalt.Experiments.PathTabling`): `undef` where they are infinite.
def tabled [BEq κ] [Hashable κ] (step : PolyStep κ α) (fuel : Nat) (ks : List κ) :
    List (Option Nat) × Bool × Array κ :=
  let r := step.run fuel ks
  (r.values.map (·.card?), r.complete, r.cyclic)

#guard tabled (fun _ _ _ _ => loopStep) 10 [()] == ([none], true, #[()])
#guard tabled (fun _ _ _ _ => listStep) 10 [()] == ([none], true, #[()])
#guard tabled (fun _ _ _ _ => bstStep) 10 [(0, 2), (0, 3)] == ([some 15, some 51], true, #[])
#guard tabled (fun _ _ _ _ => mixStep) 10 [0, 1, 2] == ([none, none, some 1], true, #[0])
#guard tabled (fun _ _ _ _ => growStep) 50 [0] == ([none], false, #[])
#guard tabled (fun _ _ _ _ => bstStep) 3 [(0, 0), (0, 3)] == ([some 2, none], false, #[])

end Tabled

/-! ## How often a derived generator exhausts, and why -/

namespace Outcome

open Basalt.Examples.Enum.Exhaustion

def summary (r : Report) : List Rat := [r.ok, r.refuted, r.fuel, r.truncated, r.inconclusive]

-- Blanket truncation at size 0 reports `bool`'s genuine refutations as truncated; per-call
-- truncation keeps them, and agrees with every larger size.
#guard summary (report (genHasType (G := WFinite) 10 .bool 0)) == [11/20, 0, 0, 9/20, 0]
#guard summary (report (genHasType' (G := WFinite) 10 .bool 0)) == [11/20, 9/20, 0, 0, 0]
#guard summary (report (genHasType' (G := WFinite) 10 .bool 0)) ==
  summary (report (genHasType (G := WFinite) 10 .bool 1))
#guard summary (report (genHasType' (G := WFinite) 2 .bool 0)) == [19/100, 17/100, 0, 0, 16/25]

-- `pos` needs recursion, so at size 0 it is truncated either way.
#guard summary (report (genHasType (G := WFinite) 5 .pos 0)) == [0, 0, 0, 1, 0]
#guard summary (report (genHasType' (G := WFinite) 5 .pos 0)) == [0, 0, 0, 1, 0]

end Outcome
