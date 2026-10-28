/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
module

public import Basalt.Enum
public import Basalt.Experiments.Budget

/-!
# Exact Sizes and Size-Biased Buckets

Two readings of a size.

* As a budget: `Sized.pay`, `Sized.splitBind` and `Sized.done` give FEAT's exact sizes from `Sized`
  alone. At `WithSize Finite`, `treeSized`'s tier `2k + 1` is the `Catalan k` trees with `k` nodes
  (a `pay` per constructor), and `compSized`'s tier `n` the compositions of `n` into `1`s and `2`s.
* As a control: `qtree` reads its size to weight its choices, QuickCheck-style. At
  `WithSize WFinite`, bucket `n` is the exact distribution it draws from at size `n`; its bucket is
  the size it was asked for, not the size of what it builds.
-/

@[expose] public section

namespace Basalt.Examples.Enum.Sizes

open Basalt RandomChoice Sized

inductive T where
  | leaf
  | node (l r : T)
  deriving Repr, BEq

def T.nodes : T → Nat
  | .leaf => 0
  | .node l r => l.nodes + r.nodes + 1

/-! ## Size as a budget -/

def treeSized [Gen G] [Sized G] [MonoSized G] [Fail G] : G T :=
  pay do
    if (← choose 0 1 (by omega)).down.val = 0 then done .leaf
    else splitBind treeSized fun l => splitBind treeSized fun r => done (.node l r)
partial_fixpoint

def compSized [Gen G] [Sized G] [MonoSized G] [Fail G] : G (List Nat) := do
  match (← choose 0 2 (by omega)).down.val with
  | 0 => done []
  | 1 => pay do return 1 :: (← compSized)
  | _ => pay (pay do return 2 :: (← compSized))
partial_fixpoint

/-! ## Reading the bucket to bias the weights

`qtree` is QuickCheck-style: at size `n` it builds a node with probability `n / (n + 1)`, and gives
each child half the size. Its bucket `n` is not its output size; it is the size it was asked for. -/

def qtree [Gen G] [Sized G] [MonoSized G] : G T :=
  Sized.sized fun n => do
    if (← choose 0 n (Nat.zero_le _)).down.val = 0 then pure .leaf
    else do
      let l ← Sized.resize (n / 2) qtree
      let r ← Sized.resize (n / 2) qtree
      pure (.node l r)
partial_fixpoint

/-- Bucket `n` of `qtree`: the exact probability of each number of nodes. -/
def qtreeBucket (n : Nat) : List (Nat × Rat) :=
  WFinite.pushforward T.nodes (((qtree (G := WithSize WFinite)).run n).entries?.getD [])

/-- Each bucket's total probability, mean number of nodes, and distribution of the number of nodes. -/
def qtreeSummary (n : Nat) : String :=
  let d := qtreeBucket n
  let total := d.foldl (fun s (_, w) => s + w) (0 : Rat)
  let mean := d.foldl (fun s (k, w) => s + k * w) (0 : Rat)
  s!"n={n} total={total} mean={mean} dist={d.map fun (k, w) => s!"{k}:{w}"}"

/-! ## Three children: a chain of `splitBind`s, and `splitInto`

A ternary tree of exact size (a `pay` per constructor). Chaining `splitBind` gives the first child
a uniform share of the size and the others what is left, so when sampling the first child is
larger on average; `splitInto` draws all three shares at once, every split alike. As enumerations
the two have the same trees; as samplers, different distributions. -/

inductive T3 where
  | leaf
  | node (a b c : T3)
  deriving Repr, BEq

def T3.size : T3 → Nat
  | .leaf => 1
  | .node a b c => 1 + a.size + b.size + c.size

def T3.children : T3 → List T3
  | .leaf => []
  | .node a b c => [a, b, c]

def tree3Chain [Gen G] [Sized G] [MonoSized G] [Fail G] : G T3 :=
  pay do
    if (← choose 0 1 (by omega)).down.val = 0 then done .leaf
    else splitBind tree3Chain fun a => splitBind tree3Chain fun b => do return .node a b (← tree3Chain)
partial_fixpoint

/-- `floor` is the least share a child is given: `1` rules out children of size `0`, which cannot be
built (every tree costs at least one). -/
def tree3Even [Gen G] [Sized G] [MonoSized G] [Fail G] (floor : Nat) : G T3 :=
  pay do
    if (← choose 0 1 (by omega)).down.val = 0 then done .leaf
    else
      match ← splitInto [floor, floor, floor] with
      | [i, j, k] => do
        let a ← Sized.resize i (tree3Even floor)
        let b ← Sized.resize j (tree3Even floor)
        let c ← Sized.resize k (tree3Even floor)
        pure (.node a b c)
      | _ => Fail.fail
partial_fixpoint

/-- The probability that the sampler at size `n` produces nothing. -/
def failsAt (g : WithSize WFinite T3) (n : Nat) : Rat :=
  1 - ((WFinite.entries? (g.run n)).getD []).foldl (fun s (_, w) => s + w) 0

/-- Each child's expected size, given that a tree of size `n` was produced: what the sampler at
size `n` gives, read exactly. -/
def childMeans (g : WithSize WFinite T3) (n : Nat) : List Rat :=
  let es := (WFinite.entries? (g.run n)).getD []
  let ok := es.foldl (fun s (_, w) => s + w) (0 : Rat)
  (List.range 3).map fun i =>
    (es.foldl (fun s (t, w) => s + ((t.children.getD i .leaf).size : Rat) * w) 0) / ok

/-! ## Three children, spending a budget

The same trees, the size spent as they are built rather than split ahead (`Budget`): a constructor
spends one, each child takes what it uses, and the rest goes on. -/

def tree3Spend [Gen G] [Spend G] : G T3 := do
  Spend.spend
  if (← choose 0 1 (by omega)).down.val = 0 then pure .leaf
  else do
    let a ← tree3Spend
    let b ← tree3Spend
    let c ← tree3Spend
    pure (.node a b c)
partial_fixpoint

end Basalt.Examples.Enum.Sizes
