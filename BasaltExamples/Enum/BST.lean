/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Segev Elazar-Mittelman
-/
module

public import Basalt.Enum
public import BasaltExamples.BST

/-!
# Enumerating Binary Search Trees

There are finitely many BSTs with keys in `[lo, hi]`, so the enumeration is finite, and with `w`
keys to choose from there are `C(w, n) · Catalan(n)` of them with `n` nodes. Two ways to get them:

* `Tree.genBST` itself, untouched, run at `Finite`: its support is the whole finite set, and
  bucketing it by `Tree.size` is the enumeration. This lists every tree.
* `bstStep`, exactly sized and in open-recursion form over `(lo, hi, n)`, memoized: each tier is
  computed directly, each sub-tier once, and the two subtrees are paired by `<*>`, so a count never
  visits a tree.
-/

@[expose] public section

namespace BST

open Basalt RandomChoice

/-- Every BST with keys in `[lo, hi]`: the ordinary generator at `Finite`. -/
def allBSTs (lo hi : Int) : Basalt.Finite (Tree Int) := Tree.genBST (G := Basalt.Finite) lo hi

/-- How many of `s` have each size `0, …, n`. -/
def bucketBySize (s : Basalt.Finite (Tree Int)) (n : Nat) : List Nat :=
  let ts : List (Tree Int) := (s.toList?).getD []
  (List.range (n + 1)).map fun k => (ts.filter (·.size == k)).length

/-- The BSTs with keys in `[lo, hi]` with exactly `n` nodes: a root, and the other `n - 1` nodes
split between the two sides. -/
def bstStep [Monad G] [RandomChoice G] [Fail G] : KeyedStep (Int × Int × Nat) (·.2.2) G (Tree Int) :=
  fun ⟨lo, hi, n⟩ rec =>
  match n, rec with
  | 0, _ => pure .leaf
  | n + 1, rec =>
    if h : lo ≤ hi then do
      let x := lo + ((← choose 0 (hi - lo).toNat (Nat.zero_le _)).down.val : Int)
      let ⟨k, hk⟩ := (← choose 0 n (by omega)).down
      (fun l r => .node l x r) <$> rec (lo, x - 1, k) (by simp; omega)
        <*> rec (x + 1, hi, n - k) (by simp)
    else Fail.fail

/-- Every tier is defined: one step is, whenever the tiers it consults are. -/
theorem bstTier_defined (lo hi : Int) (n : Nat) :
    KeyedStep.fix (G := Basalt.Finite) bstStep (lo, hi, n) ≠ .undef := by
  refine KeyedStep.fix_defined _ (fun ⟨lo, hi, n⟩ rec hrec => ?_) _
  cases n with
  | zero => exact Finite.pure_ne_undef _
  | succ n =>
    show (if h : lo ≤ hi then _ else _) ≠ _
    split
    · refine Finite.bind_defined (Finite.choose_ne_undef _ _ _) fun _ _ =>
        Finite.bind_defined (Finite.choose_ne_undef _ _ _) fun ⟨⟨k, hk⟩⟩ _ => ?_
      exact Finite.seq_defined (Finite.map_defined _ (hrec _ _)) (hrec _ _)
    · exact Finite.fail_ne_undef

/-- Every tier lists exactly the trees the exact-size generator, run as a random generator with
failure (`OptionT SPMF`), can succeed with at that size: one step relates itself whenever the tiers
it consults do, so every tier does. -/
theorem bstTier_enumerates (lo hi : Int) (n : Nat) :
    EnumeratesSome (KeyedStep.fix (G := Basalt.Finite) bstStep (lo, hi, n))
      (KeyedStep.fix (G := OptionT SPMF) bstStep (lo, hi, n)) := by
  refine KeyedStep.fix_rel (@EnumeratesSome _) _ _ (fun ⟨lo, hi, n⟩ recM recN hrec => ?_) _
  cases n with
  | zero => exact EnumeratesSome.pure _
  | succ n =>
    dsimp only [bstStep]
    refine genRel_enumeratesSome.dite (fun h => ?_) (fun _ => EnumeratesSome.fail)
    refine EnumeratesSome.bind (fun _ => EnumeratesSome.bind (fun ⟨⟨k, hk⟩⟩ => ?_)
      (EnumeratesSome.choose _ _ _)) (EnumeratesSome.choose _ _ _)
    exact EnumeratesSome.seq (EnumeratesSome.map _ (hrec _ _)) (hrec _ _)

/-- So every tier is defined, and its entries are exactly the values the generator succeeds with. -/
theorem bstTier_mem_iff (lo hi : Int) (n : Nat) (t : Tree Int) :
    (KeyedStep.fix (G := Basalt.Finite) bstStep (lo, hi, n)).Mem t ↔
      some t ∈ ((KeyedStep.fix (G := OptionT SPMF) bstStep (lo, hi, n)).run).support :=
  bstTier_enumerates lo hi n (bstTier_defined lo hi n) t

/-- Tiers `0, …, w` of the BSTs with keys in `[lo, hi]`, `w` the number of keys, sharing a table. -/
def enumBSTs (lo hi : Int) : List (Basalt.Finite (Tree Int)) :=
  KeyedStep.memoPure (bstStep (G := MemoM _ _))
    ((List.range ((hi - lo + 1).toNat + 1)).map fun n => (lo, hi, n))

/-- Memoizing changes nothing: the tiers `enumBSTs` computes are `fix`'s. -/
theorem enumBSTs_eq (lo hi : Int) :
    enumBSTs lo hi = (List.range ((hi - lo + 1).toNat + 1)).map
      fun n => KeyedStep.fix (G := Basalt.Finite) bstStep (lo, hi, n) := by
  unfold enumBSTs
  rw [KeyedStep.memoPure_eq _ (bstStep (G := Basalt.Finite))
    (fun V ⟨lo, hi, n⟩ recM recF hrec => ?_)]
  · simp only [List.map_map, Function.comp_def]
  cases n with
  | zero => exact MemoM.rel_pure _
  | succ n =>
    dsimp only [bstStep]
    refine MemoM.rel_dite (fun h => ?_) (fun _ => MemoM.rel_fail)
    refine MemoM.rel_bind (fun _ => MemoM.rel_bind (fun ⟨⟨k, hk⟩⟩ => ?_)
      (MemoM.rel_choose _ _ _)) (MemoM.rel_choose _ _ _)
    exact MemoM.rel_seq (MemoM.rel_map _ (hrec _ _)) (hrec _ _)

/-- The memoized enumeration, end to end: tier `n` of `enumBSTs` is defined, and its entries are
exactly the trees the exact-size generator succeeds with at size `n`. -/
theorem enumBSTs_mem_iff (lo hi : Int) {n : Nat} (hn : n ≤ (hi - lo + 1).toNat) (t : Tree Int) :
    ((enumBSTs lo hi)[n]'(by simp [enumBSTs_eq]; omega)).Mem t ↔
      some t ∈ ((KeyedStep.fix (G := OptionT SPMF) bstStep (lo, hi, n)).run).support := by
  simp only [enumBSTs_eq, List.getElem_map, List.getElem_range]
  exact bstTier_mem_iff lo hi n t

/-- `C(n, k)`, as the running product `∏ (n - i) / (i + 1)`, exact at every step. -/
def binom (n k : Nat) : Nat :=
  (List.range k).foldl (fun c i => c * (n - i) / (i + 1)) 1

/-- The number of BSTs with `n` nodes and keys among `w` values. -/
def expectedCount (w n : Nat) : Nat := binom w n * (binom (2 * n) n / (n + 1))

end BST
