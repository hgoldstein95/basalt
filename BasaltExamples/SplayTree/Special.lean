/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import BasaltExamples.SplayTree.Basic

open RandomChoice

/-!
# Splay Trees: the Special Structure

`Tree.genSpecial n lo hi` generates the benchmark's *additional property* (Dewey, Nichols and
Hardekopf, ICSE 2015, §V): a bounded search tree that is currently too deep, yet that some single
`splay` would bring within `splayBound`. It is the one generator in this cookbook that filters
rather than constructs; the section "Why this one filters" argues that this is the right choice
here, and `Tree.genSpecialRetry` is the law that makes the choice pay.
-/

namespace SplayTree

/-- A bounded search tree with a node deeper than `splayBound t.size`, some *one* of whose keys can
be splayed to bring every node to depth at most `splayBound t.size`. -/
def Tree.isSpecial (n : Nat) (lo hi : Int) (t : Tree) : Prop :=
  t.isBoundedBST n lo hi ∧
  t.hasDeeperNode (splayBound t.size) ∧
  ∃ x ∈ t.keys, (t.splay x).allWithinDepth (splayBound t.size)

/-- A tree is no deeper than it is large. -/
theorem Tree.height_le_size (t : Tree) : t.height ≤ t.size := by
  induction t with
  | leaf => simp [Tree.height, Tree.size]
  | node l x r ihl ihr =>
    simp only [Tree.height, Tree.size]
    omega

/-- **The property is unsatisfiable below five nodes.** Being deeper than `splayBound t.size` forces
`splayBound t.size + 2 ≤ t.size`, and that first holds at `t.size = 5`. Together with
`Tree.genSpecial.productive`, which exhibits a five-node witness, this pins the exact node budget at
which the benchmark's property becomes satisfiable. -/
theorem Tree.not_isSpecial_of_size_le_four {t : Tree} {n : Nat} {lo hi : Int} (h : t.size ≤ 4) :
    ¬ t.isSpecial n lo hi := by
  rintro ⟨-, hdeep, -⟩
  rw [Tree.hasDeeperNode] at hdeep
  have hsmall : ∀ m : Nat, m ≤ 4 → ¬ splayBound m + 1 < m := by decide
  exact hsmall t.size h (lt_of_lt_of_le hdeep (Tree.height_le_size t))

/-- The decidable shape test the generator filters on: the two conjuncts of `Tree.isSpecial` that
are not already guaranteed by `Tree.genBoundedBST`. -/
def Tree.specialShape (t : Tree) : Bool :=
  t.hasDeeperNode (splayBound t.size) &&
    t.keys.any fun x => (t.splay x).allWithinDepth (splayBound t.size)

theorem Tree.specialShape_eq_true {t : Tree} :
    t.specialShape = true ↔
      t.hasDeeperNode (splayBound t.size) ∧
        ∃ x ∈ t.keys, (t.splay x).allWithinDepth (splayBound t.size) := by
  simp [Tree.specialShape]

/-- The outcome predicate of a filtering generator: a rejection constrains nothing, and every
accepted tree is special.

**This predicate is `True` on `none`, so a `sound_complete` stated against it pins the successes and
says nothing whatever about the failures.** That is Basalt's convention for `Option`-valued
generators and it is not a defect, but it is only half a specification: the statement that pins the
whole distribution is `Tree.genSpecialRetry.sound_complete`, where retrying has already driven the
failure mass to zero. -/
def isSpecialOutcome (n : Nat) (lo hi : Int) : Option Tree → Prop
  | none => True
  | some t => t.isSpecial n lo hi

/-! ## Why this one filters

Every other special generator in this cookbook builds its property in as it goes. This one does not,
and the reason is a property of `splay`, not a gap in the effort spent:

1. **Both conjuncts are global.** `hasDeeperNode` is a statement about the deepest node of the whole
   tree and `allWithinDepth (splay x ·)` about the whole tree after a rewrite. Neither is an
   invariant a recursive generator can carry down into a subtree, because neither is determined by
   any subtree: the same left child is special or not depending on what the right child does to
   `t.size`, which sets the threshold.

2. **A constructive generator would have to enumerate splay fibers, and they are not points.**
   Conjunct two says `t ∈ splay_x⁻¹ {u | u.height ≤ splayBound t.size + 1}` for some key `x`, so
   constructing it means inverting `splay`. But `splay x` is a *retraction* onto the trees with `x`
   at the root, not a bijection — it collapses `Cat n` trees onto `Cat i · Cat (n-1-i)` — so a
   pre-image is a fiber, and completeness needs whole fibers rather than one representative.
   `Tree.IsUnsplay` (`SplayTree/Unsplay.lean`) does describe fibers, but only the uniform ones: one
   hanging size throughout, and an access path made of double rotations alone. Its bridge to
   `Tree.isSpecial` runs one way and there is no converse, so it cannot be the complete generator.

3. **The filter is complete for free, and the property is not rare.** `Tree.genBoundedBST` is
   sound and complete for the bounded search trees, so testing a decidable shape condition on its
   output is sound and complete for the special ones by construction — no fiber analysis at all.
   And rejection is cheap: `BasaltTest/IO.lean` pins the measured acceptance rate, which *rises*
   with the node budget, because deep trees come to dominate the search trees on `n` keys while the
   flatness threshold `splayBound` grows only logarithmically. This is the opposite of the usual
   filtering failure mode, where the target set thins out as the bound grows.

4. **The cost is provable, not just measured.** `Tree.genSpecialMixed` (`SplayTree/Unsplay.lean`)
   mixes this generator with the constructive family, which cannot fail; `SPMF.massSome_pick` then
   turns "one branch never rejects" into an acceptance rate of at least `1/2`, and
   `IsProductiveAtRate.expectedAttempts_le` turns that into a bound on retries. The narrow
   constructive family earns its keep as the branch that supplies a rate, which is a job it can do
   without being complete.
-/

/-- Draws a bounded search tree and keeps it only when it is special. The property is global — it
quantifies over every key's splay — so it cannot be maintained by a local recursion; see "Why this
one filters" above. -/
def Tree.genSpecial [Gen G] (n : Nat) (lo hi : Int) : G (Option Tree) := do
  let t ← Tree.genBoundedBST n lo hi
  if t.specialShape then pure (some t) else pure none

theorem Tree.genSpecial.terminates (n : Nat) (lo hi : Int) :
    IsAlmostSurelyTerminating (Tree.genSpecial n lo hi) := by
  rw [Tree.genSpecial]
  refine SPMF.IsPMF_bind (Tree.genBoundedBST.terminates n lo hi) fun t => ?_
  split <;> exact SPMF.IsPMF_pure _

theorem Tree.genSpecial_mem_support (t : Tree) (n : Nat) (lo hi : Int) :
    some t ∈ SPMF.support (Tree.genSpecial n lo hi) ↔ t.isSpecial n lo hi := by
  unfold Tree.genSpecial
  simp [Tree.genBoundedBST_mem_support, Tree.isSpecial, Tree.specialShape_eq_true]

/-- A rejection is always reachable: `leaf` is bounded by every budget and is never special. -/
theorem Tree.none_mem_support_genSpecial (n : Nat) (lo hi : Int) :
    none ∈ SPMF.support (Tree.genSpecial n lo hi) := by
  unfold Tree.genSpecial
  simp only [SPMF.mem_support_bind_iff, SPMF.mem_support_ite_iff, SPMF.mem_support_pure_iff]
  refine ⟨Tree.leaf,
    (Tree.genBoundedBST_mem_support _ n lo hi).mpr ⟨by simp [Tree.size], trivial⟩, ?_⟩
  simp [Tree.specialShape, Tree.hasDeeperNode, Tree.size, Tree.height]

/-- Rejection sampling is safe as soon as one special tree fits: a single reachable success bounds
`massSome` below. `Tree.genSpecial.productive` (`SplayTree/Unsplay.lean`) discharges the hypothesis
by constructing a special tree. -/
theorem Tree.IsProductive_genSpecial {n : Nat} {lo hi : Int} {t : Tree} (h : t.isSpecial n lo hi) :
    IsProductive (Tree.genSpecial n lo hi) :=
  IsProductive_of_mem_support ((Tree.genSpecial_mem_support t n lo hi).mpr h)

theorem Tree.genSpecial.sound_complete :
    IsSoundAndComplete (Tree.genSpecial n lo hi) (isSpecialOutcome n lo hi) := by
  rintro (_ | t)
  · exact ⟨fun _ => trivial, fun _ => Tree.none_mem_support_genSpecial n lo hi⟩
  · exact Tree.genSpecial_mem_support t n lo hi

/-! ## Retrying the filter

What a harness actually runs is not one draw but draws until one succeeds, and that object has a
distribution worth a law: retrying moves every rejection off the support, so a `sound_complete`
about it pins the *whole* distribution rather than only its successes. Every statement here is
conditional on productivity, which `Tree.genSpecial.productive` (`SplayTree/Unsplay.lean`)
discharges by exhibiting a special tree. -/

/-- `Tree.genSpecial`, redrawn on rejection. -/
noncomputable def Tree.genSpecialRetry (n : Nat) (lo hi : Int) : SPMF (Option Tree) :=
  SPMF.retry (Tree.genSpecial n lo hi)

theorem Tree.genSpecialRetry.filter_free (hprod : IsProductive (Tree.genSpecial n lo hi)) :
    IsFilterFree (Tree.genSpecialRetry n lo hi) :=
  SPMF.massSome_retry _ (Tree.genSpecial.terminates n lo hi) hprod

/-- **The law with nothing left implicit.** Unlike `Tree.genSpecial.sound_complete`, whose predicate
is vacuous on `none`, this one has no `none` to be vacuous about: the support is exactly the special
trees, tagged `some`. -/
theorem Tree.genSpecialRetry.sound_complete (hprod : IsProductive (Tree.genSpecial n lo hi)) :
    IsSoundAndComplete (Tree.genSpecialRetry n lo hi)
      (fun o => ∃ t, o = some t ∧ t.isSpecial n lo hi) := by
  have hmass : (Tree.genSpecial n lo hi : SPMF (Option Tree)).mass = 1 :=
    Tree.genSpecial.terminates n lo hi
  have hs_le : SPMF.massSome (Tree.genSpecial n lo hi) ≤ 1 := by
    rw [← hmass, SPMF.mass_split]; exact le_self_add
  have hs_ne_top : SPMF.massSome (Tree.genSpecial n lo hi) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top hs_le
  rintro (_ | t)
  · constructor
    · exact fun hmem => absurd (SPMF.retry_none_eq_zero _ hmass hprod)
        ((SPMF.apply_pos_iff _ none).mpr hmem).ne'
    · rintro ⟨t, ht, -⟩; simp at ht
  · rw [Tree.genSpecialRetry, ← SPMF.apply_pos_iff, SPMF.retry_apply _ hmass hprod,
      ENNReal.div_pos_iff]
    simp only [Option.some.injEq, exists_eq_left']
    constructor
    · rintro ⟨hne, -⟩
      exact (Tree.genSpecial_mem_support t n lo hi).mp
        (by by_contra hc; exact hne ((SPMF.apply_eq_zero_iff _ _).mpr hc))
    · exact fun h => ⟨fun hz => ((SPMF.apply_eq_zero_iff _ _).mp hz)
        ((Tree.genSpecial_mem_support t n lo hi).mpr h), hs_ne_top⟩

/-- **A rate bounds the retries.** Instantiating `IsProductiveAtRate.expectedAttempts_le` at this
generator: an acceptance rate of `r` caps the expected number of draws the retry loop performs at
`1 / r`. `Tree.genSpecialMixed.productive_at_rate` (`SplayTree/Unsplay.lean`) supplies an `r`. -/
theorem Tree.genSpecial.expectedAttempts_le {r : ENNReal}
    (h : IsProductiveAtRate (Tree.genSpecial n lo hi) r) :
    SPMF.expectedAttempts (Tree.genSpecial n lo hi) ≤ 1 / r :=
  h.expectedAttempts_le (Tree.genSpecial.terminates n lo hi)

end SplayTree
