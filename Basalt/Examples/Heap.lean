import Basalt
import Basalt.Examples.ArbNat

open RandomChoice ArbNat

namespace Heap

inductive Tree where
  | leaf : Tree
  | node : Tree → Nat → Tree → Tree
deriving Repr

def Tree.size : Tree → Nat
  | leaf => 0
  | node l _ r => l.size + r.size + 1

/-- The sum of every value stored in the tree. -/
def Tree.sum : Tree → Nat
  | leaf => 0
  | node l x r => l.sum + x + r.sum

/-- A `Tree` is a min-heap bounded below by `lo` when every node's value is at
    least `lo` and each subtree is itself a min-heap bounded below by that node's
    value. -/
def Tree.isHeap (lo : Nat) : Tree → Prop
  | leaf => True
  | node l x r =>
    lo ≤ x ∧
    isHeap x l ∧
    isHeap x r

/-- Generates an arbitrary min-heap whose values are all at least `lo`. -/
def Tree.genHeap [Gen G] (lo : Nat) : G Tree :=
  pick
    (fun () => pure leaf)
    (fun () => do
      let delta ← Nat.arbitrary
      let x := lo + delta
      let l ← Tree.genHeap x
      let r ← Tree.genHeap x
      return node l x r)
partial_fixpoint

/-- `genHeap` produces exactly the min-heaps bounded below by `lo`. -/
theorem Tree.genHeap_support :
    t ∈ SPMF.support (Tree.genHeap lo) ↔ Tree.isHeap lo t := by
  induction t generalizing lo with
  | leaf =>
    rw [Tree.genHeap]
    simp [Tree.isHeap]
  | node l x r ihl ihr =>
    rw [Tree.genHeap]
    support_simp [Tree.isHeap, Tree.node.injEq, Nat.arbitrary_support, true_and]
    constructor
    · rintro (h | ⟨d, l', hl', r', hr', hle, hld, hrd⟩)
      · simp at h
      · subst hld hle hrd
        exact ⟨by omega, ihl.mp hl', ihr.mp hr'⟩
    · rintro ⟨hle, hl, hr⟩
      right
      refine ⟨x - lo, l, ?_, r, ?_, rfl, by omega, rfl⟩
      · rw [show lo + (x - lo) = x by omega]; exact ihl.mpr hl
      · rw [show lo + (x - lo) = x by omega]; exact ihr.mpr hr

/-- `genHeap` terminates with probability 1. -/
theorem Tree.genHeap_terminates : SPMF.IsPMF (Tree.genHeap lo) := by
  -- Critical (mean offspring exactly 1); the recursion re-indexes the seed, hence the family form.
  refine SPMF.IsPMF_of_critical_family
    (fun (lo : Nat) => (Tree.genHeap lo : SPMF Tree))
    (F := fun c => 1 / 2 + 1 / 2 * c ^ 2)
    (fun c hle hge => ?_) ?_ lo
  · rw [← ENNReal.toReal_eq_one_iff]
    ennreal_to_real at hge   -- before `hle`: finiteness needs `c ≤ 1`
    ennreal_to_real at hle
    norm_num at hge hle
    nlinarith [sq_nonneg (c.toReal - 1)]
  · intro lo
    conv_rhs => beta_reduce; rw [Tree.genHeap]
    simp only [SPMF.mass_pick, SPMF.mass_pure, mul_one]
    gcongr
    rw [sq]
    refine SPMF.mass_bind_ge_of_isPMF Nat.arbitrary_terminates (fun delta => ?_)
    refine SPMF.mass_bind_ge_mul (SPMF.mass_ge_iInf _ (lo + delta)) (fun l => ?_)
    simpa [SPMF.mass_bind_pure] using SPMF.mass_ge_iInf
      (fun (lo : Nat) => (Tree.genHeap lo : SPMF Tree)) (lo + delta)

/-- `genHeap` makes a number of random choices bounded by the size and the sum
    of the values of the tree it produces (no backtracking choices). -/
theorem Tree.genHeap_cost :
    IsBounded (Tree.genHeap lo) (fun t => 3 * t.size + t.sum + 1) := by
  open Lean.Order in
  delta genHeap
  apply (fix_induct (motive := fun (g : Nat → SPMF.Cost Tree) => ∀ lo, IsBounded (g lo) (fun t => 3 * t.size + t.sum + 1)) _ ?admissible ?step) lo
  case admissible =>
    exact admissible_pi_apply _ fun _ => admissible_IsBounded _
  case step =>
    intro genHeap_rec ih lo
    rw [IsBounded_iff]
    rintro ⟨t, n⟩ hmem
    cost_support_simp at hmem
    obtain ⟨m, rfl, h | h⟩ := hmem
    · obtain ⟨rfl, rfl⟩ := h
      simp [Tree.size, Tree.sum]
    · obtain ⟨delta, n1, n2, hdelta,
        ⟨l, n3, n4, hl, ⟨r, n5, n6, hr, ⟨rfl, hn6⟩, hn4⟩, hn2⟩, hm⟩ := h
      have hd : n1 ≤ delta + 1 := IsBounded_iff.mp Nat.arbitrary_cost (delta, n1) hdelta
      have hL : n3 ≤ 3 * l.size + l.sum + 1 := ih (lo + delta) (l, n3) hl
      have hR : n5 ≤ 3 * r.size + r.sum + 1 := ih (lo + delta) (r, n5) hr
      show 1 + m ≤ 3 * (Tree.node l (lo + delta) r).size + (Tree.node l (lo + delta) r).sum + 1
      simp only [Tree.size, Tree.sum]
      omega

instance {lo : Nat} :
    LawfulGenerator (Tree.genHeap lo) (Tree.isHeap lo) (fun t => 3 * t.size + t.sum + 1) where
  support_iff := Tree.genHeap_support
  is_pmf := Tree.genHeap_terminates
  is_bounded := Tree.genHeap_cost

/- `genHeap` can be run in `IO`. -/
#guard_msgs(drop info) in
#eval (for _ in [0:20] do
  IO.println <| repr (← Tree.genHeap 0) : IO Unit)

/- `genHeap` can be run in `PlausibleGen`. -/
#guard_msgs(drop info) in
#eval (for _ in [0:20] do
  IO.println <| repr (← Plausible.Gen.run (Tree.genHeap (G := Plausible.Gen) 0) 10) : IO Unit)

end Heap
