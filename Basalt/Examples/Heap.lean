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
    rw [Tree.genHeap, SPMF.support_pick, SPMF.support_pure, Set.mem_union, Set.mem_singleton_iff]
    simp [Tree.isHeap]
  | node l x r ih_l ih_r =>
    rw [Tree.genHeap, SPMF.support_pick, SPMF.support_pure, Set.mem_union, Set.mem_singleton_iff]
    simp only [SPMF.support_bind, SPMF.support_pure,
      Set.mem_setOf_eq, reduceCtorEq, Tree.node.injEq, false_or,
      Set.mem_singleton_iff]
    constructor
    · rintro ⟨delta, h_arb, l, hl_supp, r, hr_supp, ⟨rfl, hx_eq, rfl⟩⟩
      rw [hx_eq]
      have h_left : Tree.isHeap (lo + delta) l := by
        rw [← ih_l (lo := lo + delta)]
        exact hl_supp
      have h_right : Tree.isHeap (lo + delta) r := by
        rw [← ih_r (lo := lo + delta)]
        exact hr_supp
      have h_le : lo ≤ lo + delta := by omega
      exact ⟨h_le, h_left, h_right⟩
    · rintro ⟨hle, hl, hr⟩
      set delta := x - lo with hdelta_def
      have hx_eq : x = lo + delta := by omega
      rw [hx_eq] at hl hr
      have hl_supp : l ∈ SPMF.support (Tree.genHeap (lo + delta)) := by
        rw [ih_l (lo := lo + delta)]
        exact hl
      have hr_supp : r ∈ SPMF.support (Tree.genHeap (lo + delta)) := by
        rw [ih_r (lo := lo + delta)]
        exact hr
      have h_arb_support : delta ∈ SPMF.support Nat.arbitrary := Nat.arbitrary_support (n := delta)
      refine ⟨delta, h_arb_support, l, hl_supp, r, hr_supp, rfl, hx_eq, rfl⟩

/-- `genHeap` terminates with probability 1. -/
theorem Tree.genHeap_terminates : SPMF.IsPMF (Tree.genHeap lo) := by
  let g := fun (lo : Nat) => (Tree.genHeap lo : SPMF Tree)
  have hg : ∀ lo, SPMF.IsPMF (g lo) := by
    intro lo
    refine (SPMF.IsPMF_of_mass_fixpoint
      (g := g)
      (F := fun c => 1 / 2 + 1 / 2 * c ^ 2)
      ?bounds ?mass) lo
    case bounds =>
      intro c hle hge
      apply ENNReal.eq_one_of_fixed_ineq' hle hge
      intro hmono
      rw [ENNReal.toReal_add (by norm_num) (by aesop), ENNReal.toReal_mul] at hmono
      norm_num at hmono
      nlinarith [sq_nonneg c.toReal]
    case mass =>
      intro lo hc_le
      have hgoal : (g lo).mass ≥ 1 / 2 + 1 / 2 * (⨅ j, (g j).mass) ^ 2 := by
        dsimp [g] at *
        conv_lhs => rw [Tree.genHeap]
        simp only [SPMF.mass_pick, SPMF.mass_pure, mul_one]
        gcongr
        rw [sq]
        refine SPMF.mass_bind_ge_of_isPMF Nat.arbitrary_terminates (fun delta => ?_)
        refine SPMF.mass_bind_ge_mul (SPMF.mass_ge_iInf g (lo + delta)) (fun l => ?_)
        simpa [SPMF.mass_bind_pure] using SPMF.mass_ge_iInf g (lo + delta)
      exact hgoal
  exact hg lo

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
    simp [IsBounded_iff] at *
    intro t n hn
    have hnat : ∀ p ∈ (Nat.arbitrary : SPMF.Cost Nat).support, p.2 ≤ p.1 + 1 := by
      have := IsBounded_iff.mp Nat.arbitrary_cost
      simpa using this
    grind [
      pick,
      Nat.arbitrary,
      size,
      sum,
      SPMF.Cost.mem_support_bind_iff,
      SPMF.Cost.mem_support_pure_iff,
      SPMF.Cost.mem_support_choose_iff
    ]

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
