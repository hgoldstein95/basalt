import Basalt

open RandomChoice

namespace AllTwoTree

inductive Tree : Type where
  | leaf : Tree
  | node : Tree → Nat → Tree → Tree

def Tree.size : Tree → Nat
  | .leaf => 0
  | .node l _ r => l.size + r.size + 1

def Tree.isAllTwos : Tree → Prop
  | .leaf => True
  | .node l v r => v = 2 ∧ Tree.isAllTwos l ∧ Tree.isAllTwos r

def Tree.cost : Tree → Nat := fun t => 3 * t.size + 1

def genTree [Gen G] : G Tree :=
  pick
    (fun () => pure .leaf)
    (fun () => do
      let l ← genTree
      let r ← genTree
      return .node l 2 r)
partial_fixpoint

theorem genTree_support : t ∈ SPMF.support genTree ↔ Tree.isAllTwos t := by
  fun_induction Tree.isAllTwos
    <;> rw [genTree]
    <;> simp
  grind

theorem genTree_terminates : SPMF.IsPMF genTree := by
  haveI : Nonempty Unit := ⟨()⟩
  refine (SPMF.IsPMF_of_mass_fixpoint
      (g := fun (_ : Unit) => (genTree : SPMF Tree))
      (F := fun c => 1 / 2 + 1 / 2 * c ^ 2)
      ?bounds ?mass) ()
  case bounds =>
    intro c hle hge
    apply ENNReal.eq_one_of_fixed_ineq' hle hge
    intro hmono
    rw [ENNReal.toReal_add (by norm_num) (by aesop), ENNReal.toReal_mul] at hmono
    norm_num at hmono
    nlinarith [sq_nonneg c.toReal]
  case mass =>
    intro i hc_le
    conv_lhs => rw [genTree]
    simp only [SPMF.mass_pick, SPMF.mass_pure, mul_one]
    gcongr
    rw [sq]
    apply SPMF.mass_bind_ge_mul (SPMF.mass_ge_iInf _ ())
    intro l
    simp only [SPMF.mass_bind_pure]
    exact SPMF.mass_ge_iInf _ ()

theorem genTree_cost : IsBounded genTree Tree.cost := by
  open Lean.Order in
  delta genTree
  apply (fix_induct (motive := fun (g : SPMF.Cost Tree) => IsBounded g Tree.cost) _ ?admissible ?step)
  case admissible =>
    exact admissible_IsBounded _
  case step =>
    intro genTree_rec ih
    simp [IsBounded_iff] at *
    intro t n hn
    grind [
      pick,
      Tree.cost,
      Tree.size,
      SPMF.Cost.mem_support_bind_iff,
      SPMF.Cost.mem_support_pure_iff,
      SPMF.Cost.mem_support_choose_iff
    ]

instance : LawfulGenerator genTree Tree.isAllTwos Tree.cost where
  support_iff := genTree_support
  is_pmf      := genTree_terminates
  is_bounded  := genTree_cost

end AllTwoTree
