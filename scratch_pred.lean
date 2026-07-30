import Basalt
import BasaltExperiments.UniformConstrained.Uniform
import BasaltExperiments.UniformConstrained.Predicate

open Lean.Order RandomChoice ENNReal
namespace UniformConstrained
universe u
variable {α : Type} {β γ δ : Type u}

/-! helpers over `Multiset (α ⊕ β)` -/

theorem filterMap_getLeft?_map_sumMap (M : Multiset (α ⊕ β)) (f : α → γ) (g : β → δ) :
    ((M.map (Sum.map f g)).filterMap Sum.getLeft?) = (M.filterMap Sum.getLeft?).map f := by
  rw [Multiset.filterMap_map, Multiset.map_filterMap]
  exact congrArg (fun h => Multiset.filterMap h M) (funext fun x => by cases x <;> rfl)

theorem mem_inr_map_sumMap {M : Multiset (α ⊕ β)} {f : α → γ} {g : β → δ} {d : δ}
    (h : Sum.inr d ∈ M.map (Sum.map f g)) : ∃ b, Sum.inr b ∈ M ∧ g b = d := by
  rw [Multiset.mem_map] at h
  obtain ⟨z, hz, hzd⟩ := h
  cases z with
  | inl a => exact absurd hzd (by simp [Sum.map])
  | inr b => exact ⟨b, hz, by simpa [Sum.map] using hzd⟩

theorem card_left_add_card_right (M : Multiset (α ⊕ β)) :
    (M.filterMap Sum.getLeft?).card + (M.filterMap Sum.getRight?).card = M.card := by
  refine Multiset.induction_on M (by simp) fun a s ih => ?_
  cases a with
  | inl y =>
    rw [Multiset.filterMap_cons_some Sum.getLeft? _ _ (b := y) rfl,
      Multiset.filterMap_cons_none (f := Sum.getRight?) _ _ rfl]
    simp only [Multiset.card_cons]; omega
  | inr y =>
    rw [Multiset.filterMap_cons_none (f := Sum.getLeft?) _ _ rfl,
      Multiset.filterMap_cons_some Sum.getRight? _ _ (b := y) rfl]
    simp only [Multiset.card_cons]; omega

theorem mem_filterMap_getRight? {M : Multiset (α ⊕ β)} {b : β}
    (h : b ∈ M.filterMap Sum.getRight?) : Sum.inr b ∈ M := by
  rw [Multiset.mem_filterMap] at h
  obtain ⟨z, hz, hzb⟩ := h
  cases z with
  | inl a => exact absurd hzb (by simp)
  | inr c => cases (Option.some_injective _ hzb); exact hz

theorem sum_map_sumElim (M : Multiset (α ⊕ β)) (f : α → ℝ≥0∞) (g : β → ℝ≥0∞) :
    (M.map (Sum.elim f g)).sum
      = ((M.filterMap Sum.getLeft?).map f).sum + ((M.filterMap Sum.getRight?).map g).sum := by
  refine Multiset.induction_on M (by simp) fun a s ih => ?_
  cases a with
  | inl y =>
    rw [Multiset.filterMap_cons_some Sum.getLeft? _ _ (b := y) rfl,
      Multiset.filterMap_cons_none (f := Sum.getRight?) _ _ rfl]
    simp only [Multiset.map_cons, Multiset.sum_cons, Sum.elim_inl, ih]
    rw [add_assoc]
  | inr y =>
    rw [Multiset.filterMap_cons_none (f := Sum.getLeft?) _ _ rfl,
      Multiset.filterMap_cons_some Sum.getRight? _ _ (b := y) rfl]
    simp only [Multiset.map_cons, Multiset.sum_cons, Sum.elim_inr, ih]
    rw [add_left_comm]

theorem sum_map_indicator [DecidableEq α] (M : Multiset α) (x : α) :
    (M.map (fun a => if x = a then (1 : ℝ≥0∞) else 0)).sum = (M.count x : ℝ≥0∞) := by
  refine Multiset.induction_on M (by simp) fun a s ih => ?_
  rw [Multiset.map_cons, Multiset.sum_cons, ih, Multiset.count_cons]
  by_cases h : x = a
  · simp [h, add_comm]
  · simp [h]

theorem sum_map_const_of_forall (M : Multiset β) (g : β → ℝ≥0∞) (v : ℝ≥0∞)
    (h : ∀ a ∈ M, g a = v) : (M.map g).sum = (M.card : ℝ≥0∞) * v := by
  induction M using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, ih (fun b hb => h b (Multiset.mem_cons_of_mem hb)),
      h a (Multiset.mem_cons_self _ _), Multiset.card_cons, Nat.cast_add, Nat.cast_one, add_mul,
      one_mul, add_comm]

/-! sum over indices of a `FinSet` -/

theorem sum_range_getElem?_map {α : Type u} (l : List α) (g : α → ℝ≥0∞) :
    ∑ i ∈ Finset.range l.length, ((l[i]?).map g).getD 0 = ((l : Multiset α).map g).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    rw [List.length_cons, Finset.sum_range_succ']
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.map_some, Option.getD_some]
    rw [ih]
    show _ = ((x ::ₘ (xs : Multiset α)).map g).sum
    rw [Multiset.map_cons, Multiset.sum_cons, add_comm]

theorem sum_range_indexSet_map {α : Type u} (s : FinSet α) (g : α → ℝ≥0∞) :
    ∑ i ∈ Finset.range s.card, ((s.indexSet i).map g).getD 0 = (s.toMultiset.map g).sum := by
  simp only [FinSet.indexSet_eq_getElem?, FinSet.card_eq_length_toList]
  exact sum_range_getElem?_map s.toList g


variable {α : Type}

theorem tsum_count_mul [DecidableEq α] (M : Multiset α) (g : α → ℝ≥0∞) :
    ∑' z, (M.count z : ℝ≥0∞) * g z = (M.map g).sum := by
  refine Multiset.induction_on M (by simp) fun a s ih => ?_
  have hz : ∀ z, ((a ::ₘ s).count z : ℝ≥0∞) * g z
      = (s.count z : ℝ≥0∞) * g z + (if z = a then g z else 0) := by
    intro z
    rw [Multiset.count_cons]
    by_cases h : z = a <;> simp [h, add_mul]
  rw [tsum_congr hz, ENNReal.tsum_add, ih, tsum_eq_single a (by intro b hb; simp [hb]),
    if_pos rfl, Multiset.map_cons, Multiset.sum_cons, add_comm]

theorem uniformSet_bind_apply {β : Type} (s : FinSet α) (hne : 0 < s.card) (f : α → SPMF β)
    (y : β) :
    ((uniformSet s hne : SPMF α) >>= f) y
      = (s.toMultiset.map (fun z => f z y)).sum / (s.card : ℝ≥0∞) := by
  classical
  rw [SPMF.bind_apply]
  have h1 : ∀ z, (uniformSet s hne : SPMF α) z * f z y
      = (s.toMultiset.count z : ℝ≥0∞) * f z y / (s.card : ℝ≥0∞) := by
    intro z
    rw [uniformSet_apply s hne z, ← ENNReal.mul_div_right_comm]
  rw [tsum_congr h1]
  rw [show (∑' z, (s.toMultiset.count z : ℝ≥0∞) * f z y / (s.card : ℝ≥0∞))
      = (∑' z, (s.toMultiset.count z : ℝ≥0∞) * f z y) / (s.card : ℝ≥0∞) from by
    simp only [div_eq_mul_inv]
    exact ENNReal.tsum_mul_right]
  rw [tsum_count_mul]


section UniformDef
open scoped Space

variable {G : Type → Type} [Gen G]

def uniform (O : LazyOracle) (fuel : Nat) (p : α → Bool) (s : Space α) (k : Nat)
    (hne : 0 < (Space.sized s k).card) : G (Option α) := do
  match sizedP O fuel p s k with
  | none => pure none
  | some r =>
    have hr : 0 < r.card := by
      rw [card_sizedP O fuel p s k r (by assumption)]; exact hne
    let x ← uniformSet r hr
    match x with
    | .inl a => pure (some a)
    | .inr s' =>
      if h : 0 < (Space.sized s' k).card then
        uniform O fuel p s' k h
      else
        pure none
partial_fixpoint

end UniformDef

end UniformConstrained
