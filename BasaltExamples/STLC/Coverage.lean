/-
Copyright (c) 2026 Harrison Goldstein & Ernest Ng. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein & Ernest Ng
-/
module

public import Basalt
public import BasaltExamples.STLC.Termination
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# How Many Draws Until a Shape Appears

A property-based test draws its inputs independently, so a shape that one draw has with probability
at least `q` is missed by all of `N` draws with probability at most `(1 − q)ᴺ`. This file proves that
bound and its two consequences for repeated draws, then instantiates them for `genTerm` at
`Bool → Bool` in the empty context.

**Repeated draws** (`vectorOf N g` is `N` independent draws from `g`):

* `SPMF.prob_vectorOf_miss_le` (geometric bound): all `N` draws miss `E` with probability at most
  `(1 − q)ᴺ`.
* `SPMF.tsum_prob_vectorOf_miss_le` (expected waiting time): `∑ₙ P(the first n draws all miss E)`
  is at most `1 / q`. By the tail-sum formula this sum is the expected number of draws until the
  first draw in `E`.
* `SPMF.prob_vectorOf_someMiss_le` (coupon collector): for events `E i`, `i ∈ s`, some event is
  missed by all `N` draws with probability at most `∑ᵢ (1 − qᵢ)ᴺ`.
* `SPMF.tsum_prob_vectorOf_someMiss_le`: the expected number of draws until every event has
  appeared is at most `∑ᵢ 1 / qᵢ`.

**The STLC shapes**, one draw of `genTerm [] (Bool → Bool)`:

| Shape | Witness | Lower bound |
|---|---|---|
| `IsLinear`: every bound variable used exactly once | `λx. x` | `1/12` |
| `DiscardsArg`: a lambda that ignores its argument | `λx. b` | `1/2` |
| `IsApp`: an application at the root | any | `1/3` |

So (`genTerm_linear_within_53`) `53` tests see a linear term with probability at least `99%`, and
the expected number of tests until one does is at most `12` (`genTerm_linear_expected_le`). All three
shapes appear within `56` tests with probability at least `99%` (`genTerm_all_shapes_within_56`),
and on average within `17` tests (`genTerm_all_shapes_expected_le`).

`genTerm` terminates almost surely (`genTerm.terminates`), so its branches have mass `1` and the
`IsApp` bound is exact. The other two count one family of witnesses only.
-/

@[expose] public section

open RandomChoice
open scoped ENNReal

namespace SPMF

section draws

variable {α : Type} (g : SPMF α)

/-- An event and its complement split the mass. -/
theorem prob_compl_add_prob (E : Set α) : prob g Eᶜ + prob g E = g.mass := by
  unfold prob
  rw [← expect_add, ← expect_one]
  congr 1
  funext a
  by_cases h : a ∈ E <;> simp [Set.indicator, h]

/-- A lower bound `q` on the probability of `E` is an upper bound `1 − q` on the probability of its
complement. -/
theorem prob_compl_le {E : Set α} {q : ℝ≥0∞} (hq : q ≤ prob g E) : prob g Eᶜ ≤ 1 - q := by
  have hE : prob g E ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top
    ((prob_le_mass g E).trans (mass_le_one g))
  rw [ENNReal.eq_sub_of_add_eq hE (prob_compl_add_prob g E)]
  exact tsub_le_tsub (mass_le_one g) hq

/-- **The geometric bound.** If one draw lands in `E` with probability at least `q`, then `N`
independent draws all miss `E` with probability at most `(1 − q)ᴺ`. -/
theorem prob_vectorOf_miss_le {E : Set α} {q : ℝ≥0∞} (hq : q ≤ prob g E) (N : Nat) :
    prob (vectorOf N g) {xs | ∀ x ∈ xs, x ∉ E} ≤ (1 - q) ^ N := by
  have h := prob_vectorOf_all (g := g) Eᶜ N
  simp only [Set.mem_compl_iff] at h
  rw [h]
  exact pow_le_pow_left₀ (by positivity) (prob_compl_le g hq) N

/-- **The expected waiting time.** If one draw lands in `E` with probability at least `q`, then
`∑ₙ P(the first n draws all miss E) ≤ 1 / q`. The sum is the expected number of draws until the
first draw in `E`, by the tail-sum formula `E[T] = ∑ₙ P(T > n)`. -/
theorem tsum_prob_vectorOf_miss_le {E : Set α} {q : ℝ≥0∞} (hq : q ≤ prob g E) :
    ∑' N, prob (vectorOf N g) {xs | ∀ x ∈ xs, x ∉ E} ≤ q⁻¹ := by
  have hq1 : q ≤ 1 := hq.trans ((prob_le_mass g E).trans (mass_le_one g))
  calc ∑' N, prob (vectorOf N g) {xs | ∀ x ∈ xs, x ∉ E}
      ≤ ∑' N, (1 - q) ^ N := ENNReal.tsum_le_tsum fun N => prob_vectorOf_miss_le g hq N
    _ = q⁻¹ := by rw [ENNReal.tsum_geometric, ENNReal.sub_sub_cancel ENNReal.one_ne_top hq1]

/-- The union bound, for two events. -/
theorem prob_union_le (p : SPMF α) (A B : Set α) : prob p (A ∪ B) ≤ prob p A + prob p B := by
  unfold prob
  rw [← expect_add]
  refine expect_mono fun a => ?_
  by_cases ha : a ∈ A <;> by_cases hb : a ∈ B <;> simp [Set.indicator, ha, hb]

/-- **The coupon-collector bound.** If one draw lands in `E i` with probability at least `q i`, for
each `i ∈ s`, then after `N` independent draws some `E i` has been missed by every draw with
probability at most `∑ᵢ (1 − q i)ᴺ`. -/
theorem prob_vectorOf_someMiss_le {ι : Type} (s : Finset ι) (E : ι → Set α) (q : ι → ℝ≥0∞)
    (hq : ∀ i ∈ s, q i ≤ prob g (E i)) (N : Nat) :
    prob (vectorOf N g) {xs | ∃ i ∈ s, ∀ x ∈ xs, x ∉ E i} ≤ ∑ i ∈ s, (1 - q i) ^ N := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.notMem_empty, false_and, exists_false, Set.ofPred_false, Finset.sum_empty]
    exact le_of_eq ((prob_eq_zero_iff _ _).mpr fun _ _ h => h)
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    have hsub : {xs : List α | ∃ i ∈ insert a s, ∀ x ∈ xs, x ∉ E i}
        ⊆ {xs | ∀ x ∈ xs, x ∉ E a} ∪ {xs | ∃ i ∈ s, ∀ x ∈ xs, x ∉ E i} := by
      rintro xs ⟨i, hi, hxs⟩
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact Or.inl hxs
      · exact Or.inr ⟨i, hi, hxs⟩
    refine (prob_mono hsub).trans ((prob_union_le _ _ _).trans (add_le_add ?_ ?_))
    · exact prob_vectorOf_miss_le g (hq a (Finset.mem_insert_self a s)) N
    · exact ih fun i hi => hq i (Finset.mem_insert_of_mem hi)

/-- **The expected time to collect every coupon.** If one draw lands in `E i` with probability at
least `q i`, for each `i ∈ s`, then the expected number of draws until every `E i` has appeared,
`∑ₙ P(after n draws some E i is still missing)`, is at most `∑ᵢ 1 / q i`. -/
theorem tsum_prob_vectorOf_someMiss_le {ι : Type} (s : Finset ι) (E : ι → Set α) (q : ι → ℝ≥0∞)
    (hq : ∀ i ∈ s, q i ≤ prob g (E i)) :
    ∑' N, prob (vectorOf N g) {xs | ∃ i ∈ s, ∀ x ∈ xs, x ∉ E i} ≤ ∑ i ∈ s, (q i)⁻¹ := by
  calc ∑' N, prob (vectorOf N g) {xs | ∃ i ∈ s, ∀ x ∈ xs, x ∉ E i}
      ≤ ∑' N, ∑ i ∈ s, (1 - q i) ^ N :=
        ENNReal.tsum_le_tsum fun N => prob_vectorOf_someMiss_le g s E q hq N
    _ = ∑ i ∈ s, ∑' N, (1 - q i) ^ N := Summable.tsum_finsetSum fun _ _ => ENNReal.summable
    _ = ∑ i ∈ s, (q i)⁻¹ := by
        refine Finset.sum_congr rfl fun i hi => ?_
        have hq1 : q i ≤ 1 := (hq i hi).trans ((prob_le_mass g _).trans (mass_le_one g))
        rw [ENNReal.tsum_geometric, ENNReal.sub_sub_cancel ENNReal.one_ne_top hq1]

end draws

end SPMF

namespace STLC

/-! ## Shapes of terms -/

/-- The number of uses of the de Bruijn variable `k` in a term. -/
def Term.uses (k : Nat) : Term → Nat
  | .Bool _ => 0
  | .Var n => if n = k then 1 else 0
  | .App a b => Term.uses k a + Term.uses k b
  | .Abs _ b => Term.uses (k + 1) b

/-- A term is **linear** when every variable that a lambda binds is used exactly once in that
lambda's body. Variables of the context are unconstrained. -/
def Term.isLinear : Term → _root_.Bool
  | .Bool _ => true
  | .Var _ => true
  | .App a b => Term.isLinear a && Term.isLinear b
  | .Abs _ b => Term.uses 0 b == 1 && Term.isLinear b

/-- The terms that use their bound variables linearly. -/
def IsLinear : Set Term := {t | t.isLinear = true}

/-- A lambda at the root that ignores its argument. -/
def DiscardsArg : Set Term := {t | ∃ τ b, t = .Abs τ b ∧ b.uses 0 = 0}

/-- An application at the root. -/
def IsApp : Set Term := {t | ∃ a b, t = .App a b}

/-! ## Probability plumbing -/

section plumbing

open SPMF

/-- A draw followed by a continuation that meets the event with probability at least `d` on `F`. -/
theorem prob_bind_ge {α β : Type} {x : SPMF α} {f : α → SPMF β} {E : Set β} (F : Set α)
    {d : ℝ≥0∞} (hd : ∀ a ∈ F, d ≤ prob (f a) E) : prob x F * d ≤ prob (x >>= f) E := by
  rw [prob_bind, mul_comm, prob, ← expect_mul_left]
  refine expect_mono fun a => ?_
  by_cases ha : a ∈ F
  · simpa [Set.indicator, ha] using hd a ha
  · simp [Set.indicator, ha]

theorem prob_pure_of_mem {α : Type} {a : α} {E : Set α} (h : a ∈ E) :
    prob (Pure.pure a : SPMF α) E = 1 := by
  classical
  simp [prob_pure, h]

/-- A generator all of whose draws lie in `E` puts its whole mass on `E`. -/
theorem prob_eq_mass_of_subset {α : Type} {p : SPMF α} {E : Set α}
    (h : ∀ a ∈ support p, a ∈ E) : prob p E = p.mass := by
  unfold prob
  rw [← expect_one p]
  exact expect_congr_support fun a ha => by simp [Set.indicator, h a ha]

/-- An almost surely terminating generator lands in `Set.univ` with probability `1`. -/
theorem prob_univ_of_terminates {α : Type} {p : SPMF α} (h : IsAlmostSurelyTerminating p) :
    prob p Set.univ = 1 :=
  (prob_eq_mass_of_subset fun _ _ => Set.mem_univ _).trans h

end plumbing

/-! ## One draw of `genTerm` -/

/-- A Boolean literal. -/
def IsBoolLit : Set Term := {t | ∃ b, t = .Bool b}

theorem genBool_prob_boolLit : SPMF.prob (genBool : SPMF Term) IsBoolLit = 1 := by
  have h : ∀ t ∈ SPMF.support (genBool : SPMF Term), t ∈ IsBoolLit := by
    intro t ht
    unfold genBool at ht
    simp only [SPMF.mem_support_map_iff] at ht
    obtain ⟨b, -, rfl⟩ := ht
    exact ⟨b, rfl⟩
  rw [prob_eq_mass_of_subset h]
  exact (genZero.terminates (Γ := [Ty.Bool]) (τ := .Bool))

/-- In the context `[Bool]` at `Bool`, the variable `#0` is drawn with probability at least `1/4`:
`elements` over the one variable of type `Bool` is one branch of four. -/
theorem genTerm_bool_prob_var0 :
    (1 : ℝ≥0∞) / 4 ≤ SPMF.prob (genTerm [Ty.Bool] .Bool) {Term.Var 0} := by
  rw [genTerm]
  have hv : varsWithType [Ty.Bool] Ty.Bool = [Term.Var 0] := rfl
  simp only [hv, ne_eq, List.cons_ne_nil, not_false_eq_true, dite_true, oneOfWith_eq,
    SPMF.prob_oneOf]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
    List.length_nil]
  have h1 : SPMF.prob (elements [Term.Var 0] (List.cons_ne_nil _ _) : SPMF Term) {Term.Var 0} = 1 := by
    unfold SPMF.prob; rw [SPMF.expect_elements]; simp
  rw [h1, show ((0 + 1 + 1 + 1 + 1 : ℕ) : ℝ≥0∞) = 4 by norm_num]
  refine ENNReal.div_le_div_right ?_ _
  exact le_trans (le_add_right le_rfl) le_add_self

/-- In the context `[Bool]` at `Bool`, a Boolean literal is drawn with probability at least `1/2`:
the `genZero` branch and the introduction branch are both `genBool`. -/
theorem genTerm_bool_prob_boolLit :
    (1 : ℝ≥0∞) / 2 ≤ SPMF.prob (genTerm [Ty.Bool] .Bool) IsBoolLit := by
  rw [genTerm]
  have hv : varsWithType [Ty.Bool] Ty.Bool = [Term.Var 0] := rfl
  simp only [hv, ne_eq, List.cons_ne_nil, not_false_eq_true, dite_true, oneOfWith_eq,
    SPMF.prob_oneOf]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
    List.length_nil]
  rw [show genZero [Ty.Bool] Ty.Bool = (genBool : SPMF Term) from rfl, genBool_prob_boolLit,
    show ((0 + 1 + 1 + 1 + 1 : ℕ) : ℝ≥0∞) = 4 by norm_num]
  calc (1 : ℝ≥0∞) / 2 = (1 + 1) / 4 := by
        rw [ENNReal.div_eq_div_iff (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
        norm_num
    _ ≤ _ := by
        refine ENNReal.div_le_div_right (add_le_add le_rfl ?_) _
        exact le_add_left (le_add_left (by rw [add_zero]))

/-- The three branches of `genTerm [] (Bool → Bool)`, each with probability `1/3`. -/
theorem genTerm_fun_prob_eq (E : Set Term) :
    SPMF.prob (genTerm [] (.Fun .Bool .Bool)) E
      = (SPMF.prob (genZero [] (.Fun .Bool .Bool) : SPMF Term) E
        + (SPMF.prob (do
              let argTy ← genType
              let e1 ← genTerm [] (argTy.Fun (Ty.Bool.Fun Ty.Bool))
              let e2 ← genTerm [] argTy
              pure (e1.App e2) : SPMF Term) E
          + (SPMF.prob (do
                let e ← genTerm [Ty.Bool] Ty.Bool
                pure (Term.Abs Ty.Bool e) : SPMF Term) E + 0))) / 3 := by
  conv_lhs => rw [genTerm]
  simp only [show varsWithType [] (Ty.Fun .Bool .Bool) = [] from rfl, ne_eq, not_true_eq_false,
    dite_false, oneOfWith_eq, SPMF.prob_oneOf]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
    List.length_nil]
  norm_num

/-- **A linear term.** One draw of `genTerm [] (Bool → Bool)` is linear with probability at least
`1/12`: the introduction branch (`1/3`) with the body `#0` (`1/4`), which is `λx. x`. -/
theorem genTerm_prob_linear_ge :
    (1 : ℝ≥0∞) / 12 ≤ SPMF.prob (genTerm [] (.Fun .Bool .Bool)) IsLinear := by
  rw [genTerm_fun_prob_eq]
  have habs : (1 : ℝ≥0∞) / 4 ≤ SPMF.prob (do
      let e ← genTerm [Ty.Bool] Ty.Bool
      pure (Term.Abs Ty.Bool e) : SPMF Term) IsLinear := by
    refine le_trans ?_ (prob_bind_ge {Term.Var 0} (d := 1) fun e he => ?_)
    · rw [mul_one]; exact genTerm_bool_prob_var0
    · rw [Set.mem_singleton_iff.mp he, prob_pure_of_mem]
      rfl
  calc (1 : ℝ≥0∞) / 12 = 1 / 4 / 3 := by
        simp only [div_eq_mul_inv, one_mul]
        rw [← ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num))]
        norm_num
    _ ≤ _ := ENNReal.div_le_div_right
        (le_add_left (le_add_left (by rw [add_zero]; exact habs))) _

/-- **A lambda that ignores its argument.** One draw of `genTerm [] (Bool → Bool)` is `λx. b` for a
literal `b` with probability at least `1/2`: always under `genZero` (`1/3`), and at least half the
time under the introduction branch (`1/3 · 1/2`). -/
theorem genTerm_prob_discardsArg_ge :
    (1 : ℝ≥0∞) / 2 ≤ SPMF.prob (genTerm [] (.Fun .Bool .Bool)) DiscardsArg := by
  rw [genTerm_fun_prob_eq]
  have hlit : ∀ e ∈ IsBoolLit, (1 : ℝ≥0∞) ≤
      SPMF.prob (Pure.pure (Term.Abs Ty.Bool e) : SPMF Term) DiscardsArg := by
    rintro e ⟨b, rfl⟩
    rw [prob_pure_of_mem (show Term.Abs Ty.Bool (.Bool b) ∈ DiscardsArg from
      ⟨Ty.Bool, _, rfl, rfl⟩)]
  have hzero : 1 ≤ SPMF.prob (genZero [] (.Fun .Bool .Bool) : SPMF Term) DiscardsArg := by
    rw [show (genZero [] (.Fun .Bool .Bool) : SPMF Term)
        = (do let e ← genZero [Ty.Bool] Ty.Bool; pure (Term.Abs Ty.Bool e)) from rfl]
    refine le_trans ?_ (prob_bind_ge IsBoolLit hlit)
    rw [show genZero [Ty.Bool] Ty.Bool = (genBool : SPMF Term) from rfl, genBool_prob_boolLit,
      mul_one]
  have habs : (1 : ℝ≥0∞) / 2 ≤ SPMF.prob (do
      let e ← genTerm [Ty.Bool] Ty.Bool
      pure (Term.Abs Ty.Bool e) : SPMF Term) DiscardsArg := by
    refine le_trans ?_ (prob_bind_ge IsBoolLit hlit)
    rw [mul_one]; exact genTerm_bool_prob_boolLit
  calc (1 : ℝ≥0∞) / 2 = (1 + 1 / 2) / 3 := by
        rw [ENNReal.div_eq_div_iff (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
        rw [mul_add, mul_one, ENNReal.mul_div_cancel (by norm_num) (by norm_num)]
        norm_num
    _ ≤ _ := ENNReal.div_le_div_right
        (add_le_add hzero (le_add_left (by rw [add_zero]; exact habs))) _

/-- **An application.** One draw of `genTerm [] (Bool → Bool)` is an application with probability
at least `1/3`: the application branch, whose draws all terminate. -/
theorem genTerm_prob_isApp_ge :
    (1 : ℝ≥0∞) / 3 ≤ SPMF.prob (genTerm [] (.Fun .Bool .Bool)) IsApp := by
  rw [genTerm_fun_prob_eq]
  have happ : 1 ≤ SPMF.prob (do
      let argTy ← genType
      let e1 ← genTerm [] (argTy.Fun (Ty.Bool.Fun Ty.Bool))
      let e2 ← genTerm [] argTy
      pure (e1.App e2) : SPMF Term) IsApp := by
    refine le_trans ?_ (prob_bind_ge Set.univ (d := 1) fun argTy _ => ?_)
    · rw [prob_univ_of_terminates genType.terminates, mul_one]
    refine le_trans ?_ (prob_bind_ge Set.univ (d := 1) fun e1 _ => ?_)
    · rw [prob_univ_of_terminates genTerm.terminates, mul_one]
    refine le_trans ?_ (prob_bind_ge Set.univ (d := 1) fun e2 _ => ?_)
    · rw [prob_univ_of_terminates genTerm.terminates, mul_one]
    rw [prob_pure_of_mem (show Term.App e1 e2 ∈ IsApp from ⟨e1, e2, rfl⟩)]
  exact ENNReal.div_le_div_right (le_add_left (le_add_right happ)) _

/-! ## How many tests -/

theorem one_sub_eleven_twelfths : (1 : ℝ≥0∞) - 1 / 12 = 11 / 12 := by
  refine ENNReal.sub_eq_of_eq_add (by finiteness) ?_
  rw [ENNReal.div_add_div_same]
  norm_num
  exact (ENNReal.div_self (by norm_num) (by norm_num)).symm

theorem one_sub_half : (1 : ℝ≥0∞) - 1 / 2 = 1 / 2 := by
  refine ENNReal.sub_eq_of_eq_add (by finiteness) ?_
  rw [ENNReal.div_add_div_same]
  norm_num
  exact (ENNReal.div_self (by norm_num) (by norm_num)).symm

theorem one_sub_third : (1 : ℝ≥0∞) - 1 / 3 = 2 / 3 := by
  refine ENNReal.sub_eq_of_eq_add (by finiteness) ?_
  rw [ENNReal.div_add_div_same]
  norm_num
  exact (ENNReal.div_self (by norm_num) (by norm_num)).symm

/-- **53 tests see a linear term with probability at least 99%.** All `53` draws of
`genTerm [] (Bool → Bool)` are non-linear with probability at most `(11/12)⁵³ < 1/100`. -/
theorem genTerm_linear_within_53 :
    SPMF.prob (vectorOf 53 (genTerm [] (.Fun .Bool .Bool) : SPMF Term))
      {ts | ∀ t ∈ ts, t ∉ IsLinear} ≤ 1 / 100 := by
  refine le_trans (SPMF.prob_vectorOf_miss_le _ genTerm_prob_linear_ge 53) ?_
  rw [one_sub_eleven_twelfths, ← ENNReal.toReal_le_toReal (by finiteness) (by finiteness)]
  simp only [ENNReal.toReal_pow, ENNReal.toReal_div, ENNReal.toReal_ofNat, ENNReal.toReal_one]
  norm_num

/-- **The expected number of tests until a linear term is at most 12.** -/
theorem genTerm_linear_expected_le :
    ∑' N, SPMF.prob (vectorOf N (genTerm [] (.Fun .Bool .Bool) : SPMF Term))
      {ts | ∀ t ∈ ts, t ∉ IsLinear} ≤ 12 := by
  refine le_trans (SPMF.tsum_prob_vectorOf_miss_le _ genTerm_prob_linear_ge) (le_of_eq ?_)
  rw [one_div, inv_inv]

/-- The three shapes. -/
def shapes : Fin 3 → Set Term := ![IsLinear, DiscardsArg, IsApp]

/-- Their per-draw lower bounds. -/
noncomputable def shapeBounds : Fin 3 → ℝ≥0∞ := ![1 / 12, 1 / 2, 1 / 3]

theorem shapeBounds_le (i : Fin 3) :
    shapeBounds i ≤ SPMF.prob (genTerm [] (.Fun .Bool .Bool)) (shapes i) := by
  fin_cases i
  · exact genTerm_prob_linear_ge
  · exact genTerm_prob_discardsArg_ge
  · exact genTerm_prob_isApp_ge

/-- **56 tests see all three shapes with probability at least 99%.** After `56` draws of
`genTerm [] (Bool → Bool)`, some shape (linear, ignores its argument, application) is still missing
with probability at most `(11/12)⁵⁶ + (1/2)⁵⁶ + (2/3)⁵⁶ < 1/100`. -/
theorem genTerm_all_shapes_within_56 :
    SPMF.prob (vectorOf 56 (genTerm [] (.Fun .Bool .Bool) : SPMF Term))
      {ts | ∃ i ∈ Finset.univ, ∀ t ∈ ts, t ∉ shapes i} ≤ 1 / 100 := by
  refine le_trans (SPMF.prob_vectorOf_someMiss_le _ Finset.univ shapes shapeBounds
    (fun i _ => shapeBounds_le i) 56) ?_
  simp only [Fin.sum_univ_three, shapeBounds, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, one_sub_eleven_twelfths, one_sub_half,
    one_sub_third]
  rw [← ENNReal.toReal_le_toReal (by finiteness) (by finiteness),
    ENNReal.toReal_add (by finiteness) (by finiteness),
    ENNReal.toReal_add (by finiteness) (by finiteness)]
  simp only [ENNReal.toReal_pow, ENNReal.toReal_div, ENNReal.toReal_ofNat, ENNReal.toReal_one]
  norm_num

/-- **The expected number of tests until all three shapes have appeared is at most 17**
(`12 + 2 + 3`). -/
theorem genTerm_all_shapes_expected_le :
    ∑' N, SPMF.prob (vectorOf N (genTerm [] (.Fun .Bool .Bool) : SPMF Term))
      {ts | ∃ i ∈ Finset.univ, ∀ t ∈ ts, t ∉ shapes i} ≤ 17 := by
  refine le_trans (SPMF.tsum_prob_vectorOf_someMiss_le _ Finset.univ shapes shapeBounds
    (fun i _ => shapeBounds_le i)) (le_of_eq ?_)
  simp only [Fin.sum_univ_three, shapeBounds, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, one_div, inv_inv]
  norm_num

end STLC
