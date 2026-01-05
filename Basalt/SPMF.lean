import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.MeasureTheory.Measure.Dirac
import Basalt.RandomChoice

open Lean.Order RandomChoice NNReal ENNReal MeasureTheory

/-!
# Sub-Probability Mass Functions

This file defines a type of sub-probability mass functions, similar to `PMF` from Mathlib.
-/

/-- A sub-probability mass function is similar to a PMF, but the total mass may be less than 1. -/
def SPMF.{u} (α : Type u) : Type u := {μ : α → ℝ≥0∞ // (∑' a, μ a) ≤ 1}

namespace SPMF

instance instBot : Bot (SPMF α) where
  bot := ⟨fun _ => 0, by simp⟩

instance instFunLike : FunLike (SPMF α) α ℝ≥0∞ where
  coe p a := p.1 a
  coe_injective' _ _ h := Subtype.ext h

@[ext]
protected theorem ext {p q : SPMF α} (h : ∀ x, p x = q x) : p = q :=
  DFunLike.ext p q h

@[simp]
theorem tsum_coe (p : SPMF α) : ∑' a, p a ≤ 1 := p.2

theorem tsum_coe_ne_top (p : SPMF α) : ∑' a, p a ≠ ∞ := by
  have := ENNReal.one_lt_top
  have := p.tsum_coe
  grind only

theorem tsum_coe_indicator_ne_top (p : SPMF α) (s : Set α) : ∑' a, s.indicator p a ≠ ∞ :=
  ne_of_lt (lt_of_le_of_lt
    (ENNReal.tsum_le_tsum (fun _ => Set.indicator_apply_le fun _ => le_rfl))
    (lt_of_le_of_ne le_top p.tsum_coe_ne_top))

def support (p : SPMF α) : Set α := Function.support p

theorem mem_support_iff (p : SPMF α) (a : α) : a ∈ p.support ↔ p a ≠ 0 := Iff.rfl

@[simp]
theorem support_countable (p : SPMF α) : p.support.Countable :=
  Summable.countable_support_ennreal (tsum_coe_ne_top p)

theorem apply_eq_zero_iff (p : SPMF α) (a : α) : p a = 0 ↔ a ∉ p.support := by
  rw [mem_support_iff, Classical.not_not]

theorem apply_pos_iff (p : SPMF α) (a : α) : 0 < p a ↔ a ∈ p.support :=
  pos_iff_ne_zero.trans (p.mem_support_iff a).symm

theorem coe_le_one (p : SPMF α) (a : α) : p a ≤ 1 := by
  have h₁ := p.tsum_coe
  have h₂ := ENNReal.le_tsum (f := p) a
  grind only

theorem apply_ne_top (p : SPMF α) (a : α) : p a ≠ ∞ :=
  ne_of_lt (lt_of_le_of_lt (p.coe_le_one a) ENNReal.one_lt_top)

theorem apply_lt_top (p : SPMF α) (a : α) : p a < ∞ :=
  lt_of_le_of_ne le_top (p.apply_ne_top a)

open Classical in
/-- A dirac distribution; all of the mass is on `a`. -/
noncomputable def pure (a : α) : SPMF α :=
  ⟨fun a' => if a' = a then 1 else 0, by simp⟩

/-- The standard Giry monad approach to PMF composition. -/
noncomputable def bind (p : SPMF α) (f : α → SPMF β) : SPMF β := by
  refine ⟨fun b => ∑' a, p a * f a b, ?pf⟩
  have p_prop := p.tsum_coe
  have : ∑' (b : β) (a : α), p a * f a b ≤ ∑' (a : α), p a := by
    simp [ENNReal.tsum_comm, ENNReal.tsum_mul_left, ENNReal.tsum_le_tsum, mul_le_of_le_one_right']
  grind only

noncomputable instance : Monad SPMF where
  pure a := pure a
  bind p f := p.bind f

/-- This order captures a notion of "definedness." If `p ≤ q`, then any value that has mass in `p`
has at least as much mass in `q`. -/
instance : Lean.Order.PartialOrder (SPMF α) where
  rel p q := ∀ a, p a ≤ q a
  rel_refl := by grind
  rel_trans := by grind
  rel_antisymm h₁ h₂ := by ext; grind

/-- The supremum of a chain is the SPMF where each point is maximally defined. -/
noncomputable def csupFun {α : Type u} (c : Set (SPMF α)) : α → ℝ≥0∞ :=
  fun a => ⨆ f ∈ c, f a

-- TODO: This proof came from Claude, and I'm not sure I 100% understand why it needs to be so
-- complicated. I'm planning on coming back to try to understand it better later.
theorem csupFun_sum_le_one
  {c : Set (SPMF α)}
  (h_chain : chain c) :
  (∑' a, csupFun c a) ≤ 1 := by
  -- For a chain, the biSup over elements is either achieved at some element or is ⊥
  by_cases hc : c.Nonempty
  · -- When c is nonempty, use that chains are directed
    have h_directed : DirectedOn (· ⊑ ·) c := fun x hx y hy => by
      rcases h_chain x y hx hy with h | h
      · exact ⟨y, hy, h, PartialOrder.rel_refl⟩
      · exact ⟨x, hx, PartialOrder.rel_refl, h⟩
    -- The chain is also directed w.r.t. ≤ on ℝ≥0∞ pointwise
    have h_directed_le : DirectedOn (fun f g => ∀ a, f a ≤ g a) c := fun x hx y hy => by
      rcases h_directed x hx y hy with ⟨z, hz, hxz, hyz⟩
      exact ⟨z, hz, hxz, hyz⟩

    obtain ⟨f₀, hf₀⟩ := hc
    calc ∑' a, csupFun c a
      _ = ⨆ s : Finset α, ∑ a ∈ s, csupFun c a := ENNReal.tsum_eq_iSup_sum
      _ = ⨆ s : Finset α, ∑ a ∈ s, ⨆ f ∈ c, f a := rfl
      _ ≤ ⨆ s : Finset α, ⨆ f ∈ c, ∑ a ∈ s, f a := by
          apply iSup_mono; intro s
          -- For a finite set s, we use directedness to interchange sum and sup
          -- ∑ a ∈ s, ⨆ f ∈ c, f a ≤ ⨆ f ∈ c, ∑ a ∈ s, f a
          -- This follows from directedness: for any finite s, we can find an upper bound
          -- Rewrite biSup as iSup over Subtype
          simp_rw [iSup_subtype']
          -- Use finsetSum_iSup with directedness
          have hdir : ∀ (f g : c), ∃ k : c, ∀ a, (f : SPMF α) a ≤ (k : SPMF α) a ∧ (g : SPMF α) a ≤ (k : SPMF α) a := by
            intro ⟨f, hf⟩ ⟨g, hg⟩
            rcases h_directed_le f hf g hg with ⟨k, hk, hfk, hgk⟩
            exact ⟨⟨k, hk⟩, fun a => ⟨hfk a, hgk a⟩⟩
          rw [ENNReal.finsetSum_iSup hdir]
      _ = ⨆ f ∈ c, ⨆ s : Finset α, ∑ a ∈ s, f a := by
          rw [iSup_comm]; congr 1
          ext f
          rw [iSup_comm]
      _ = ⨆ f ∈ c, ∑' a, f a := by
          congr 1; ext f; congr 1; ext _
          exact ENNReal.tsum_eq_iSup_sum.symm
      _ ≤ 1 := by apply iSup₂_le; intro f _; exact f.tsum_coe
  · -- When c is empty, the sup is 0
    simp only [Set.not_nonempty_iff_eq_empty] at hc
    simp [csupFun, hc]

noncomputable instance : CCPO (SPMF α) where
  has_csup := by
    intros c hc
    exists ?sup
    case sup => exact ⟨csupFun c, csupFun_sum_le_one hc⟩
    intro x
    constructor
    · intro h_csup_le y hy a
      exact Trans.trans (le_iSup₂_of_le y hy le_rfl) (h_csup_le a)
    · intro h_ub a
      unfold csupFun
      apply iSup₂_le
      intro y hy
      exact h_ub y hy a

instance : MonoBind SPMF where
  bind_mono_left {_ _} {p₁ p₂ f} h b := by
    simp only [Bind.bind, bind]
    apply ENNReal.tsum_le_tsum
    intro a
    exact mul_le_mul_left (h a) _
  bind_mono_right {_ _} {p f₁ f₂} h b := by
    simp only [Bind.bind, bind]
    apply ENNReal.tsum_le_tsum
    intro a
    exact mul_le_mul_right (h a b) _

/-- The bottom element is minimally defined; the mass sums to 0. -/
instance : Inhabited (SPMF α) where
  default := Bot.bot

noncomputable instance : RandomChoice SPMF where
  choose lo hi h := by
    let n : ℕ := hi - lo + 1
    refine ⟨fun a => if lo ≤ a ∧ a ≤ hi then 1 / n else 0, ?pf⟩
    have hn : n ≠ 0 := Nat.add_one_ne_zero _
    have hsupp : ∀ a, a ∉ Finset.Icc lo hi → (if lo ≤ a ∧ a ≤ hi then (1 : ℝ≥0∞) / n else 0) = 0 := by
      intro a ha
      simp only [Finset.mem_Icc, not_and, not_le] at ha
      by_cases hlo : lo ≤ a
      · have := ha hlo; simp [hlo, Nat.not_le.mpr this]
      · simp [hlo]
    calc ∑' a, if lo ≤ a ∧ a ≤ hi then (1 : ℝ≥0∞) / n else 0
      _ = ∑ a ∈ Finset.Icc lo hi, if lo ≤ a ∧ a ≤ hi then (1 : ℝ≥0∞) / n else 0 :=
          tsum_eq_sum hsupp
      _ = ∑ _a ∈ Finset.Icc lo hi, (1 : ℝ≥0∞) / n :=
          Finset.sum_congr rfl (fun x hx => by simp [Finset.mem_Icc.mp hx])
      _ = (Finset.Icc lo hi).card • (1 / n : ℝ≥0∞) :=
          Finset.sum_const _
      _ = n * (1 / n) := by
          simp only [Nat.card_Icc, nsmul_eq_mul]
          congr 1
          have heq : hi + 1 - lo = hi - lo + 1 := by omega
          exact congrArg Nat.cast heq
      _ = 1 := ENNReal.mul_div_cancel (Nat.cast_ne_zero.mpr hn) (ENNReal.natCast_ne_top n)
      _ ≤ 1 := le_rfl

@[simp]
theorem support_bind
    {x : SPMF α}
    {f : α → SPMF β} :
    (x >>= f).support = {b | ∃ a, a ∈ x.support ∧ b ∈ (f a).support} := by
  ext b
  simp only [support, Function.mem_support, Set.mem_setOf_eq]
  constructor
  · intro h
    by_contra hc
    push_neg at hc
    have hzero : ∀ a, x a * f a b = 0 := fun a => by
      by_cases ha : x a = 0
      · simp [ha]
      · simp [hc a ha]
    apply h
    change (∑' a, x a * f a b) = 0
    simp only [hzero, tsum_zero]
  · intro ⟨a, ha, hb⟩
    apply ne_of_gt
    change 0 < (∑' a', x a' * f a' b)
    calc 0 < x a * f a b := ENNReal.mul_pos ha hb
      _ ≤ ∑' a, x a * f a b := ENNReal.le_tsum a

@[simp]
theorem support_pure :
    (Pure.pure a : SPMF _).support = {a} := by
  classical
  ext x
  simp only [support, Function.mem_support, Set.mem_singleton_iff]
  constructor
  · intro h
    by_contra hne
    apply h
    show (if x = a then (1 : ℝ≥0∞) else 0) = 0
    simp [hne]
  · intro h
    show (if x = a then (1 : ℝ≥0∞) else 0) ≠ 0
    simp [h]

@[simp]
theorem support_choose :
    (choose lo hi h : SPMF _).support = {a | lo ≤ a ∧ a ≤ hi} := by
  ext a
  rw [support, Function.mem_support, Set.mem_setOf_eq]
  simp only [RandomChoice.choose, DFunLike.coe]
  constructor
  · intro ha
    by_contra hc
    push_neg at hc
    apply ha
    by_cases hlo : lo ≤ a
    · simp [hlo, Nat.not_le.mpr (hc hlo)]
    · simp [hlo]
  · intro ⟨hlo, hhi⟩
    simp only [hlo, hhi, and_self, ↓reduceIte, ne_eq, one_div]
    exact ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _)

@[simp]
theorem support_pick
    {x y : SPMF α} :
    (pick (fun () => x) (fun () => y)).support = x.support ∪ y.support := by
  simp only [pick, support_bind, support_choose]
  ext a
  simp only [Set.mem_setOf_eq, Set.mem_union]
  constructor
  · intro ⟨n, ⟨_, hn1⟩, ha⟩
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hn1 with rfl | rfl
    · left; simpa using ha
    · right; simpa using ha
  · intro h
    cases h with
    | inl hx =>
      refine ⟨0, ⟨Nat.zero_le _, Nat.zero_le _⟩, ?_⟩
      simpa using hx
    | inr hy =>
      refine ⟨1, ⟨Nat.zero_le _, le_refl _⟩, ?_⟩
      simpa using hy
/-- The total mass of an SPMF. Always ≤ 1 by definition. -/
noncomputable def mass (p : SPMF α) : ℝ≥0∞ := ∑' a, p a

theorem mass_eq_zero_of_support_empty {p : SPMF α} (h : p.support = ∅) : p.mass = 0 := by
  unfold mass
  rw [ENNReal.tsum_eq_zero]
  intro a
  rw [apply_eq_zero_iff]
  exact Set.eq_empty_iff_forall_notMem.mp h a

/-- An SPMF is a PMF if the mass sums to exactly 1.

We conjecture that, this means that the probability of non-termination is vanishingly small, and
therefore that the generator almost-surely terminates. -/
def IsPMF (p : SPMF α) : Prop := p.mass = 1

theorem pick_apply {x y : SPMF α} (a : α) :
    (pick (fun () => x) (fun () => y)) a = (1/2 : ℝ≥0∞) * x a + (1/2 : ℝ≥0∞) * y a := by
  simp only [pick, Bind.bind, bind]
  -- Work with raw SPMF application (using FunLike coercion)
  show ∑' n, (choose 0 1 pick._proof_1 : SPMF Nat) n *
       (if (n == 0) = true then x else y : SPMF α) a = _
  -- The summand is 0 for all n outside {0, 1}
  have h_supp : ∀ n ∉ Finset.Icc 0 1,
      (choose 0 1 pick._proof_1 : SPMF Nat) n *
      (if (n == 0) = true then x else y : SPMF α) a = 0 := by
    intro n hn
    simp only [Finset.mem_Icc, not_and, not_le] at hn
    have hn' : ¬(0 ≤ n ∧ n ≤ 1) := by push_neg; intro _; omega
    -- choose gives 0 outside its range
    have hzero : (choose 0 1 pick._proof_1 : SPMF Nat) n = 0 := by
      simp only [RandomChoice.choose, instFunLike]
      simp only [hn', ite_false]
    simp only [hzero, zero_mul]
  rw [tsum_eq_sum h_supp]
  -- Sum over Finset.Icc 0 1 = {0, 1}
  have hIcc : Finset.Icc 0 1 = ({0, 1} : Finset Nat) := by decide
  rw [hIcc, Finset.sum_pair (by simp : (0 : Nat) ≠ 1)]
  -- Compute choose 0 and choose 1
  have h0 : (choose 0 1 pick._proof_1 : SPMF Nat) 0 = 1 / 2 := by
    simp only [RandomChoice.choose, instFunLike]
    norm_num
  have h1 : (choose 0 1 pick._proof_1 : SPMF Nat) 1 = 1 / 2 := by
    simp only [RandomChoice.choose, instFunLike]
    norm_num
  simp only [h0, h1, beq_self_eq_true, ite_true, one_ne_zero, beq_iff_eq, ite_false]

theorem tsum_pick {x y : SPMF α} :
    ∑' a, (pick (fun () => x) (fun () => y)) a = (1/2 : ℝ≥0∞) * (∑' a, x a) + (1/2 : ℝ≥0∞) * (∑' a, y a) := by
  simp_rw [pick_apply]
  rw [ENNReal.tsum_add]
  congr 1 <;> rw [ENNReal.tsum_mul_left]

theorem mass_pick {x y : SPMF α} :
    (pick (fun () => x) (fun () => y)).mass = (1/2 : ℝ≥0∞) * x.mass + (1/2 : ℝ≥0∞) * y.mass := tsum_pick

@[simp]
theorem bot_apply (a : α) : Bot.bot (α := SPMF α) a = 0 := rfl

@[simp]
theorem mass_bot : Bot.bot (α := SPMF α).mass = 0 := by
  simp [mass]

@[simp]
theorem bot_bind (f : α → SPMF β) : (Bot.bot (α := SPMF α) >>= f) = Bot.bot := by
  ext b
  simp only [Bind.bind, bind, bot_apply, zero_mul, tsum_zero]
  rfl

theorem mass_eq_zero_iff {x : SPMF α} : x.mass = 0 ↔ x = Bot.bot := by
  constructor
  · intro h
    ext a
    simp only [bot_apply]
    have : ∑' a, x a = 0 := h
    exact (ENNReal.tsum_eq_zero.mp this) a
  · intro h
    simp [h]

theorem IsPMF_pick {x y : SPMF α} (hx : IsPMF x) (hy : IsPMF y) : IsPMF (pick (fun () => x) (fun () => y)) := by
  unfold IsPMF mass at *
  rw [tsum_pick, hx, hy]
  simp only [mul_one]
  exact ENNReal.add_halves 1

theorem mass_pure (a : α) : (Pure.pure a : SPMF α).mass = 1 := by
  unfold mass
  simp only [Pure.pure, pure, DFunLike.coe]
  rw [tsum_eq_single a]
  · simp
  · intro a' ha'
    simp [ha']

theorem IsPMF_pure (a : α) : IsPMF (Pure.pure a : SPMF α) := mass_pure a

theorem mass_bind_pure {x : SPMF α} {f : α → β} :
    (x >>= fun a => Pure.pure (f a)).mass = x.mass := by
  classical
  unfold mass
  simp only [Bind.bind, bind, Pure.pure, pure, DFunLike.coe]
  -- LHS: ∑' b, ∑' a, x a * (if f a = b then 1 else 0)
  -- RHS: ∑' a, x a
  -- Strategy: swap the sums, then for each a, the inner sum over b is just x a
  rw [ENNReal.tsum_comm]
  -- Now: ∑' a, ∑' b, x a * (if f a = b then 1 else 0) = ∑' a, x a
  congr 1
  ext a
  -- For fixed a, only b = f a contributes
  rw [tsum_eq_single (f a)]
  · simp
  · intro b hb
    simp only [mul_ite, mul_one, mul_zero]
    split_ifs with heq
    · simp_all
    · rfl

theorem IsPMF_bind_pure {x : SPMF α} {f : α → β} (hx : IsPMF x) :
    IsPMF (x >>= fun a => Pure.pure (f a)) := by
  unfold IsPMF
  rw [mass_bind_pure, hx]

theorem mass_bind_const {x : SPMF α} {y : SPMF β} :
    (x >>= fun _ => y).mass = x.mass * y.mass := by
  unfold mass
  simp only [Bind.bind, bind, DFunLike.coe]
  rw [ENNReal.tsum_comm]
  simp_rw [ENNReal.tsum_mul_left]
  rw [← ENNReal.tsum_mul_right]

theorem mass_bind_of_const_mass {x : SPMF α} {f : α → SPMF β} {c : ℝ≥0∞}
    (hx : IsPMF x) (hf : ∀ a, (f a).mass = c) :
    (x >>= f).mass = c := by
  unfold mass IsPMF at *
  simp only [Bind.bind, bind, DFunLike.coe]
  rw [ENNReal.tsum_comm]
  calc ∑' a, ∑' b, x a * (f a) b
    _ = ∑' a, x a * (∑' b, (f a) b) := by simp_rw [ENNReal.tsum_mul_left]
    _ = ∑' a, x a * c := by simp_rw [hf]
    _ = c * ∑' a, x a := by rw [ENNReal.tsum_mul_right]; ring
    _ = c * 1 := by unfold mass at hx; rw [hx]
    _ = c := by ring

theorem mass_bind {x : SPMF α} {f : α → SPMF β} (hf : ∀ a, IsPMF (f a)) :
    (x >>= f).mass = x.mass := by
  unfold IsPMF mass at *
  simp only [Bind.bind, bind, DFunLike.coe]
  rw [ENNReal.tsum_comm]
  simp_rw [ENNReal.tsum_mul_left]
  calc ∑' a, x a * ∑' b, (f a) b
    _ = ∑' a, x a * 1 := by simp_rw [hf]
    _ = ∑' a, x a := by simp

theorem IsPMF_bind {x : SPMF α} {f : α → SPMF β} (hx : IsPMF x) (hf : ∀ a, IsPMF (f a)) :
    IsPMF (x >>= f) := by
  unfold IsPMF
  rw [mass_bind hf, hx]

theorem mass_eq_one_of_half_plus_half_self {p : SPMF α}
    (h : p.mass = 1/2 + 1/2 * p.mass) : p.mass = 1 := by
  have hle : p.mass ≤ 1 := p.tsum_coe
  have hne_top : p.mass ≠ ⊤ := ne_of_lt (lt_of_le_of_lt hle ENNReal.one_lt_top)
  -- From h: mass = 1/2 + 1/2 * mass
  -- Multiply both sides by 2: 2 * mass = 1 + mass
  -- So: mass = 1
  have h2ne0 : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have h2netop : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
  have h12 : (1/2 : ℝ≥0∞) * 2 = 1 := ENNReal.div_mul_cancel h2ne0 h2netop
  -- Compute 2 * (1/2 + 1/2 * mass)
  have hmul : 2 * p.mass = 1 + p.mass := by
    conv_lhs => rw [h]
    calc 2 * (1/2 + 1/2 * p.mass)
      _ = 2 * (1/2) + 2 * (1/2 * p.mass) := by rw [mul_add]
      _ = 2 * (1/2) + 2 * (1/2) * p.mass := by rw [mul_assoc]
      _ = 1 + 1 * p.mass := by rw [mul_comm 2 (1/2), h12]
      _ = 1 + p.mass := by rw [one_mul]
  -- Now hmul : 2 * p.mass = 1 + p.mass
  -- So: 2 * mass - mass = 1
  have hsub : 2 * p.mass - p.mass = 1 := by
    rw [hmul]
    exact ENNReal.add_sub_cancel_right hne_top
  -- And 2 * mass - mass = mass
  have hlhs : 2 * p.mass - p.mass = p.mass := by
    have : (2 : ℝ≥0∞) * p.mass = p.mass + p.mass := by ring
    rw [this]
    exact ENNReal.add_sub_cancel_left hne_top
  rw [hlhs] at hsub
  exact hsub

theorem IsPMF_pick_pure_of_mass_eq {a : α} {body : SPMF α} {full : SPMF α}
    (h_eq : full = pick (fun () => Pure.pure a) (fun () => body))
    (h_mass : body.mass = full.mass) : IsPMF full := by
  unfold IsPMF
  apply mass_eq_one_of_half_plus_half_self
  calc full.mass
    _ = (pick (fun () => Pure.pure a) (fun () => body)).mass := by rw [h_eq]
    _ = 1/2 * (Pure.pure a : SPMF α).mass + 1/2 * body.mass := mass_pick
    _ = 1/2 * 1 + 1/2 * body.mass := by rw [mass_pure]
    _ = 1/2 + 1/2 * full.mass := by rw [h_mass]; ring

end SPMF
