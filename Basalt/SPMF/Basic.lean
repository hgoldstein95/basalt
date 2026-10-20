/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
module

public import Mathlib.MeasureTheory.Measure.Dirac
public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import Basalt.RandomChoice

/-!
# Sub-Probability Mass Functions

This file defines a type of sub-probability mass functions, similar to `PMF` from Mathlib, with its
`support` (the values with nonzero mass) and its `mass` (the total probability of producing a value,
as opposed to diverging — always ≤ 1).
-/

@[expose] public section

open Lean.Order RandomChoice NNReal ENNReal MeasureTheory

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

theorem coe_le_one (p : SPMF α) (a : α) : p a ≤ 1 := by
  have h₁ := p.tsum_coe
  have h₂ := ENNReal.le_tsum (f := p) a
  grind only

theorem apply_ne_top (p : SPMF α) (a : α) : p a ≠ ∞ :=
  ne_of_lt (lt_of_le_of_lt (p.coe_le_one a) ENNReal.one_lt_top)

instance : Lean.Order.PartialOrder (SPMF α) where
  rel p q := ∀ a, p a ≤ q a
  rel_refl := by grind
  rel_trans := by grind
  rel_antisymm h₁ h₂ := by ext; grind

/-- The supremum of a chain is the SPMF where each point is maximally defined. -/
noncomputable def csupFun {α : Type u} (c : Set (SPMF α)) : α → ℝ≥0∞ :=
  fun a => ⨆ f ∈ c, f a

/-- A sum of suprema along a chain is at most the supremum of the sums. -/
theorem tsum_iSup₂_le_of_chain {c : SPMF α → Prop} (hc : chain c) (g : SPMF α → α → ℝ≥0∞)
    (hg : ∀ p q, p ⊑ q → ∀ a, g p a ≤ g q a) :
    ∑' a, ⨆ p, ⨆ (_ : c p), g p a ≤ ⨆ p, ⨆ (_ : c p), ∑' a, g p a := by
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun s => ?_
  simp_rw [iSup_subtype']
  rw [ENNReal.finsetSum_iSup fun ⟨p, hp⟩ ⟨q, hq⟩ => (hc p q hp hq).elim
    (fun h => ⟨⟨q, hq⟩, fun a => ⟨hg p q h a, le_rfl⟩⟩)
    (fun h => ⟨⟨p, hp⟩, fun a => ⟨le_rfl, hg q p h a⟩⟩)]
  exact iSup_mono fun _ => ENNReal.sum_le_tsum s

/-- `csupFun` is a valid SPMF. -/
theorem csupFun_sum_le_one {c : Set (SPMF α)} (h_chain : chain c) : (∑' a, csupFun c a) ≤ 1 :=
  (tsum_iSup₂_le_of_chain h_chain (fun p a => p a) fun _ _ h => h).trans
    (iSup₂_le fun p _ => p.tsum_coe)

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

section operations

/-- A dirac distribution; all of the mass is on `a`. -/
noncomputable def pure (a : α) : SPMF α :=
  open Classical in
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


theorem tsum_subtype_Icc (lo hi : Nat) (f : Nat → ℝ≥0∞) :
    ∑' (m : ULift.{u} {x : Nat // lo ≤ x ∧ x ≤ hi}), f m.down.val
      = ∑ n ∈ Finset.Icc lo hi, f n := by
  calc ∑' (m : ULift.{u} {x : Nat // lo ≤ x ∧ x ≤ hi}), f m.down.val
      = ∑' (n : ↥(Finset.Icc lo hi)), f n.val :=
        Equiv.tsum_eq
          (({ toFun := fun m => ⟨m.down.val, Finset.mem_Icc.mpr m.down.property⟩
              invFun := fun n => ⟨⟨n.val, Finset.mem_Icc.mp n.property⟩⟩
              left_inv := fun _ => rfl
              right_inv := fun _ => rfl } :
            ULift.{u} {x : Nat // lo ≤ x ∧ x ≤ hi} ≃ ↥(Finset.Icc lo hi)))
          (fun n : ↥(Finset.Icc lo hi) => f n.val)
    _ = ∑ n ∈ Finset.Icc lo hi, f n := Finset.tsum_subtype _ _

theorem tsum_subtype_Icc_const (lo hi : Nat) (c : ℝ≥0∞) :
    ∑' (_ : ULift {x : Nat // lo ≤ x ∧ x ≤ hi}), c = (Finset.Icc lo hi).card * c := by
  rw [tsum_subtype_Icc lo hi fun _ => c, Finset.sum_const, nsmul_eq_mul]

theorem card_Icc_eq (lo hi : Nat) (h : lo ≤ hi) :
    (Finset.Icc lo hi).card = hi - lo + 1 := by
  rw [Nat.card_Icc]; omega

noncomputable instance : RandomChoice SPMF where
  choose lo hi h := by
    let n : ℕ := hi - lo + 1
    refine ⟨fun _ => 1 / n, ?pf⟩
    have hn : n ≠ 0 := Nat.add_one_ne_zero _
    calc ∑' (_ : ULift {x : Nat // lo ≤ x ∧ x ≤ hi}), (1 / n : ℝ≥0∞)
      _ = (Finset.Icc lo hi).card * (1 / n : ℝ≥0∞) := tsum_subtype_Icc_const lo hi _
      _ = (n : ℝ≥0∞) * (1 / n) := by rw [card_Icc_eq lo hi h]
      _ = 1 := ENNReal.mul_div_cancel (Nat.cast_ne_zero.mpr hn) (ENNReal.natCast_ne_top n)
      _ ≤ 1 := le_rfl

end operations

section operation_uses

private lemma bot_apply (a : α) : Bot.bot (α := SPMF α) a = 0 := rfl

end operation_uses

section equations

theorem pure_bind (a : α) (f : α → SPMF β) : bind (pure a) f = f a := by
  ext b
  simp only [bind, pure, DFunLike.coe]
  rw [tsum_eq_single a]
  · simp
  · intro b' hb; simp [hb]

theorem bind_pure (p : SPMF α) : bind p pure = p := by
  ext b
  simp only [bind, pure, DFunLike.coe]
  rw [tsum_eq_single b]
  · simp
  · intro b' hb
    simp [Ne.symm hb]

theorem bind_assoc (m : SPMF α) (f : α → SPMF β) (g : β → SPMF γ) :
    bind (bind m f) g = bind m (fun x => bind (f x) g) := by
  ext c
  simp only [bind, DFunLike.coe]
  trans ∑' (b : β) (a : α), m a * f a b * g b c
  · congr; ext b
    rw [ENNReal.tsum_mul_right]
    rfl
  rw [ENNReal.tsum_comm]
  congr; ext a
  rw [← ENNReal.tsum_mul_left]
  congr; ext b
  rw [mul_assoc]
  rfl

instance instLawfulMonadSPMF : LawfulMonad SPMF := LawfulMonad.mk' _
  (id_map := bind_pure) (pure_bind := pure_bind) (bind_assoc := bind_assoc)

theorem bind_apply {x : SPMF α} {f : α → SPMF β} (b : β) :
    (x >>= f) b = ∑' a, x a * (f a) b := rfl

open Classical in
@[simp]
theorem pure_apply (a a' : α) :
    (Pure.pure a : SPMF α) a' = if a' = a then 1 else 0 := rfl

theorem choose_apply (lo hi : Nat) (h : lo ≤ hi) (m : ULift {x : Nat // lo ≤ x ∧ x ≤ hi}) :
    (choose lo hi h : SPMF (ULift {x : Nat // lo ≤ x ∧ x ≤ hi})) m
      = 1 / ((hi - lo + 1 : ℕ) : ℝ≥0∞) := rfl

theorem default_apply (a : α) : (default : SPMF α) a = 0 := rfl

@[simp]
theorem bot_bind (f : α → SPMF β) : (Bot.bot (α := SPMF α) >>= f) = Bot.bot := by
  ext b
  simp only [Bind.bind, bind, bot_apply, zero_mul, tsum_zero]
  rfl

end equations

section support

/-- The support of an `SPMF` is the set of values that have nonzero mass. -/
def support (p : SPMF α) : Set α := Function.support p

theorem mem_support_iff (p : SPMF α) (a : α) : a ∈ p.support ↔ p a ≠ 0 := Iff.rfl

/-- `SPMF.bind` is the monad's `>>=`. -/
theorem bind_eq (x : SPMF α) (f : α → SPMF β) : x.bind f = x >>= f := rfl

/-- `SPMF.pure` is the monad's `pure`. -/
theorem pure_eq (a : α) : (SPMF.pure a : SPMF α) = Pure.pure a := rfl

@[simp]
theorem support_countable (p : SPMF α) : p.support.Countable :=
  Summable.countable_support_ennreal (tsum_coe_ne_top p)

theorem apply_eq_zero_iff (p : SPMF α) (a : α) : p a = 0 ↔ a ∉ p.support := by
  rw [mem_support_iff, Classical.not_not]

theorem apply_pos_iff (p : SPMF α) (a : α) : 0 < p a ↔ a ∈ p.support :=
  pos_iff_ne_zero.trans (p.mem_support_iff a).symm

theorem csup_apply {c : SPMF α → Prop} (hc : chain c) (a : α) :
    (CCPO.csup hc) a = ⨆ f, ⨆ (_ : c f), f a := by
  have hge : ∀ b, ⨆ f, ⨆ (_ : c f), f b ≤ (CCPO.csup hc) b :=
    fun b => iSup₂_le (fun f hf => le_csup hc hf b)
  have hsum : ∑' b, ⨆ f, ⨆ (_ : c f), f b ≤ 1 :=
    (ENNReal.tsum_le_tsum hge).trans (tsum_coe _)
  exact le_antisymm
    ((csup_le hc (fun f hf b => le_iSup₂_of_le f hf le_rfl) :
        CCPO.csup hc ⊑ ⟨fun b => ⨆ f, ⨆ (_ : c f), f b, hsum⟩) a)
    (hge a)

end support

section mass

/-- The total mass of an SPMF. Always ≤ 1 by definition. -/
noncomputable def mass (p : SPMF α) : ℝ≥0∞ := ∑' a, p a

theorem mass_le_one (p : SPMF α) : p.mass ≤ 1 := p.tsum_coe

end mass

end SPMF
