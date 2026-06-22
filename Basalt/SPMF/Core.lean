/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
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
  coe_injective _ _ h := Subtype.ext h

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

theorem coe_le_one (p : SPMF α) (a : α) : p a ≤ 1 := by
  have h₁ := p.tsum_coe
  have h₂ := ENNReal.le_tsum (f := p) a
  grind only

theorem apply_ne_top (p : SPMF α) (a : α) : p a ≠ ∞ :=
  ne_of_lt (lt_of_le_of_lt (p.coe_le_one a) ENNReal.one_lt_top)

theorem apply_lt_top (p : SPMF α) (a : α) : p a < ∞ :=
  lt_of_le_of_ne le_top (p.apply_ne_top a)

instance : Lean.Order.PartialOrder (SPMF α) where
  rel p q := ∀ a, p a ≤ q a
  rel_refl := by grind
  rel_trans := by grind
  rel_antisymm h₁ h₂ := by ext; grind

/-- The supremum of a chain is the SPMF where each point is maximally defined. -/
noncomputable def csupFun {α : Type u} (c : Set (SPMF α)) : α → ℝ≥0∞ :=
  fun a => ⨆ f ∈ c, f a

/-- `csupFun` is a valid SPMF. -/
theorem csupFun_sum_le_one
  {c : Set (SPMF α)}
  (h_chain : chain c) :
  (∑' a, csupFun c a) ≤ 1 := by
  by_cases hc : c = ∅
  case pos =>
    simp [csupFun, hc]
  case neg =>
    have h_directed : DirectedOn (· ⊑ ·) c := fun x hx y hy => by
      rcases h_chain x y hx hy with h | h
      · exact ⟨y, hy, h, PartialOrder.rel_refl⟩
      · exact ⟨x, hx, PartialOrder.rel_refl, h⟩
    have h_directed_le : DirectedOn (fun f g => ∀ a, f a ≤ g a) c := fun x hx y hy => by
      rcases h_directed x hx y hy with ⟨z, hz, hxz, hyz⟩
      exact ⟨z, hz, hxz, hyz⟩
    calc ∑' a, csupFun c a
      _ = ⨆ s : Finset α, ∑ a ∈ s, csupFun c a := ENNReal.tsum_eq_iSup_sum
      _ = ⨆ s : Finset α, ∑ a ∈ s, ⨆ f ∈ c, f a := rfl
      _ ≤ ⨆ s : Finset α, ⨆ f ∈ c, ∑ a ∈ s, f a := by
          apply iSup_mono
          intro s
          simp_rw [iSup_subtype']
          rw [ENNReal.finsetSum_iSup]
          intro ⟨f, hf⟩ ⟨g, hg⟩
          rcases h_directed_le f hf g hg with ⟨k, hk, hfk, hgk⟩
          exact ⟨⟨k, hk⟩, fun a => ⟨hfk a, hgk a⟩⟩
      _ = ⨆ f ∈ c, ⨆ s : Finset α, ∑ a ∈ s, f a := by
          rw [iSup_comm]
          congr 1
          ext f
          rw [iSup_comm]
      _ = ⨆ f ∈ c, ∑' a, f a := by
          congr 1; ext f; congr 1; ext _
          exact ENNReal.tsum_eq_iSup_sum.symm
      _ ≤ 1 := by simp

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

theorem tsum_subtype_Icc_const (lo hi : Nat) (c : ℝ≥0∞) :
    ∑' (_ : ULift {x : Nat // lo ≤ x ∧ x ≤ hi}), c = (Finset.Icc lo hi).card * c := by
  have e : ULift {x : Nat // lo ≤ x ∧ x ≤ hi} ≃ ↥(Finset.Icc lo hi) :=
    Equiv.ulift.trans (Equiv.subtypeEquivRight (fun a => (Finset.mem_Icc).symm))
  calc ∑' (_ : ULift {x : Nat // lo ≤ x ∧ x ≤ hi}), c
      = ∑' (_ : ↥(Finset.Icc lo hi)), c := Equiv.tsum_eq e (fun _ => c)
    _ = ∑ _ ∈ Finset.Icc lo hi, c := Finset.tsum_subtype (Finset.Icc lo hi) (fun _ => c)
    _ = (Finset.Icc lo hi).card * c := by rw [Finset.sum_const, nsmul_eq_mul]

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

private lemma pick_apply {α : Type u} {x y : SPMF α} (a : α) :
    (pick (fun () => x) (fun () => y)) a =
    (1/2 : ℝ≥0∞) * x a + (1/2 : ℝ≥0∞) * y a := by
  simp only [pick, Bind.bind, bind]
  show ∑' (n : ULift {x : Nat // 0 ≤ x ∧ x ≤ 1}),
       (choose 0 1 (by simp) : SPMF (ULift {x : Nat // 0 ≤ x ∧ x ≤ 1})) n *
       (if (n.down.val == 0) = true then x else y : SPMF α) a = _
  let e0 : ULift {x : Nat // 0 ≤ x ∧ x ≤ 1} := ⟨⟨0, by omega⟩⟩
  let e1 : ULift {x : Nat // 0 ≤ x ∧ x ≤ 1} := ⟨⟨1, by omega⟩⟩
  have hne : e0 ≠ e1 := by
    intro heq
    have : (0 : Nat) = 1 := congrArg (fun z => z.down.val) heq
    omega
  have h_supp : ∀ n : ULift {x : Nat // 0 ≤ x ∧ x ≤ 1}, n ∉ ({e0, e1} : Finset _) →
      (choose 0 1 (by simp) : SPMF (ULift {x : Nat // 0 ≤ x ∧ x ≤ 1})) n *
      (if (n.down.val == 0) = true then x else y : SPMF α) a = 0 := by
    intro n hn
    exfalso
    apply hn
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp n.down.property.2 with h0 | h1
    · exact Or.inl (ULift.down_injective (Subtype.ext h0))
    · exact Or.inr (ULift.down_injective (Subtype.ext h1))
  rw [tsum_eq_sum h_supp, Finset.sum_pair hne]
  rfl

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

instance instLawfulMonadSPMF : LawfulMonad SPMF where
  bind_pure_comp := by intros; rfl
  bind_map := by intros; rfl
  pure_bind := pure_bind
  bind_assoc := bind_assoc
  map_const := by intros; rfl
  id_map := bind_pure
  seqLeft_eq := by
    intros
    simp only [SeqLeft.seqLeft, Seq.seq, Functor.map]
    unfold Function.comp Function.const
    rw [bind_assoc]
    simp [pure_bind]
  seqRight_eq := by
    intros
    simp only [SeqRight.seqRight, Seq.seq, Functor.map]
    unfold Function.comp Function.const
    rw [bind_assoc]
    simp [pure_bind, bind_pure]
  pure_seq := by
    intros
    simp only [Seq.seq, Functor.map, Pure.pure]
    unfold Function.comp
    simp [pure_bind]

theorem bind_pick {α β} (x y : SPMF α) (f : α → SPMF β) :
    (pick (fun () => x) (fun () => y) >>= f) = pick (fun _ => x >>= f) (fun _ => y >>= f) := by
  apply SPMF.ext
  intro b
  simp only [pick_apply, bind, SPMF.bind, Bind.bind]
  simp only [ENNReal.tsum_add, add_mul, ENNReal.tsum_mul_left, mul_assoc]
  rfl

theorem tsum_pick {x y : SPMF α} :
    ∑' a, (pick (fun () => x) (fun () => y)) a = (1/2 : ℝ≥0∞) * (∑' a, x a) + (1/2 : ℝ≥0∞) * (∑' a, y a) := by
  simp_rw [pick_apply]
  rw [ENNReal.tsum_add]
  congr 1 <;> rw [ENNReal.tsum_mul_left]

@[simp]
theorem bot_bind (f : α → SPMF β) : (Bot.bot (α := SPMF α) >>= f) = Bot.bot := by
  ext b
  simp only [Bind.bind, bind, bot_apply, zero_mul, tsum_zero]
  rfl

end equations

end SPMF
