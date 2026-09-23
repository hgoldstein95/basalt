/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt.SPMF
import Basalt.RandomChoice

open RandomChoice

/-!
# Cost-Tracking SPMF

`SPMF.Cost` interprets a generator as a distribution over (value, number of random choices) pairs,
and `IsBounded` says every value is produced within a given choice budget — enabling proofs like "a
list generator makes `O(|xs|)` choices to generate `xs`."
-/

namespace SPMF

/-- A cost-tracking SPMF: pairs each output with the number of random choices made. -/
abbrev Cost (α : Type u) : Type u := SPMF (α × Nat)

end SPMF

namespace SPMF.Cost

instance instInhabited : Inhabited (SPMF.Cost α) where
  -- default = ⊥, the empty-support SPMF
  default := @Bot.bot (SPMF (α × Nat)) _

noncomputable instance instMonad : Monad SPMF.Cost where
  pure a := (SPMF.pure (a, 0) : SPMF _)
  bind m f :=
    SPMF.bind m fun pair =>
      SPMF.bind (f pair.1) fun pair2 =>
        SPMF.pure (pair2.1, pair.2 + pair2.2)

section CCPO

open Lean.Order

instance instPartialOrder : Lean.Order.PartialOrder (SPMF.Cost α) where
  rel p q := @PartialOrder.rel (SPMF (α × Nat)) _ p q
  rel_refl := @PartialOrder.rel_refl (SPMF (α × Nat)) _
  rel_trans := @PartialOrder.rel_trans (SPMF (α × Nat)) _
  rel_antisymm := @PartialOrder.rel_antisymm (SPMF (α × Nat)) _

instance instCCPO : CCPO (SPMF.Cost α) where
  has_csup := by
    intros c hc
    exact @CCPO.has_csup (SPMF (α × Nat)) _ c hc

instance instMonoBind : MonoBind SPMF.Cost where
  bind_mono_left {α β} {m₁ m₂ : SPMF.Cost α} {f : α → SPMF.Cost β} (h : m₁ ⊑ m₂) := by
    intro pair
    simp only [Bind.bind, bind]
    unfold SPMF.bind
    apply ENNReal.tsum_le_tsum
    intro ⟨a, n₁⟩
    simp only [Lean.Order.PartialOrder.rel] at h
    gcongr
    exact h (a, n₁)
  bind_mono_right {α β} {m : SPMF.Cost α} {f₁ f₂ : α → SPMF.Cost β} (h : ∀ a, f₁ a ⊑ f₂ a) := by
    intro pair
    simp only [Bind.bind, bind]
    unfold SPMF.bind
    simp only [Lean.Order.PartialOrder.rel] at h ⊢
    apply ENNReal.tsum_le_tsum
    intro ⟨a, n₁⟩
    gcongr ?_ * ?_
    apply ENNReal.tsum_le_tsum
    intro i
    gcongr ?_ * ?_
    apply h

end CCPO

noncomputable instance instRandomChoice : RandomChoice SPMF.Cost where
  choose lo hi h := by
    exact SPMF.bind (choose lo hi h : SPMF (ULift {x : Nat // lo ≤ x ∧ x ≤ hi}))
      fun n => SPMF.pure (n, 1)

section support

@[simp]
theorem mem_support_pure_iff {a b : α} {n : Nat} :
    (b, n) ∈ (Pure.pure a : SPMF.Cost α).support ↔ b = a ∧ n = 0 := by
  have : (Pure.pure a : SPMF.Cost α) = (Pure.pure (a, 0) : SPMF _) := rfl
  simp [this, Prod.mk.injEq]

@[simp]
theorem mem_support_bind_iff
    {m : SPMF.Cost α} {f : α → SPMF.Cost β} {b : β} {n : Nat} :
    (b, n) ∈ (m >>= f).support ↔
    ∃ a n1 n2, (a, n1) ∈ m.support ∧ (b, n2) ∈ (f a).support ∧ n = n1 + n2 := by
  have : (m >>= f : SPMF.Cost β) =
      SPMF.bind m fun pair =>
        SPMF.bind (f pair.1) fun pair2 =>
          SPMF.pure (pair2.1, pair.2 + pair2.2) := rfl
  rw [this]
  simp only [SPMF.bind_eq, SPMF.pure_eq, SPMF.mem_support_bind_iff, SPMF.mem_support_pure_iff,
    Prod.mk.injEq]
  constructor
  · rintro ⟨⟨a, n1⟩, hmem1, ⟨b', n2⟩, hmem2, rfl, h_n⟩
    exact ⟨a, n1, n2, hmem1, hmem2, h_n⟩
  · rintro ⟨a, n1, n2, hmem1, hmem2, rfl⟩
    exact ⟨⟨a, n1⟩, hmem1, ⟨b, n2⟩, hmem2, rfl, rfl⟩

@[simp]
theorem mem_support_choose_iff
    {lo hi : Nat} {h : lo ≤ hi} {n : ULift {x : Nat // lo ≤ x ∧ x ≤ hi}} {c : Nat} :
    (n, c) ∈ (choose lo hi h : SPMF.Cost (ULift {x : Nat // lo ≤ x ∧ x ≤ hi})).support ↔ c = 1 := by
  have : (choose lo hi h : SPMF.Cost (ULift {x : Nat // lo ≤ x ∧ x ≤ hi})) =
      SPMF.bind (choose lo hi h : SPMF (ULift {x : Nat // lo ≤ x ∧ x ≤ hi}))
        fun k => SPMF.pure (k, 1) := rfl
  rw [this]
  simp only [SPMF.bind_eq, SPMF.pure_eq, SPMF.mem_support_bind_iff, SPMF.mem_support_choose_iff,
             SPMF.mem_support_pure_iff, Prod.mk.injEq, true_and]
  constructor
  · rintro ⟨k, rfl, rfl⟩
    rfl
  · rintro rfl
    exact ⟨n, rfl, rfl⟩

@[simp]
theorem mem_support_map_iff {m : SPMF.Cost α} {f : α → β} {b : β} {n : Nat} :
    (b, n) ∈ (f <$> m).support ↔ ∃ a, (a, n) ∈ m.support ∧ b = f a := by
  have : (f <$> m : SPMF.Cost β) = m >>= fun a => Pure.pure (f a) := rfl
  rw [this]
  simp only [mem_support_bind_iff, mem_support_pure_iff]
  constructor
  · rintro ⟨a, n1, n2, hmem, ⟨rfl, rfl⟩, rfl⟩
    exact ⟨a, by simpa using hmem, rfl⟩
  · rintro ⟨a, hmem, rfl⟩
    exact ⟨a, n, 0, hmem, ⟨rfl, rfl⟩, rfl⟩

/-- Support inversion for `pick` at the cost interpretation: a branch draw plus one choice. -/
@[simp]
theorem mem_support_pick_iff {x y : Unit → SPMF.Cost α} {a : α} {n : Nat} :
    (a, n) ∈ (pick x y).support ↔
      ∃ m, n = 1 + m ∧ ((a, m) ∈ (x ()).support ∨ (a, m) ∈ (y ()).support) := by
  unfold RandomChoice.pick
  simp only [SPMF.Cost.mem_support_bind_iff, SPMF.Cost.mem_support_choose_iff]
  constructor
  · rintro ⟨k, n1, n2, h1, h2, rfl⟩
    subst h1
    refine ⟨n2, rfl, ?_⟩
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp k.down.property.2 with h0 | h1
    · left; simpa [h0] using h2
    · right
      have : (k.down.val == 0) = false := by simp [h1]
      simpa [this] using h2
  · rintro ⟨m, rfl, h | h⟩
    · exact ⟨⟨⟨0, by omega⟩⟩, 1, m, rfl, by simpa using h, rfl⟩
    · exact ⟨⟨⟨1, by omega⟩⟩, 1, m, rfl, by simpa using h, rfl⟩

@[simp]
theorem mem_support_chooseNat_iff {lo hi : Nat} {h : lo ≤ hi} {n c : Nat} :
    (n, c) ∈ (chooseNat lo hi h : SPMF.Cost Nat).support ↔ (lo ≤ n ∧ n ≤ hi) ∧ c = 1 := by
  unfold chooseNat
  simp only [mem_support_map_iff, mem_support_choose_iff]
  constructor
  · rintro ⟨a, rfl, rfl⟩
    exact ⟨a.down.property, rfl⟩
  · rintro ⟨⟨h1, h2⟩, rfl⟩
    exact ⟨⟨⟨n, h1, h2⟩⟩, rfl, rfl⟩

@[simp]
theorem mem_support_chooseInt_iff {lo hi : Int} {h : lo ≤ hi} {n : Int} {c : Nat} :
    (n, c) ∈ (chooseInt lo hi h : SPMF.Cost Int).support ↔ (lo ≤ n ∧ n ≤ hi) ∧ c = 1 := by
  unfold chooseInt
  simp only [mem_support_bind_iff, mem_support_pure_iff, mem_support_chooseNat_iff]
  constructor
  · rintro ⟨k, n1, n2, ⟨⟨-, hk⟩, rfl⟩, ⟨rfl, rfl⟩, rfl⟩
    exact ⟨by omega, rfl⟩
  · rintro ⟨⟨h1, h2⟩, rfl⟩
    exact ⟨(n - lo).toNat, 1, 0, ⟨⟨Nat.zero_le _, by omega⟩, rfl⟩, ⟨by omega, rfl⟩, rfl⟩

end support

end SPMF.Cost

open SPMF.Cost

/-- A cost-tracking generator `x` `IsBounded` by a cost function `f` if every output `a` it can
produce is produced with at most `f a` random choices. -/
def IsBounded (x : SPMF.Cost α) (f : α → Nat) : Prop :=
  ∀ p ∈ SPMF.support x, p.2 ≤ f p.1

/-- `IsBounded`, unfolded to its definition. Useful with `rw` and `simp`. -/
theorem IsBounded_iff {x : SPMF.Cost α} {f : α → Nat} :
    IsBounded x f ↔
    ∀ p ∈ SPMF.support x, p.2 ≤ f p.1 := Iff.rfl

theorem IsBounded_mono
    (hc₁ : IsBounded x c₁)
    (h : ∀ a, c₁ a ≤ c₂ a) :
    IsBounded x c₂ := by
  simp_all only [IsBounded_iff]
  grind

namespace SPMF.Cost

section expectation

open scoped ENNReal

/-- The expected number of random choices a cost-tracking generator makes. -/
noncomputable def expectedCost (g : SPMF.Cost α) : ℝ≥0∞ :=
  SPMF.expect g (fun p => (p.2 : ℝ≥0∞))

theorem expect_pure (a : α) (φ : α × Nat → ℝ≥0∞) :
    SPMF.expect (Pure.pure a : SPMF.Cost α) φ = φ (a, 0) := by
  have h : (Pure.pure a : SPMF.Cost α) = (Pure.pure (a, 0) : SPMF (α × Nat)) := rfl
  rw [h, SPMF.expect_pure]

/-- The tower rule at the cost interpretation: the two stages' costs add. -/
theorem expect_bind (m : SPMF.Cost α) (f : α → SPMF.Cost β) (φ : β × Nat → ℝ≥0∞) :
    SPMF.expect (m >>= f : SPMF.Cost β) φ
      = SPMF.expect m (fun p => SPMF.expect (f p.1) (fun q => φ (q.1, p.2 + q.2))) := by
  have h : (m >>= f : SPMF.Cost β)
      = SPMF.bind m fun p => SPMF.bind (f p.1) fun q => SPMF.pure (q.1, p.2 + q.2) := rfl
  rw [h, SPMF.bind_eq, SPMF.expect_bind]
  congr 1
  funext p
  rw [SPMF.bind_eq, SPMF.expect_bind]
  congr 1
  funext q
  rw [SPMF.pure_eq, SPMF.expect_pure]

theorem expect_pick (x y : Unit → SPMF.Cost α) (φ : α × Nat → ℝ≥0∞) :
    SPMF.expect (pick x y : SPMF.Cost α) φ
      = (1/2 : ℝ≥0∞) * SPMF.expect (x ()) (fun p => φ (p.1, 1 + p.2))
        + (1/2 : ℝ≥0∞) * SPMF.expect (y ()) (fun p => φ (p.1, 1 + p.2)) := by
  unfold RandomChoice.pick
  rw [expect_bind]
  have hch : (choose 0 1 (by simp) : SPMF.Cost (ULift {n : Nat // 0 ≤ n ∧ n ≤ 1}))
      = SPMF.bind (choose 0 1 (by simp) : SPMF (ULift {n : Nat // 0 ≤ n ∧ n ≤ 1}))
          (fun n => SPMF.pure (n, 1)) := rfl
  rw [hch, SPMF.bind_eq, SPMF.expect_bind]
  simp only [SPMF.pure_eq, SPMF.expect_pure]
  rw [SPMF.expect_choose (Nat.zero_le 1) _
    (fun k => if k == 0 then SPMF.expect (x ()) (fun p => φ (p.1, 1 + p.2))
              else SPMF.expect (y ()) (fun p => φ (p.1, 1 + p.2)))
    (fun a => by by_cases h : (a.down.val == 0) = true <;> simp [h])]
  have hIcc : Finset.Icc 0 1 = ({0, 1} : Finset ℕ) := by decide
  rw [hIcc, Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [Nat.sub_zero, beq_self_eq_true, if_pos, Nat.one_ne_zero, beq_iff_eq]
  norm_num
  rw [ENNReal.add_div]
  congr 1 <;> rw [ENNReal.div_eq_inv_mul]

/-- A worst-case cost law bounds the average: `expectedCost` is at most the expected bound. -/
theorem expectedCost_le_of_IsBounded {g : SPMF.Cost α} {c : α → Nat} (h : IsBounded g c) :
    expectedCost g ≤ SPMF.expect g (fun p => (c p.1 : ℝ≥0∞)) := by
  refine SPMF.expect_mono_support fun p hp => ?_
  exact_mod_cast h p hp

end expectation

end SPMF.Cost
