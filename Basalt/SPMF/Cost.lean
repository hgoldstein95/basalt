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

This file provides a modified interpretation of a `Gen` that ascribes cost to each choice a
generator makes. This allows us to prove things like "a list generator makes `O(|xs|)` choices when
generating a list `xs`."

NOTE: Right now there is more infrastructure here than is strictly needed for the proofs in
`Examples/`. In particular, we do not need the full power of the coupling relation, and can work
instead with the simpler definition provided by `IsBounded_iff`.

## Main Definitions

- `SPMF.Cost` — A cost interpretation for a generator.
- `IsBounded` — A proposition that says a generator makes a bounded number of choices.

## Main Theorems

- `IsBounded_iff` — Relates the more complicated definition of boundedness (using couplings) to a
  simpler statement.
-/

namespace SPMF

/-- Compose two couplings through a shared marginal `y`.

Given coupling `couplingXY` with marginals `x` and `y`, and coupling `couplingYZ`
with marginals `y` and `z`, produce a coupling of `x` and `z`. -/
noncomputable def composeCouplings {α β γ : Type}
    (y : SPMF β)
    (couplingXY : SPMF (α × β))
    (couplingYZ : SPMF (β × γ))
    (hXY : ∀ b, ∑' a, couplingXY (a, b) = y b)
    (hYZ : ∀ b, ∑' c, couplingYZ (b, c) = y b) : SPMF (α × γ) := by
  refine ⟨fun (a, c) => ∑' b, couplingXY (a, b) * couplingYZ (b, c) / y b, ?_⟩
  classical
  have hy_ne_top : ∀ b : β, y b ≠ ⊤ := fun b =>
    ne_top_of_lt ((ENNReal.le_tsum b).trans y.property |>.trans_lt ENNReal.one_lt_top)
  calc ∑' (ac : α × γ) (b : β), couplingXY (ac.1, b) * couplingYZ (b, ac.2) / y b
      = ∑' (b : β) (ac : α × γ), couplingXY (ac.1, b) * couplingYZ (b, ac.2) / y b := by
        rw [ENNReal.tsum_comm]
    _ = ∑' (b : β), (y b)⁻¹ * ∑' (ac : α × γ), couplingXY (ac.1, b) * couplingYZ (b, ac.2) := by
        congr 1; ext b
        rw [← ENNReal.tsum_mul_left]
        congr 1; ext ⟨a₁, a₂⟩
        rw [ENNReal.div_eq_inv_mul, mul_comm (y b)⁻¹]
    _ = ∑' (b : β), (y b)⁻¹ * ((∑' a : α, couplingXY (a, b)) * ∑' c : γ, couplingYZ (b, c)) := by
        congr 1; ext b; congr 1
        rw [ENNReal.tsum_prod']
        simp_rw [ENNReal.tsum_mul_left]
        rw [ENNReal.tsum_mul_right]
    _ = ∑' (b : β), (y b)⁻¹ * (y b * y b) := by
        congr 1; ext b; congr 1; congr 1
        · exact hXY b
        · exact hYZ b
    _ = ∑' (b : β), y b := by
        congr 1; ext b
        rcases eq_or_ne (y b) 0 with h | h
        · simp [h]
        · rw [← mul_assoc, ENNReal.inv_mul_cancel h (hy_ne_top b), one_mul]
    _ ≤ 1 := y.property

/-- A cost-tracking SPMF: pairs each output with the number of random choices made. -/
abbrev Cost (α : Type u) : Type u := SPMF (α × Nat)

end SPMF

namespace SPMF.Cost

instance instInhabited : Inhabited (SPMF.Cost α) where
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

/-- Charge does nothing but cost `n` ticks. -/
noncomputable def charge (n : Nat) : SPMF.Cost Unit := SPMF.pure ((), n)

instance : LE (SPMF.Cost α) where
  le p q :=
    ∃ (coupling : SPMF ((α × ℕ) × (α × ℕ))),
      (·.1) <$> coupling = p ∧
      (·.2) <$> coupling = q ∧
      ∀ x ∈ coupling.support, x.1.1 = x.2.1 ∧ x.1.2 ≤ x.2.2

private lemma map_fst_tsum {α β : Type} (c : SPMF (α × β)) (p : SPMF α)
    (h : (·.1) <$> c = p) (a : α) : ∑' b : β, c (a, b) = p a := by
  have key := congr_fun (congrArg Subtype.val h) a
  simp only [Functor.map, SPMF.bind, DFunLike.coe, Function.comp_apply, SPMF.pure] at key
  rw [ENNReal.tsum_prod', tsum_eq_single a (by intro a₁ ha₁; simp [if_neg (Ne.symm ha₁)])] at key
  simp_all
  assumption

private lemma map_snd_tsum {α β : Type} (c : SPMF (α × β)) (p : SPMF β)
    (h : (·.2) <$> c = p) (b : β) : ∑' a : α, c (a, b) = p b := by
  have key := congr_fun (congrArg Subtype.val h) b
  simp only [Functor.map, SPMF.bind, DFunLike.coe, Function.comp_apply, SPMF.pure] at key
  rw [ENNReal.tsum_prod'] at key
  conv_lhs at key =>
    arg 1; ext a₁
    rw [tsum_eq_single b (by intro a₂ ha₂; simp [if_neg (Ne.symm ha₂)])]
  simp_all
  assumption

instance : Preorder (SPMF.Cost α) where
  le_refl x := by
    exists (x >>= fun a => Pure.pure (a, a))
    refine ⟨?_, ?_, ?_⟩ <;> simp
    grind
  le_trans x y z hxy hyz := by
    have ⟨couplingXY, hxy₁, hxy₂, hxy₃⟩ := hxy
    have ⟨couplingYZ, hyz₁, hyz₂, hyz₃⟩ := hyz
    have hXY_left := map_fst_tsum couplingXY x hxy₁
    have hXY_marg := map_snd_tsum couplingXY y hxy₂
    have hYZ_marg := map_fst_tsum couplingYZ y hyz₁
    have hYZ_right := map_snd_tsum couplingYZ z hyz₂
    have hy_ne_top b : y b ≠ ⊤ :=
      ne_top_of_lt ((ENNReal.le_tsum b).trans y.property |>.trans_lt ENNReal.one_lt_top)
    exists SPMF.composeCouplings y couplingXY couplingYZ hXY_marg hYZ_marg
    refine ⟨?left_marginal, ?right_marginal, ?cost_refinement⟩
    case left_marginal =>
      apply DFunLike.ext; intro a
      simp only [Functor.map, SPMF.bind, DFunLike.coe, Function.comp_apply, SPMF.pure,
                 SPMF.composeCouplings]
      rw [ENNReal.tsum_prod', tsum_eq_single a (by intro a₁ ha₁; simp [if_neg (Ne.symm ha₁)])]
      simp only [ite_true, mul_one]
      rw [ENNReal.tsum_comm]
      have key : ∀ b, ∑' c, couplingXY (a, b) * couplingYZ (b, c) / y b = couplingXY (a, b) := by
        intro b
        simp_rw [ENNReal.div_eq_inv_mul, ← mul_assoc, ENNReal.tsum_mul_left, hYZ_marg b]
        rcases eq_or_ne (y b) 0 with h | h
        . simp [ENNReal.tsum_eq_zero.mp ((hXY_marg b).trans h) a, h]
        . rw [mul_right_comm, ENNReal.inv_mul_cancel h (hy_ne_top b), one_mul]
      show ∑' b, ∑' a_1, couplingXY (a, b) * couplingYZ (b, a_1) / y b = x a
      simp_rw [key]
      exact hXY_left a
    case right_marginal =>
      apply DFunLike.ext; intro c
      simp only [Functor.map, SPMF.bind, DFunLike.coe, Function.comp_apply, SPMF.pure,
                 SPMF.composeCouplings]
      rw [ENNReal.tsum_prod']
      conv_lhs =>
        arg 1; ext a
        rw [tsum_eq_single c (by intro c' hc'; simp [if_neg (Ne.symm hc')])]
      simp only [ite_true, mul_one]
      rw [ENNReal.tsum_comm]
      have key : ∀ b, ∑' a, couplingXY (a, b) * couplingYZ (b, c) / y b = couplingYZ (b, c) := by
        intro b
        simp_rw [mul_div_assoc, ENNReal.tsum_mul_right, hXY_marg b]
        rcases eq_or_ne (y b) 0 with h | h
        . simp [ENNReal.tsum_eq_zero.mp ((hYZ_marg b).trans h) c, h]
        . exact ENNReal.mul_div_cancel h (hy_ne_top b)
      show ∑' b, ∑' a, couplingXY (a, b) * couplingYZ (b, c) / y b = z c
      simp_rw [key]
      exact hYZ_right c
    case cost_refinement =>
      intro ⟨a, c⟩ hmem
      rw [SPMF.mem_support_iff] at hmem
      simp only [SPMF.composeCouplings, DFunLike.coe] at hmem
      have ⟨b, hb⟩ : ∃ b, couplingXY (a, b) * couplingYZ (b, c) / y b ≠ 0 := by
        by_contra hall
        push Not at hall
        exact hmem (ENNReal.tsum_eq_zero.mpr hall)
      have hprod : couplingXY (a, b) * couplingYZ (b, c) ≠ 0 := by
        intro h; simp [h] at hb
      have hab_ne : couplingXY (a, b) ≠ 0 := left_ne_zero_of_mul hprod
      have hbc_ne : couplingYZ (b, c) ≠ 0 := right_ne_zero_of_mul hprod
      have hab := hxy₃ (a, b) ((SPMF.mem_support_iff _ _).mpr hab_ne)
      have hbc := hyz₃ (b, c) ((SPMF.mem_support_iff _ _).mpr hbc_ne)
      exact ⟨hab.1.trans hbc.1, hab.2.trans hbc.2⟩

theorem bind_mono_left
    {x y : SPMF.Cost α}
    {f : α → SPMF.Cost β}
    (hxy : x ≤ y) :
    x >>= f ≤ y >>= f := by
  have ⟨c, hcx, hcy, hc_cost⟩ := hxy
  exists do
    let ((a, ca), (_, ca')) ← c
    let (b, cb) ← f a
    return ((b, cb + ca), (b, cb + ca'))
  refine ⟨?left_marginal, ?right_marginal, ?cost_refinement⟩
  case left_marginal =>
    simp only [Functor.map] at *
    rw [← hcx]
    simp +arith [Bind.bind, Pure.pure, SPMF.bind_assoc, SPMF.pure_bind]
  case right_marginal =>
    simp only [Functor.map] at *
    rw [← hcy]
    simp only [Bind.bind, Pure.pure, SPMF.bind_assoc, SPMF.pure_bind, Function.comp_apply]
    apply SPMF.bind_congr_support
    intro a ha
    simp +arith [(hc_cost a ha).1]
  case cost_refinement =>
    grind only [SPMF.support_bind, usr Set.mem_setOf_eq, SPMF.support_pure, = Set.mem_singleton_iff]

theorem bind_mono_right
    {f g : α → SPMF.Cost β}
    (hfg : ∀ a, f a ≤ g a) :
    x >>= f ≤ x >>= g := by
  exists do
    let (a, ca) ← x
    let ((b, cb), (_, cb')) ← Classical.choose (hfg a)
    return ((b, ca + cb), (b, ca + cb'))
  refine ⟨?left_marginal, ?right_marginal, ?cost_refinement⟩
  case left_marginal =>
    simp only [Functor.map, Bind.bind, Prod.forall, Pure.pure, SPMF.bind_assoc, SPMF.pure_bind, Function.comp_apply]
    grind only [SPMF.bind_congr_support, Classical.choose_spec, usr Exists.choose_spec, SPMF.bind_assoc, SPMF.pure_bind]
  case right_marginal =>
    simp only [Functor.map, Bind.bind, Prod.forall, Pure.pure, SPMF.bind_assoc, SPMF.pure_bind, Function.comp_apply]
    grind only [SPMF.bind_congr_support, Classical.choose_spec, usr Exists.choose_spec, SPMF.bind_assoc, SPMF.pure_bind]
  case cost_refinement =>
    intro p hp
    simp only [Prod.forall, bind_pure_comp, SPMF.support_bind, SPMF.support_map, Prod.exists, Set.mem_setOf_eq] at hp
    grind

/-- Erases cost. This is used in the definition of `IsBounded` in conjunction with `charge`. -/
noncomputable def noCharge (x : SPMF.Cost α) : SPMF.Cost α := SPMF.bind x (fun (a, _) => SPMF.pure (a, 0))

@[simp]
theorem noCharge_pure : noCharge (Pure.pure a) = Pure.pure a := by
  simp [Pure.pure, noCharge, SPMF.pure_bind]

@[simp]
theorem noCharge_bind : noCharge (x >>= f) = noCharge x >>= noCharge ∘ f := by
  simp [Bind.bind, noCharge, SPMF.bind_assoc, SPMF.pure_bind]

@[simp]
theorem noCharge_charge : noCharge (charge n) = Pure.pure () := by
  simp [noCharge, charge, Pure.pure, SPMF.pure_bind]

@[simp]
theorem noCharge_choose :
    noCharge (choose lo hi h) =
      SPMF.bind (choose lo hi h : SPMF.Cost (ULift {x : Nat // lo ≤ x ∧ x ≤ hi}))
        fun (a, _) => SPMF.pure (a, 0) := by
  simp [noCharge]

section support

@[simp]
theorem mem_support_pure_iff {a b : α} {n : Nat} :
    (b, n) ∈ (Pure.pure a : SPMF.Cost α).support ↔ b = a ∧ n = 0 := by
  have : (Pure.pure a : SPMF.Cost α) = (SPMF.pure (a, 0) : SPMF _) := rfl
  simp [this, SPMF.mem_support_pure_iff, Prod.mk.injEq]

@[simp]
theorem mem_support_bind_iff
    {m : SPMF.Cost α} {f : α → SPMF.Cost β} {b : β} {n : Nat} :
    (b, n) ∈ (m >>= f).support ↔
    ∃ a n1 n2, (a, n1) ∈ m.support ∧ (b, n2) ∈ (f a).support ∧ n = n1 + n2 := by
  have : (m >>= f : SPMF.Cost β) =
      SPMF.bind m fun pair =>
        SPMF.bind (f pair.1) fun pair2 =>
          (SPMF.pure (pair2.1, pair.2 + pair2.2) : SPMF _) := rfl
  rw [this]
  simp only [SPMF.mem_support_bind_iff, SPMF.mem_support_pure_iff, Prod.mk.injEq]
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
        fun k => (SPMF.pure (k, 1) : SPMF _) := rfl
  rw [this]
  simp only [SPMF.mem_support_bind_iff, SPMF.mem_support_choose_iff,
             SPMF.mem_support_pure_iff, Prod.mk.injEq, true_and]
  constructor
  · rintro ⟨k, rfl, rfl⟩
    rfl
  · rintro rfl
    exact ⟨n, rfl, rfl⟩

end support

end SPMF.Cost

open SPMF.Cost

def IsBounded (x : SPMF.Cost α) (f : α → Nat) : Prop :=
  x ≤ (noCharge x >>= fun a => do charge (f a); pure a)

/-- Translates between the complex, coupling-based definition of `IsBounded` and a simpler version
  that expresses the property more intuitively.

  In general, when an `IsBounded` goal can be proved in terms of the simpler definition, this lemma
  should be used to simplify the goal. -/
theorem IsBounded_iff {x : SPMF.Cost α} {f : α → Nat} :
    IsBounded x f ↔
    ∀ p ∈ SPMF.support x, p.2 ≤ f p.1 := by
  constructor
  . simp only [bind, noCharge, charge, pure, SPMF.pure_bind, add_zero, SPMF.bind_assoc, zero_add, IsBounded, Prod.forall]
    intro h a n hsupport
    have ⟨c, h₁, h₂, h₃⟩ := h
    have : ((a, n), (a, f a)) ∈ c.support := by
      clear h
      simp only [Functor.map, Function.comp_def] at *
      rw [← h₁] at h₂
      simp only [SPMF.bind_assoc, SPMF.pure_bind] at *
      rw [← h₁] at hsupport
      simp only [SPMF.mem_support_bind_iff, SPMF.mem_support_pure_iff] at hsupport
      have ⟨(a', n'), h, heq⟩ := hsupport
      cases heq
      have hn' : n' = (a, f a) := by
        have hmem : n' ∈ (c.bind fun x => SPMF.pure x.2).support := by
          grind only [SPMF.mem_support_bind_iff, SPMF.mem_support_pure_iff]
        grind only [SPMF.mem_support_bind_iff, Prod.snd_eq_iff, SPMF.mem_support_pure_iff]
      subst hn'
      exact h
    grind
  . intro h
    simp only [IsBounded, bind, noCharge, pure, charge, SPMF.pure_bind, add_zero, SPMF.bind_assoc, zero_add]
    exists do
      let (a, n) ← x
      pure ((a, n), (a, f a))
    refine ⟨?left_marginal, ?right_marginal, ?cost_refinement⟩
    case left_marginal =>
      simp [Functor.map, SPMF.bind_assoc, Function.comp_def, SPMF.pure_bind, SPMF.bind_pure]
    case right_marginal =>
      simp [Functor.map, SPMF.bind_assoc, Function.comp_def, SPMF.pure_bind]
    case cost_refinement =>
      simp_all

theorem IsBounded_pure : IsBounded (pure a) (fun _ => 0) := by
  simp +arith [IsBounded, noCharge, charge, pure, bind, SPMF.pure_bind]

theorem IsBounded_choose : IsBounded (choose lo hi h) (fun _ => 1) := by
  rw [IsBounded_iff]
  rintro ⟨n, c⟩ hmem
  simp only [mem_support_choose_iff] at hmem
  omega

theorem IsBounded_bind
    {cx : α → Nat}
    {cf : α → β → Nat}
    {c : β → Nat}
    (hx : IsBounded x cx)
    (hf : ∀ a, IsBounded (f a) (cf a))
    (hg : ∀ p ∈ x.support, ∀ q ∈ (f p.1).support, cx p.1 + cf p.1 q.1 ≤ c q.1) :
    IsBounded (x >>= f) c := by
  simp_all only [IsBounded_iff]
  intro (b, nb) hb
  simp only [bind, SPMF.mem_support_bind_iff, SPMF.mem_support_pure_iff] at hb
  replace ⟨(a, na), ha, ⟨(b, nb), hb, h⟩⟩ := hb
  cases h
  simp_all
  grind

theorem IsBounded_mono
    (hc₁ : IsBounded x c₁)
    (h : ∀ a, c₁ a ≤ c₂ a) :
    IsBounded x c₂ := by
  simp_all only [IsBounded_iff]
  grind

theorem IsBounded_pick
    {fx fy : Unit → SPMF.Cost α}
    {cx cy : α → Nat}
    (hx : IsBounded (fx ()) cx)
    (hy : IsBounded (fy ()) cy) :
    IsBounded (pick fx fy) (fun a => 1 + max (cx a) (cy a)) := by
  unfold pick
  apply IsBounded_bind (cx := fun _ => 1)
      (cf := fun k a => if k.down.val == 0 then cx a else cy a)
      IsBounded_choose
  · intro k
    split_ifs
    · exact hx
    · exact hy
  · intro ⟨k, _⟩ _ ⟨a, _⟩ _
    simp only
    split_ifs <;> omega

open Lean.Order in
/-- `IsBounded` is an admissible relation.

  This is intended to be used in the construction of partial_fixpoint, and not meant to be used otherwise. -/
theorem admissible_IsBounded (f : α → Nat) :
    admissible (fun (x : SPMF.Cost α) => IsBounded x f) := by
  intro c hc ih
  simp only [IsBounded_iff] at *
  intro p hp
  rw [SPMF.mem_support_csup hc] at hp
  obtain ⟨x, hxc, hxp⟩ := hp
  exact ih x hxc p hxp
