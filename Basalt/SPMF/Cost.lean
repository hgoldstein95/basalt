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
list generator makes `O(|xs|)` choices to generate `xs`." Its observations land in `WPC`, whose
`bind` and `choose` do the cost accounting, so a combinator's lemma is its `Obs.map_*` read through
one of them.
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
    · rfl
    · apply ENNReal.tsum_le_tsum
      intro i
      gcongr ?_ * ?_
      apply h
      rfl

end CCPO

noncomputable instance instRandomChoice : RandomChoice SPMF.Cost where
  choose lo hi h := by
    exact SPMF.bind (choose lo hi h : SPMF (ULift {x : Nat // lo ≤ x ∧ x ≤ hi}))
      fun n => SPMF.pure (n, 1)

instance instLawfulMonad : LawfulMonad SPMF.Cost := LawfulMonad.mk' _
  (id_map := fun x => by
    show SPMF.bind x (fun p => SPMF.bind (SPMF.pure (p.1, 0)) fun q => SPMF.pure (q.1, p.2 + q.2)) = x
    simp only [SPMF.pure_bind, Nat.add_zero]
    exact SPMF.bind_pure x)
  (pure_bind := fun a f => by
    show SPMF.bind (SPMF.pure (a, 0)) (fun p => SPMF.bind (f p.1) fun q => SPMF.pure (q.1, p.2 + q.2))
      = f a
    simp only [SPMF.pure_bind, Nat.zero_add]
    exact SPMF.bind_pure (f a))
  (bind_assoc := fun x f g => by
    show SPMF.bind (SPMF.bind x fun p => SPMF.bind (f p.1) fun q => SPMF.pure (q.1, p.2 + q.2))
        (fun r => SPMF.bind (g r.1) fun s => SPMF.pure (s.1, r.2 + s.2))
      = SPMF.bind x fun p =>
          SPMF.bind (SPMF.bind (f p.1) fun q => SPMF.bind (g q.1) fun s => SPMF.pure (s.1, q.2 + s.2))
            fun t => SPMF.pure (t.1, p.2 + t.2)
    simp only [SPMF.bind_assoc, SPMF.pure_bind, Nat.add_assoc])

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

end support

section observations

open scoped ENNReal

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

/-- The expectation observation: the postcondition sees the value and the choices it took. -/
noncomputable def expectObs : Obs SPMF.Cost.{u} (WPC Mix.average) where
  spec g := fun post => SPMF.expect g fun p => post p.1 p.2
  map_pure a := by funext post; exact expect_pure a _
  map_bind x k := by funext post; exact expect_bind x k _
  map_choose lo hi h := by
    funext post
    show SPMF.expect (SPMF.bind (choose lo hi h : SPMF _) fun n => SPMF.pure (n, 1)) _ = _
    rw [SPMF.bind_eq, SPMF.expect_bind]
    simp only [SPMF.pure_eq, SPMF.expect_pure]
    rfl

/-- The may observation. -/
def mayObs : Obs SPMF.Cost.{u} (WPC Mix.angelic) where
  spec g := fun Q => ∃ p ∈ SPMF.support g, Q p.1 p.2
  map_pure a := by
    funext Q; apply propext
    constructor
    · rintro ⟨⟨b, n⟩, hp, h⟩
      obtain ⟨rfl, rfl⟩ := mem_support_pure_iff.mp hp
      exact h
    · exact fun h => ⟨(a, 0), mem_support_pure_iff.mpr ⟨rfl, rfl⟩, h⟩
  map_bind x k := by
    funext Q; apply propext
    constructor
    · rintro ⟨⟨b, n⟩, hp, h⟩
      obtain ⟨a, n1, n2, h1, h2, rfl⟩ := mem_support_bind_iff.mp hp
      exact ⟨(a, n1), h1, (b, n2), h2, h⟩
    · rintro ⟨⟨a, n1⟩, h1, ⟨b, n2⟩, h2, h⟩
      exact ⟨(b, n1 + n2), mem_support_bind_iff.mpr ⟨a, n1, n2, h1, h2, rfl⟩, h⟩
  map_choose lo hi h := by
    funext Q; apply propext
    constructor
    · rintro ⟨⟨a, c⟩, hp, h⟩
      obtain rfl := mem_support_choose_iff.mp hp
      exact ⟨a, h⟩
    · exact fun ⟨a, h⟩ => ⟨(a, 1), mem_support_choose_iff.mpr rfl, h⟩

/-- The always observation. -/
def alwaysObs : Obs SPMF.Cost.{u} (WPC Mix.demonic) where
  spec g := fun Q => ∀ p ∈ SPMF.support g, Q p.1 p.2
  map_pure a := by
    funext Q; apply propext
    constructor
    · exact fun h => h (a, 0) (mem_support_pure_iff.mpr ⟨rfl, rfl⟩)
    · rintro h ⟨b, n⟩ hp
      obtain ⟨rfl, rfl⟩ := mem_support_pure_iff.mp hp
      exact h
  map_bind x k := by
    funext Q; apply propext
    constructor
    · rintro h ⟨a, n1⟩ h1 ⟨b, n2⟩ h2
      exact h (b, n1 + n2) (mem_support_bind_iff.mpr ⟨a, n1, n2, h1, h2, rfl⟩)
    · rintro h ⟨b, n⟩ hp
      obtain ⟨a, n1, n2, h1, h2, rfl⟩ := mem_support_bind_iff.mp hp
      exact h (a, n1) h1 (b, n2) h2
  map_choose lo hi h := by
    funext Q; apply propext
    constructor
    · exact fun hq a => hq (a, 1) (mem_support_choose_iff.mpr rfl)
    · rintro hq ⟨a, c⟩ hp
      obtain rfl := mem_support_choose_iff.mp hp
      exact hq a

/-- Support membership, read through a specification the may observation equals. -/
theorem mem_support_of_may {g : SPMF.Cost α} {w : WPC Mix.angelic α} (h : mayObs.spec g = w)
    {a : α} {n : Nat} : (a, n) ∈ SPMF.support g ↔ w fun b m => b = a ∧ m = n := by
  refine Iff.trans ⟨fun h => ⟨(a, n), h, rfl, rfl⟩, ?_⟩ (iff_of_eq (congrFun h _))
  rintro ⟨⟨b, m⟩, hp, rfl, rfl⟩
  exact hp

/-- An expectation, read through a specification the expectation observation equals. -/
theorem expect_of_obs {g : SPMF.Cost α} {w : WPC Mix.average α} (h : expectObs.spec g = w)
    (φ : α × Nat → ℝ≥0∞) : SPMF.expect g φ = w fun a n => φ (a, n) :=
  congrFun h fun a n => φ (a, n)

end observations

section erasure

open scoped ENNReal

/-- The value distribution of a cost-tracking generator: `Prod.fst <$> g` in `SPMF`. -/
noncomputable def erase (g : SPMF.Cost α) : SPMF α := SPMF.bind g fun p => SPMF.pure p.1

/-- The erasure observation. A generator's two interpretations agree on values wherever `erase`
commutes with it, which for a combinator is its `Obs.spec_*` lemma. -/
noncomputable def eraseObs : Obs SPMF.Cost.{u} SPMF where
  spec := erase
  map_pure a := SPMF.pure_bind (a, 0) _
  map_bind x k := by
    show SPMF.bind (SPMF.bind x fun p => SPMF.bind (k p.1) fun q => SPMF.pure (q.1, p.2 + q.2))
        (fun r => SPMF.pure r.1)
      = SPMF.bind (SPMF.bind x fun p => SPMF.pure p.1) fun a =>
          SPMF.bind (k a) fun q => SPMF.pure q.1
    simp only [SPMF.bind_assoc, SPMF.pure_bind]
  map_choose lo hi h := by
    show SPMF.bind (SPMF.bind (choose lo hi h : SPMF _) fun n => SPMF.pure (n, 1))
        (fun r => SPMF.pure r.1) = _
    simp only [SPMF.bind_assoc, SPMF.pure_bind]
    exact SPMF.bind_pure _

/-- An expectation over values may be taken at either interpretation. -/
theorem expect_erase (g : SPMF.Cost α) (f : α → ℝ≥0∞) :
    SPMF.expect (erase g) f = SPMF.expect g fun p => f p.1 := by
  unfold erase
  rw [SPMF.bind_eq, SPMF.expect_bind]
  simp only [SPMF.pure_eq, SPMF.expect_pure]

theorem erase_pure (a : α) : erase (Pure.pure a : SPMF.Cost α) = Pure.pure a :=
  eraseObs.map_pure a

theorem erase_bind (x : SPMF.Cost α) (k : α → SPMF.Cost β) :
    erase (x >>= k) = erase x >>= fun a => erase (k a) :=
  eraseObs.map_bind x k

theorem erase_map (f : α → β) (x : SPMF.Cost α) : erase (f <$> x) = f <$> erase x :=
  eraseObs.map_map f x

theorem erase_pick (x y : Unit → SPMF.Cost α) :
    erase (pick x y) = pick (fun u => erase (x u)) (fun u => erase (y u)) :=
  eraseObs.map_pick x y

theorem erase_coin (r : Rat) : erase (coin r : SPMF.Cost Bool) = coin r :=
  eraseObs.map_coin r

theorem erase_chooseNat (lo hi : Nat) (h : lo ≤ hi) :
    erase (chooseNat lo hi h : SPMF.Cost Nat) = chooseNat lo hi h :=
  eraseObs.spec_chooseNat lo hi h

theorem erase_chooseInt (lo hi : Int) (h : lo ≤ hi) :
    erase (chooseInt lo hi h : SPMF.Cost Int) = chooseInt lo hi h :=
  eraseObs.spec_chooseInt lo hi h

theorem erase_elements (xs : List α) (hne : xs ≠ []) :
    erase (elements xs hne : SPMF.Cost α) = elements xs hne :=
  eraseObs.spec_elements xs hne

theorem erase_oneOf (gs : List (Unit → SPMF.Cost α)) (hne : gs ≠ []) :
    erase (oneOf gs hne) = oneOf (gs.map fun g u => erase (g u)) (by simpa using hne) :=
  eraseObs.spec_oneOf gs hne

theorem erase_frequency (gs : List (Nat × (Unit → SPMF.Cost α)))
    (h : 0 < (gs.map Prod.fst).sum) :
    erase (frequency gs h)
      = frequency (gs.map fun p => (p.1, fun u => erase (p.2 u)))
          (by simpa [Function.comp_def] using h) :=
  eraseObs.spec_frequency gs h

theorem erase_vectorOf {α : Type} (n : Nat) (g : SPMF.Cost α) :
    erase (vectorOf n g) = vectorOf n (erase g) :=
  eraseObs.spec_vectorOf n g

theorem erase_listOfMaxLength (n : Nat) (g : SPMF.Cost α) :
    erase (listOfMaxLength n g) = listOfMaxLength n (erase g) :=
  eraseObs.spec_listOfMaxLength n g

theorem erase_biasedOptionGen (r : Rat) (g : SPMF.Cost α) :
    erase (biasedOptionGen r g) = biasedOptionGen r (erase g) :=
  eraseObs.spec_biasedOptionGen r g

theorem erase_optionGen (g : SPMF.Cost α) : erase (optionGen g) = optionGen (erase g) :=
  eraseObs.spec_optionGen g

end erasure

section support

/-- Support inversion for `pick` at the cost interpretation: a branch draw plus one choice. -/
@[simp]
theorem mem_support_pick_iff {x y : Unit → SPMF.Cost α} {a : α} {n : Nat} :
    (a, n) ∈ (pick x y).support ↔
      ∃ m, n = 1 + m ∧ ((a, m) ∈ (x ()).support ∨ (a, m) ∈ (y ()).support) := by
  refine (mem_support_of_may (mayObs.map_pick x y)).trans ((Mix.binary_angelic _).trans ?_)
  constructor
  · rintro (⟨⟨b, m⟩, hp, rfl, rfl⟩ | ⟨⟨b, m⟩, hp, rfl, rfl⟩)
    · exact ⟨m, rfl, Or.inl hp⟩
    · exact ⟨m, rfl, Or.inr hp⟩
  · rintro ⟨m, rfl, h | h⟩
    · exact Or.inl ⟨(a, m), h, rfl, rfl⟩
    · exact Or.inr ⟨(a, m), h, rfl, rfl⟩

@[simp]
theorem mem_support_chooseNat_iff {lo hi : Nat} {h : lo ≤ hi} {n c : Nat} :
    (n, c) ∈ (chooseNat lo hi h : SPMF.Cost Nat).support ↔ (lo ≤ n ∧ n ≤ hi) ∧ c = 1 :=
  (mem_support_of_may (mayObs.map_chooseNat lo hi h)).trans ((Mix.range_angelic _).trans
    ⟨fun ⟨_, hx, e, e'⟩ => ⟨e ▸ hx, e'.symm⟩, fun ⟨hx, e⟩ => ⟨n, hx, rfl, e.symm⟩⟩)

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

theorem expect_pick (x y : Unit → SPMF.Cost α) (φ : α × Nat → ℝ≥0∞) :
    SPMF.expect (pick x y : SPMF.Cost α) φ
      = (1/2 : ℝ≥0∞) * SPMF.expect (x ()) (fun p => φ (p.1, 1 + p.2))
        + (1/2 : ℝ≥0∞) * SPMF.expect (y ()) (fun p => φ (p.1, 1 + p.2)) :=
  (expect_of_obs (expectObs.map_pick x y) φ).trans (Mix.binary_average _)

theorem expect_coin {r : Rat} (h0 : 0 ≤ r) (h1 : r ≤ 1) (φ : Bool × Nat → ℝ≥0∞) :
    SPMF.expect (coin r : SPMF.Cost Bool) φ
      = (r.num.toNat : ℝ≥0∞) / (r.den : ℝ≥0∞) * φ (true, 1)
        + ((r.den - r.num.toNat : ℕ) : ℝ≥0∞) / (r.den : ℝ≥0∞) * φ (false, 1) := by
  obtain ⟨hnum, hle⟩ := SPMF.coin_num_bounds h0 h1
  refine (expect_of_obs (expectObs.map_coin r) φ).trans ?_
  simp only [coin, WPC.choose_bind_apply, WPC.ite_apply]
  exact Mix.threshold_average r.den_pos hnum hle _ _

theorem expect_chooseNat {lo hi : Nat} (h : lo ≤ hi) (φ : Nat × Nat → ℝ≥0∞) :
    SPMF.expect (chooseNat lo hi h : SPMF.Cost Nat) φ
      = (∑ x ∈ Finset.Icc lo hi, φ (x, 1)) / ((hi - lo + 1 : ℕ) : ℝ≥0∞) :=
  (expect_of_obs (expectObs.map_chooseNat lo hi h) φ).trans
    (Mix.range_average lo hi fun x => φ (x, 1))

theorem expect_elements {xs : List α} (hne : xs ≠ []) (φ : α × Nat → ℝ≥0∞) :
    SPMF.expect (elements xs hne : SPMF.Cost α) φ
      = (xs.map fun a => φ (a, 1)).sum / (xs.length : ℝ≥0∞) :=
  (expect_of_obs (expectObs.map_elements xs hne) φ).trans
    (Mix.index_average xs hne fun a => φ (a, 1))

theorem expect_oneOf {gs : List (Unit → SPMF.Cost α)} (hne : gs ≠ []) (φ : α × Nat → ℝ≥0∞) :
    SPMF.expect (oneOf gs hne : SPMF.Cost α) φ
      = (gs.map fun g => SPMF.expect (g ()) fun p => φ (p.1, 1 + p.2)).sum
          / (gs.length : ℝ≥0∞) :=
  (expect_of_obs (expectObs.map_oneOf gs hne) φ).trans
    (Mix.index_average gs hne fun g => SPMF.expect (g ()) fun p => φ (p.1, 1 + p.2))

theorem expect_frequency {gs : List (Nat × (Unit → SPMF.Cost α))}
    (h : 0 < (gs.map Prod.fst).sum) (φ : α × Nat → ℝ≥0∞) :
    SPMF.expect (frequency gs h : SPMF.Cost α) φ
      = (gs.map fun p => (p.1 : ℝ≥0∞) * SPMF.expect (p.2 ()) fun q => φ (q.1, 1 + q.2)).sum
          / (((gs.map Prod.fst).sum : ℕ) : ℝ≥0∞) := by
  refine (expect_of_obs (expectObs.map_frequency gs h (expectObs.spec default)) φ).trans ?_
  simp only [WPC.choose_bind_apply,
    Obs.selectD_map (fun w : WPC Mix.average α => w fun b n => φ (b, 1 + n)), List.map_map]
  refine (Mix.select_average _ ?_ h _).trans ?_
  · simp [Function.comp_def]
  · simp [Function.comp_def, expectObs]

/-- A worst-case cost law bounds the average: `expectedCost` is at most the expected bound. -/
theorem expectedCost_le_of_IsBounded {g : SPMF.Cost α} {c : α → Nat} (h : IsBounded g c) :
    expectedCost g ≤ SPMF.expect g (fun p => (c p.1 : ℝ≥0∞)) := by
  refine SPMF.expect_mono_support fun p hp => ?_
  exact_mod_cast h p hp

end expectation

end SPMF.Cost
