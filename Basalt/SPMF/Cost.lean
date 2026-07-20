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

## Main Definitions

- `SPMF.Cost` — A cost interpretation for a generator.
- `IsBounded` — A proposition that says a generator makes a bounded number of choices.
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

/-- Support inversion for `frequency` at the cost interpretation: a draw from `frequency gs`
  is a draw from one of its positive-weight branches, plus exactly one choice (the branch
  selection). The cost-side counterpart of `SPMF.support_frequency`. -/
theorem mem_support_frequency
    {gs : List (Nat × (Unit → SPMF.Cost α))}
    {hne : 0 < (List.map Prod.fst gs).sum}
    {a : α} {n : Nat}
    (hmem : (a, n) ∈ (frequency gs hne).support) :
    ∃ w g m, (w, g) ∈ gs ∧ 0 < w ∧ (a, m) ∈ (g ()).support ∧ n = m + 1 := by
  unfold frequency Helpers.frequencyAux at hmem
  rw [mem_support_bind_iff] at hmem
  obtain ⟨v, n1, n2, hchoose, hrest, rfl⟩ := hmem
  rw [mem_support_map_iff] at hchoose
  obtain ⟨u, hu, rfl⟩ := hchoose
  rw [mem_support_choose_iff] at hu
  subst hu
  obtain ⟨⟨x, hx0, hxle⟩⟩ := u
  simp only at hrest
  have hlt : x < (List.map Prod.fst gs).sum := by omega
  rw [dif_pos hlt] at hrest
  obtain ⟨w, g, hwg, hw, heq⟩ := SPMF.frequencySelect_mem hlt
  rw [heq] at hrest
  exact ⟨w, g, n2, hwg, hw, hrest, by omega⟩

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

theorem IsBounded_pure : IsBounded (pure a) (fun _ => 0) := by
  rw [IsBounded_iff]
  rintro ⟨b, n⟩ hmem
  simp only [mem_support_pure_iff] at hmem
  omega

theorem IsBounded_choose : IsBounded (choose lo hi h) (fun _ => 1) := by
  rw [IsBounded_iff]
  rintro ⟨n, c⟩ hmem
  simp only [mem_support_choose_iff] at hmem
  omega

/-- The `default` generator has empty support since it's just the constant function returning 0.
    Thus, `default` is bounded by any cost function `f`. -/
theorem IsBounded_default {f : α → Nat} : IsBounded (default : SPMF.Cost α) f := by
  rw [IsBounded_iff]
  intro (x, c) hp
  rw [SPMF.mem_support_iff] at hp
  dsimp
  apply Nat.le_of_not_lt
  intro hcontra
  apply hp
  rfl

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
  simp only [SPMF.Cost.mem_support_bind_iff] at hb
  obtain ⟨a, n1, n2, ha, hb2, rfl⟩ := hb
  have h1 : n1 ≤ cx a := hx (a, n1) ha
  have h2 : n2 ≤ cf a b := hf a (b, n2) hb2
  have h3 : cx a + cf a b ≤ c b := hg (a, n1) ha (b, n2) hb2
  show n1 + n2 ≤ c b
  omega

-- We add this lemma to make it easier to reason about generators that use `<$>`
theorem IsBounded_map
    {f : α → β}
    {cx : α → Nat}
    {c : β → Nat}
    (hx : IsBounded x cx)
    (hg : ∀ p ∈ x.support, cx p.1 ≤ c (f p.1)) :
    IsBounded (f <$> x) c := by
  -- For any monad, we have that `f <$> x === x >>= (pure ∘ f)`,
  -- and we use this equational law to change the shape of our goal
  -- so that we can prove it in terms of `IsBounded_bind`
  show IsBounded (x >>= fun a => pure (f a)) c
  apply IsBounded_bind
  . assumption
  · intro a
    apply IsBounded_pure
  · intro (a, a_cost) ha ⟨b, b_cost⟩ hq
    simp only [mem_support_pure_iff] at hq
    obtain ⟨rfl, rfl⟩ := hq
    dsimp
    specialize hg (a, a_cost) ha
    dsimp at hg
    assumption

theorem IsBounded_mono
    (hc₁ : IsBounded x c₁)
    (h : ∀ a, c₁ a ≤ c₂ a) :
    IsBounded x c₂ := by
  simp_all only [IsBounded_iff]
  grind

/-- The `elements` combinator makes only one random choice (the index into the list) -/
theorem IsBounded_elements
    (hne : xs ≠ []) :
    IsBounded (elements xs hne) (fun _ => 1) := by
  unfold elements
  -- After picking the random index, `elements` no longer performs any more random choices,
  -- so `cf` (the cost function for the continuation after we bind the result of `choose`)
  -- is just the constant function returning 0
  apply IsBounded_bind
    (cx := fun _ => 1)
    (cf := fun _ _ => 0)
  . apply IsBounded_map
    . apply IsBounded_choose
    . omega
  . intro ⟨k, ⟨_, hle⟩⟩
    dsimp
    apply IsBounded_pure
  . omega

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

/-- The cost incurred by `vectorOf n g` is the sum of the costs of generating each element using `g` -/
theorem IsBounded_vectorOf
    (hx : IsBounded g cost_g) :
    IsBounded (vectorOf n g) (fun xs => List.sum (cost_g <$> xs)) := by
  simp_all only [IsBounded_iff]
  induction n with
  | zero =>
    intro (xs, xs_cost) hxs
    simp [vectorOf] at hxs
    obtain ⟨h1, h2⟩ := hxs
    subst h1 h2
    omega
  | succ n' IH =>
    rw [vectorOf_succ]
    intro (xs, xs_cost) hxs
    simp only [mem_support_bind_iff, mem_support_pure_iff] at hxs
    obtain ⟨a, a_cost, ys_cost, ha, ⟨ys, _, _, hys, ⟨rfl, rfl⟩, rfl⟩, rfl⟩ := hxs
    dsimp
    have ha_cost : (a, a_cost).2 ≤ cost_g (a, a_cost).1 := by
      apply hx
      assumption
    have hys_cost : (ys, ys_cost).2 ≤ (cost_g <$> (ys, ys_cost).1).sum := by
      apply IH
      assumption
    simp only [Functor.map, List.map_cons, List.sum_cons] at *
    omega

/-- The cost function here is 1 more than the cost of `vectorOf`, because
    `listOfMaxLength` needs to randomly choose a length for the list before invoking `vectorOf` -/
theorem IsBounded_listOfMaxLength
    (hx : IsBounded g cost_g) :
    IsBounded (listOfMaxLength n g) (fun xs => 1 + List.sum (cost_g <$> xs)) := by
  -- Note: we have to explicitly instantiate `cx` & `cf` here, otherwise we will get a heartbeat timeout
  -- when we do `lake build`
  apply IsBounded_bind
    (cx := fun _ => 1)                            -- 1 random choice to pick length of list
    (cf := fun _ xs => List.sum (cost_g <$> xs))  -- Sum all the cost incurred from generating each list element
  · -- IsBounded (ULift.down <$> choose 0 n ⋯) (fun x => 1)
    apply IsBounded_map
    . apply IsBounded_choose
    . intro (k, k_cost) hk
      constructor
  · -- ∀ k, IsBounded (vectorOf k g) (fun xs => (cost_g <$> xs).sum)
    intro ⟨k, ⟨hge, hle⟩⟩
    apply IsBounded_vectorOf
    assumption
  · omega

/-- `oneOf`'s cost function is upper-bounded by 1 +
    the max-valued cost function out of all the sub-generators -/
theorem IsBounded_oneOf
    {gs : List (Unit → SPMF.Cost α)}
    (hne : gs ≠ [])
    (hcost : ∀ g ∈ gs, {cost_g // IsBounded (g ()) cost_g}) :
    IsBounded (oneOf gs hne)
      (fun x => 1 + List.foldr (fun ⟨ g, hg ⟩ acc => max ((hcost g hg).val x) acc) 0 gs.attach) := by
  -- Every generator's cost is ≤ the max cost over all generators.
  have hcost_le : ∀ (i : Nat) (hi : i < gs.length) (y : α),
      (hcost gs[i] (List.getElem_mem hi)).val y ≤
        List.foldr (fun g acc => max ((hcost g.val g.property).val y) acc) 0 gs.attach := by
    intro i hi y
    -- Rewrite `foldr` over `attach` as a `foldr` plus a `map` via `List.foldr_map`
    rw [← List.foldr_map]
    apply List.le_max_of_le'
    . apply List.mem_map.mpr
      . exists ⟨gs[i], List.getElem_mem hi⟩
        constructor
        . apply List.mem_attach
        . rfl
    . constructor
  -- Any index chosen by `choose 0 (gs.length - 1)` is in bounds
  have hidx : ∀ (idx : {i : Nat // 0 ≤ i ∧ i ≤ gs.length - 1}), idx.val < gs.length := by
    intro idx
    have hle : idx.val ≤ gs.length - 1 :=
      idx.property.2
    have h_nonzero : 0 < gs.length := by
      apply List.length_pos_iff.mpr hne
    omega
  unfold oneOf Helpers.oneOfAux
  apply IsBounded_bind
    (cx := fun _ => 1)
    (cf := fun idx y => (hcost (gs[idx.val]'(hidx idx)) (List.getElem_mem (hidx idx))).val y)
  · apply IsBounded_map
    · apply IsBounded_choose
    · intro p _
      constructor
  · -- For each `i`, `gs[i]` is bounded by its own cost function
    rintro ⟨i, hge, hle⟩
    -- Reduce the `match` on the index subtype and the `↑⟨i, ⋯⟩` coercion down to `i`
    dsimp only
    have hlt : i < gs.length := hidx ⟨i, hge, hle⟩
    have h_bounded := (hcost gs[i] (List.getElem_mem hlt)).property
    assumption
  · -- The chosen generator's cost is ≤ the max cost, so 1 + it ≤ 1 + the max
    rintro ⟨⟨i, hge, hle⟩, _⟩ _ ⟨g, _⟩ _
    dsimp
    specialize hcost_le i (hidx ⟨i, hge, hle⟩) g
    omega

/-- `frequency`'s cost function is upper-bounded by 1 +
    the max-valued cost function out of all the sub-generators -/
theorem IsBounded_frequency
    {gs : List (Nat × (Unit → SPMF.Cost α))}
    (hne : 0 < (List.map Prod.fst gs).sum)
    (hcost : ∀ g ∈ gs, {cost_g // IsBounded (g.2 ()) cost_g}) :
    IsBounded (frequency gs hne)
      (fun x => 1 + List.foldr (fun ⟨ (w, g), hg ⟩ acc => max ((hcost (w, g) hg).val x) acc) 0 gs.attach) := by
  -- Every generator's cost is ≤ the max cost over all generators.
  have hcost_le : ∀ (i : Nat) (hi : i < gs.length) (y : α),
      (hcost gs[i] (List.getElem_mem hi)).val y ≤
        List.foldr (fun ⟨ (w, g), hg ⟩ acc => max ((hcost (w, g) hg).val y) acc) 0 gs.attach := by
    intro i hi y
    -- Rewrite `foldr` over `attach` as a `foldr` plus a `map` via `List.foldr_map`
    rw [← List.foldr_map]
    apply List.le_max_of_le'
    . apply List.mem_map.mpr
      . exists ⟨gs[i], List.getElem_mem hi⟩
        constructor
        . apply List.mem_attach
        . rfl
    . constructor
  unfold frequency Helpers.frequencyAux
  -- We need to instantiate `cx`/`cf` explicitly here, otherwise unification times out
  apply IsBounded_bind
    (cx := fun _ => 1)
    (cf := fun _ x => List.foldr (fun ⟨(w, g), hg⟩ acc => max ((hcost (w, g) hg).val x) acc) 0 gs.attach)
  . -- IsBounded (ULift.down <$> choose 0 ((List.map Prod.fst gs).sum - 1) ⋯) (fun _ => 1)
    apply IsBounded_map
    . apply IsBounded_choose
    . intro (i, w) hi
      apply le_refl
  . -- ∀ x, IsBounded (if x < (Prod.fst <$> gs).sum then ... else ...) (List.foldr ... 0 gs)
    rintro ⟨n, hge, hle⟩
    dsimp only
    -- `frequencySelect` has an `if`-expression that cases on whether `n < (Prod.fst <$> gs).sum`,
    -- we case on this
    split
    . -- In this case, we have `n ≤ (List.map Prod.fst gs).sum`, so
      -- `frequencyAux` calls `frequencySelect`.
      -- Here we use the fact that `frequencySelect` is bounded...
      obtain ⟨w, g, hwg, _, heq⟩ := SPMF.frequencySelect_mem (by assumption)
      -- We name the chosen sub-generator's cost function `cost_g : α → Nat`.
      -- `set` (not `have`) rewrites every occurrence, including inside `hbounded`,
      -- so the remaining goal is phrased in terms of `cost_g` throughout.
      set cost_g : α → Nat := (hcost (w, g) hwg).val with hcost_g
      -- `frequencySelect` reduces to the chosen generator `g ()`, which `hcost` bounds
      rw [heq]
      have hbounded : IsBounded (g ()) cost_g := (hcost (w, g) hwg).property
      -- ...along the fact that the `IsBounded` relation is monotonic over `≤`
      apply IsBounded_mono hbounded
      -- Now we just need to show that `cost_g` is less than
      -- `List.foldr (fun ... acc => max <some_cost_function> acc) 0 gs.attach`
      intro x
      -- Now we rewrite the RHS into
      -- the form `List.foldr max 0 (List.map <cost_function> gs.attach)`
      rw [← List.foldr_map]
      -- We use the fact that the cost of each sub-generator
      -- is upper-bounded by the `max` of all sub-generators' costs.
      -- (We instantiate the variable `x` of the `List.le_max_of_le'` lemma
      -- here to make subsequent goals clearer.)
      apply List.le_max_of_le' (x := cost_g x)
      . -- `cost_g x ∈ List.map <cost_function> gs`
        apply List.mem_map.mpr
        exists ⟨(w, g), hwg⟩
        constructor
        . apply List.mem_attach
        . rfl
      . apply le_refl
    . -- In this case, we have `¬ n ≤ (List.map Prod.fst gs).sum`,
      -- so `frequencyAux` ends up using the `default` generator instead.
      -- The fallback `default` generator has empty support, so it is bounded by anything.
      apply IsBounded_default
  . -- The bound for the cost function for the continuation (after the bind) is tight
    dsimp
    intro p hp q hq
    apply le_refl


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

/-- Note: this proof is very similar to `List.arbitrary_cost` in `BasaltExamples/ArbList.lean`,
    except the cost function now comprises the following:
    - `2 * xs.length`: 2 random choices for each element in `xs` (a call to `pick` and a call to `g`)
    - `(cost_g <$> xs).sum`: Need to apply `g`'s cost function to each generated element and sum them
    - `1`: one final call to `pick` to produce the end of the list -/
theorem IsBounded_listOf
    {g : SPMF.Cost α}
    (hx : IsBounded g cost_g) :
    IsBounded (listOf g) (fun xs => 2 * xs.length + (cost_g <$> xs).sum + 1) := by
  open Lean.Order in
  delta listOf
  apply fix_induct (motive := fun (g : SPMF.Cost (List α)) => IsBounded g
    (fun xs => 2 * xs.length + (cost_g <$> xs).sum + 1)) _ ?admissible ?step
  case admissible =>
    apply admissible_IsBounded
  case step =>
    intro arbitrary_rec ih
    rw [IsBounded_iff] at ih ⊢
    rintro ⟨xs, c⟩ hxs
    simp only [SPMF.Cost.mem_support_pick_iff, SPMF.Cost.mem_support_bind_iff,
      SPMF.Cost.mem_support_pure_iff] at hxs
    obtain ⟨m, rfl, h | h⟩ := hxs
    · obtain ⟨rfl, rfl⟩ := h
      simp
    · obtain ⟨hd, n1, n2, hhd, ⟨tl, n3, n4, htl, ⟨rfl, hn4⟩, hn2⟩, hm⟩ := h
      have hhead : n1 ≤ cost_g hd := IsBounded_iff.mp hx (hd, n1) hhd
      have htail : n3 ≤ 2 * tl.length + (List.map cost_g tl).sum + 1 := ih (tl, n3) htl
      show 1 + m ≤ 2 * (hd :: tl).length + (List.map cost_g (hd :: tl)).sum + 1
      simp only [List.length_cons, List.map_cons, List.sum_cons]
      omega
