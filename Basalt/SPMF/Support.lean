/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt.Combinators.QuickCheck
import Basalt.Obs.Presentation
import Basalt.SPMF.Expect.Obs

/-!
# SPMF Support

Support inversion for the host constructs (`bind`, `pure`, `map`, `ite`, `dite`, `choose`), stated
on monad notation, which is what do-notation elaborates to; the may and always observations built
from them; and the support laws of the list combinators, which the walker's rules bridge. A
combinator's support is otherwise not a lemma: it is what `walk` computes from its `Obs.map_*`.
-/

open Lean.Order RandomChoice NNReal ENNReal MeasureTheory

namespace SPMF

section support

@[simp]
theorem mem_support_bind_iff
    {x : SPMF α}
    {f : α → SPMF β} :
    b ∈ (x >>= f).support ↔ ∃ a ∈ x.support, b ∈ (f a).support := by
  rw [mem_support_iff_prob_pos, prob_bind, expect_pos_iff]
  simp only [← mem_support_iff_prob_pos]

@[simp]
theorem support_bind
    {x : SPMF α}
    {f : α → SPMF β} :
    (x >>= f).support = {b | ∃ a, a ∈ x.support ∧ b ∈ (f a).support} := by
  ext b
  simp only [mem_support_bind_iff, Set.mem_ofPred_eq]

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
theorem mem_support_pure_iff :
    b ∈ (Pure.pure a : SPMF α).support ↔ b = a := by
  simp [support_pure]

@[simp]
theorem support_map
    {x : SPMF α}
    {f : α → β} :
    (f <$> x).support = {b | ∃ a, a ∈ x.support ∧ b = f a} := by
  rw [← LawfulMonad.bind_pure_comp]
  simp only [support_bind, support_pure]
  grind

@[simp]
theorem mem_support_map_iff
    {x : SPMF α}
    {f : α → β} :
    b ∈ (f <$> x).support ↔ ∃ a ∈ x.support, b = f a := by
  simp [support_map]

@[simp]
theorem mem_support_dite_iff {p : Prop} [Decidable p]
    {t : p → SPMF α} {e : ¬p → SPMF α} :
    a ∈ (dite p t e).support ↔ (∃ h : p, a ∈ (t h).support) ∨ (∃ h : ¬p, a ∈ (e h).support) := by
  by_cases hp : p <;> simp_all

@[simp]
theorem mem_support_ite_iff {p : Prop} [Decidable p]
    {t e : SPMF α} :
    a ∈ (ite p t e).support ↔ (p ∧ a ∈ t.support) ∨ (¬p ∧ a ∈ e.support) := by
  by_cases hp : p <;> simp_all

@[simp]
theorem support_choose :
    (choose lo hi h : SPMF (ULift {x : Nat // lo ≤ x ∧ x ≤ hi})).support = Set.univ := by
  ext a
  simp only [mem_support_iff, Set.mem_univ, iff_true]
  change (1 : ℝ≥0∞) / ((hi - lo + 1 : ℕ)) ≠ 0
  simp

@[simp]
theorem mem_support_choose_iff :
    a ∈ (choose lo hi h : SPMF (ULift {x : Nat // lo ≤ x ∧ x ≤ hi})).support ↔ True := by
  simp [support_choose]

section observations

/-- The may observation: some value the generator can produce satisfies the postcondition. -/
def mayObs : Obs SPMF.{u} (WP Mix.angelic) where
  spec g := fun Q => ∃ a ∈ g.support, Q a
  map_pure a := by
    funext Q; apply propext
    exact ⟨fun ⟨b, hb, h⟩ => mem_support_pure_iff.mp hb ▸ h,
      fun h => ⟨a, mem_support_pure_iff.mpr rfl, h⟩⟩
  map_bind x k := by
    funext Q; apply propext
    show (∃ b ∈ (x >>= k).support, Q b) ↔ ∃ a ∈ x.support, ∃ b ∈ (k a).support, Q b
    simp only [mem_support_bind_iff]
    exact ⟨fun ⟨b, ⟨a, ha, hb⟩, h⟩ => ⟨a, ha, b, hb, h⟩, fun ⟨a, ha, b, hb, h⟩ => ⟨b, ⟨a, ha, hb⟩, h⟩⟩
  map_choose lo hi h := by
    funext Q; apply propext
    exact ⟨fun ⟨a, _, h⟩ => ⟨a, h⟩, fun ⟨a, h⟩ => ⟨a, mem_support_choose_iff.mpr trivial, h⟩⟩

/-- The always observation: every value the generator can produce satisfies the postcondition. -/
def alwaysObs : Obs SPMF.{u} (WP Mix.demonic) where
  spec g := fun Q => ∀ a ∈ g.support, Q a
  map_pure a := by
    funext Q; apply propext
    exact ⟨fun h => h a (mem_support_pure_iff.mpr rfl), fun h b hb => mem_support_pure_iff.mp hb ▸ h⟩
  map_bind x k := by
    funext Q; apply propext
    show (∀ b ∈ (x >>= k).support, Q b) ↔ ∀ a ∈ x.support, ∀ b ∈ (k a).support, Q b
    simp only [mem_support_bind_iff]
    exact ⟨fun h a ha b hb => h b ⟨a, ha, hb⟩, fun h b ⟨a, ha, hb⟩ => h a ha b hb⟩
  map_choose lo hi h := by
    funext Q; apply propext
    exact ⟨fun hq x => hq x (mem_support_choose_iff.mpr trivial), fun hq a _ => hq a⟩

instance : mayObs.Monotone := ⟨fun _ _ _ h ⟨a, ha, hp⟩ => ⟨a, ha, h a hp⟩⟩

instance : alwaysObs.Monotone := ⟨fun _ _ _ h hp a ha => h a (hp a ha)⟩

/-- Support membership is the may observation at the postcondition `(· = a)`. -/
theorem mem_support_iff_may {g : SPMF α} {a : α} : a ∈ g.support ↔ mayObs.spec g (· = a) :=
  ⟨fun h => ⟨a, h, rfl⟩, fun ⟨_, hb, e⟩ => e ▸ hb⟩

/-- Support membership, read through a specification the may observation equals. -/
theorem mem_support_of_may {g : SPMF α} {w : WP Mix.angelic α} (h : mayObs.spec g = w) {a : α} :
    a ∈ g.support ↔ w (· = a) :=
  mem_support_iff_may.trans (iff_of_eq (congrFun h _))

end observations

/-- The support of `oneOf gs` is exactly the union of all generators in `gs` -/
@[simp]
theorem support_oneOf
    {gs : List (Unit → SPMF α)}
    (hne : gs ≠ []) :
    support (oneOf gs hne) = {a | ∃ g ∈ gs, a ∈ (g ()).support} := by
  ext a
  exact (mem_support_of_may (mayObs.map_oneOf gs hne)).trans
    ((Mix.index_angelic gs hne fun g => mayObs.spec (g ()) (· = a)).trans
      (exists_congr fun g => and_congr_right fun _ => mem_support_iff_may.symm))

/-- The support of `vectorOf n g` is the set of all length-`n` list where each element is in `g`'s
support. -/
theorem support_vectorOf
    {n : Nat}
    {g : SPMF α} :
    support (vectorOf n g) = { xs | List.length xs = n ∧ ∀ x ∈ xs, x ∈ g.support } := by
  induction n with
  | zero =>
    simp [vectorOf]
    ext a
    constructor
    . intro h
      rw [Set.mem_singleton_iff] at h
      constructor
      . assumption
      . intro x hmem
        subst h
        contradiction
    . intro h
      obtain ⟨heq, hmem⟩ := h
      apply Set.mem_singleton_iff.mpr
      assumption
  | succ n' IH =>
    rw [vectorOf_succ]
    ext xs
    simp
    constructor
    . intro h
      obtain ⟨x, ⟨hmem, ⟨xs, ⟨hxs, hcons⟩⟩⟩⟩ := h
      subst hcons
      rw [IH] at hxs
      dsimp at hxs
      obtain ⟨hlen, hsupp⟩ := hxs
      constructor
      . simp
        assumption
      . intro y hy
        rw [List.mem_cons] at hy
        obtain ⟨heq, hy⟩ := hy
        . assumption
        . apply hsupp
          assumption
    . intro ⟨hlen, hmem⟩
      obtain ⟨y, ys, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
      exists y
      constructor
      . apply hmem
        apply List.mem_cons_self
      . exists ys
        constructor
        . rw [IH]
          apply Set.mem_sep
          . simp at hlen
            assumption
          . intro x hx
            apply hmem
            apply List.mem_cons_of_mem
            assumption
        . rfl

/-- Membership form of `support_vectorOf`. -/
@[simp]
theorem mem_support_vectorOf_iff
    {n : Nat}
    {g : SPMF α} :
    xs ∈ (vectorOf n g).support ↔ xs.length = n ∧ ∀ x ∈ xs, x ∈ g.support := by
  simp [support_vectorOf]


/-- The support of `listOfMaxLength n g` is the set of all lists with length at most `n`, where each
element is in `g`'s support -/
theorem support_listOfMaxLength
    {n : Nat}
    {g : SPMF α} :
    support (listOfMaxLength n g) = { xs | List.length xs ≤ n ∧ ∀ x ∈ xs, x ∈ g.support } := by
  simp [listOfMaxLength]

@[simp]
theorem mem_support_listOfMaxLength_iff
    {n : Nat}
    {g : SPMF α} :
    xs ∈ (listOfMaxLength n g).support ↔ xs.length ≤ n ∧ ∀ x ∈ xs, x ∈ g.support := by
  simp [support_listOfMaxLength]

/-- The support of `listOf g` is the set of all lists where each element is in `g`'s support -/
theorem support_listOf
    {g : SPMF α} :
    support (listOf g) = { xs | ∀ x ∈ xs, x ∈ g.support } := by
  ext xs
  induction xs with
  | nil =>
    dsimp
    constructor
    . intro h x hvacuous
      contradiction
    . intro h
      unfold listOf
      simp [support_oneOf]
  | cons x xs' IH =>
    constructor
    . dsimp
      intro h y hy
      cases hy with
      | head =>
        unfold listOf at h
        simp [support_oneOf] at h
        obtain ⟨h1, _⟩ := h
        assumption
      | tail =>
        rename_i hy
        unfold listOf at h
        simp [support_oneOf] at h
        obtain ⟨_, h2⟩ := h
        rw [IH] at h2
        apply h2
        assumption
    . intro h
      rw [Set.mem_ofPred_eq] at h
      unfold listOf
      simp [support_oneOf]
      constructor
      . apply h
        apply List.mem_cons_self
      . apply IH.mpr
        rw [Set.mem_ofPred_eq]
        intro x hx
        apply h
        apply List.mem_cons_of_mem
        assumption

/-- The support of `nonEmptyListOf g` is the set of all *non-empty* lists where each element
    is in `g`'s support -/
theorem support_nonEmptyListOf
    {g : SPMF α} :
    support (nonEmptyListOf g) = { xs | xs ≠ [] ∧ ∀ x ∈ xs, x ∈ g.support } := by
  ext xs
  induction xs with
  | nil =>
    dsimp
    constructor
    . intro h
      unfold nonEmptyListOf at h
      simp [support_oneOf] at h
    . intro ⟨hneq, hmem⟩
      contradiction
  | cons x xs' IH =>
    constructor
    . dsimp
      intro hy
      constructor
      . apply List.cons_ne_nil
      . intro y hy
        cases hy with
        | head =>
          unfold nonEmptyListOf at hy
          simp [support_oneOf] at hy
          rcases hy with ⟨h, _⟩ | ⟨h, _⟩ <;> assumption
        | tail =>
          rename_i hmem
          unfold nonEmptyListOf at hy
          simp [support_oneOf] at hy
          rcases hy with ⟨_, hxs⟩ | ⟨_, hxs⟩
          · subst hxs
            contradiction
          · apply (IH.mp hxs).2
            assumption
    . intro h
      rw [Set.mem_ofPred_eq] at h
      unfold nonEmptyListOf
      simp [support_oneOf]
      obtain ⟨h1, h2⟩ := h
      have hx : x ∈ g.support := by
        apply h2
        apply List.mem_cons_self
      by_cases he : xs' = []
      · left
        constructor <;> assumption
      · right
        constructor
        . assumption
        . apply IH.mpr
          apply Set.mem_ofPred.mpr
          constructor
          . assumption
          . intro w hw
            apply h2
            apply List.mem_cons_of_mem
            assumption


@[simp]
theorem mem_support_listOf
    {xs : List α}
    {g : SPMF α} :
    xs ∈ (listOf g).support ↔ xs ∈ {xs | ∀ x ∈ xs, x ∈ g.support} := by
  simp [support_listOf]

@[simp]
theorem mem_support_nonEmptylistOf
    {xs : List α}
    {g : SPMF α} :
    xs ∈ (nonEmptyListOf g).support ↔ xs ∈ {xs | xs ≠ [] ∧ ∀ x ∈ xs, x ∈ g.support} := by
  simp [support_nonEmptyListOf]

/-- The support of `permutationOf xs` is the set of all values of the subtype `{ys // xs ~ ys}`,
    i.e. all possible permutations of `xs`.  -/
theorem support_permutationOf {α} {xs : List α} :
    support (permutationOf xs) = Set.univ := by
  ext z
  simp only [Set.mem_univ, iff_true]
  induction xs with
  | nil =>
    obtain ⟨zs, hz⟩ := z
    have : zs = [] := List.Perm.eq_nil hz.symm
    subst this
    rw [permutationOf]
    simp
  | cons x xs ih =>
    obtain ⟨zs, hz⟩ := z
    -- `x` occurs at some index `n` of `zs`.
    obtain ⟨n, hn, hxn⟩ := List.mem_iff_getElem.mp (hz.mem_iff.mp List.mem_cons_self)
    -- Erasing that index and reinserting `x` there recovers `zs` (the inverse of one step).
    have hinv : (zs.eraseIdx n).insertIdx n x = zs := by
      rw [← hxn]; exact List.insertIdx_eraseIdx_getElem hn
    have hle : n ≤ (zs.eraseIdx n).length := by rw [List.length_eraseIdx_of_lt hn]; omega
    -- Peel the head off both sides to get a permutation of the tail.
    have hzperm : zs.Perm (x :: zs.eraseIdx n) := by
      conv_lhs => rw [← hinv]
      exact List.perm_insertIdx x (zs.eraseIdx n) hle
    have htail : xs.Perm (zs.eraseIdx n) := List.Perm.cons_inv (hz.trans hzperm)
    rw [permutationOf]
    simp only [mem_support_bind_iff, mem_support_map_iff, mem_support_choose_iff, true_and]
    -- Witnesses: the recursive result `⟨zs.eraseIdx n, htail⟩` and the insertion index `n`.
    refine ⟨⟨zs.eraseIdx n, htail⟩, ih _, ⟨n, by omega, hle⟩,
      ⟨ULift.up ⟨n, by omega, hle⟩, rfl⟩, ?_⟩
    exact mem_support_pure_iff.mpr (Subtype.ext hinv.symm)

/-- Membership form of `support_permutationOf` -/
@[simp]
theorem mem_support_permutationOf_iff {α} {xs : List α} {z : { ys // xs.Perm ys }} :
    z ∈ support (permutationOf xs : SPMF _) ↔ True := by
  rw [support_permutationOf]; exact iff_of_true (Set.mem_univ z) trivial

/-- If the sum of weights in `gs` is non-zero, then the support of `frequency gs` is exactly the
union of the support of the generators in `gs` with non-zero weights. -/
@[simp]
theorem support_frequency
    {gs : List (Nat × (Unit → SPMF α))}
    (h_pos : 0 < List.sum (List.map Prod.fst gs)) :
    support (frequency gs h_pos) = {a | ∃ w g, ⟨ w, g ⟩ ∈ gs ∧ 0 < w ∧ a ∈ (g ()).support} := by
  ext a
  refine (mem_support_of_may (mayObs.map_frequency gs h_pos)).trans ?_
  simp only [Obs.select, WP.choose_bind_apply, Obs.selectD_map (fun w : WP Mix.angelic α => w (· = a)), List.map_map]
  refine (Mix.select_angelic _ (by simp [Function.comp_def]) h_pos _).trans ?_
  constructor
  · rintro ⟨_, hp, hw, ha⟩
    obtain ⟨⟨w, g⟩, hmem, rfl⟩ := List.mem_map.mp hp
    exact ⟨w, g, hmem, hw, mem_support_iff_may.mpr ha⟩
  · rintro ⟨w, g, hmem, hw, ha⟩
    exact ⟨_, List.mem_map.mpr ⟨(w, g), hmem, rfl⟩, hw, mem_support_iff_may.mp ha⟩

theorem bind_congr_support
    {x : SPMF α}
    (h : ∀ a ∈ x.support, f a = g a) :
    bind x f = bind x g := by
  simp only [bind]
  ext a
  simp only [DFunLike.coe]
  congr
  funext v
  by_cases hsupport : v ∈ x.support
  · rwa [h]
  · simp only [support, Function.notMem_support] at hsupport
    simp_all [DFunLike.coe]

theorem mem_support_csup {c : SPMF α → Prop} (hc : chain c) {a : α} :
    a ∈ (CCPO.csup hc).support ↔ ∃ f, c f ∧ a ∈ f.support := by
  simp only [mem_support_iff_prob_pos, prob, expect_csup, lt_iSup_iff, exists_prop]

/-- A value is reachable by `suchThat g p` exactly when `g` reaches it and `p` accepts it, whatever
the chance of acceptance: the first draw can be that value. -/
theorem mem_support_suchThat {g : SPMF α} {p : α → Bool} {a : α} :
    a ∈ (suchThat g p).support ↔ a ∈ g.support ∧ p a = true := by
  have key : ∀ a ∈ (suchThat g p).support, a ∈ g.support ∧ p a = true := by
    refine suchThat.fixpoint_induct g p (fun x => ∀ a ∈ x.support, a ∈ g.support ∧ p a = true)
      (fun c hc ih a ha => ?_) (fun z ih a ha => ?_)
    · obtain ⟨x, hxc, hxa⟩ := (mem_support_csup hc).mp ha
      exact ih x hxc a hxa
    · obtain ⟨b, hb, hab⟩ := mem_support_bind_iff.mp ha
      split at hab
      · exact (mem_support_pure_iff.mp hab) ▸ ⟨hb, ‹_›⟩
      · exact ih a hab
  refine ⟨key a, fun ⟨ha, hp⟩ => ?_⟩
  rw [suchThat]
  exact mem_support_bind_iff.mpr ⟨a, ha, by simp only [hp, ↓reduceIte, mem_support_pure_iff]⟩

/-- Reweighting a uniform choice preserves its support. Replacing `oneOf gs` by a `frequency`
over the same branches leaves the set of reachable values unchanged, provided every weight is
positive. -/
theorem support_frequency_reweight
    {gs : List (Unit → SPMF α)} {gs' : List (Nat × (Unit → SPMF α))}
    (hsnd : gs'.map Prod.snd = gs) (hpos : ∀ p ∈ gs', 0 < p.1)
    (hne : gs ≠ []) (h_pos : 0 < List.sum (List.map Prod.fst gs')) :
    support (frequency gs' h_pos) = support (oneOf gs hne) := by
  subst hsnd
  rw [support_frequency, support_oneOf]
  ext a
  simp only [Set.mem_ofPred_eq, List.mem_map]
  constructor
  · rintro ⟨w, g, hmem, _, ha⟩
    exact ⟨g, ⟨(w, g), hmem, rfl⟩, ha⟩
  · rintro ⟨g, ⟨⟨w, g'⟩, hmem, hg⟩, ha⟩
    cases hg
    exact ⟨w, g', hmem, hpos _ hmem, ha⟩

/-- The same, between two `frequency`s. This is the shape a tuning rewrite has: `@[tunable]`
replaces literal weights by `Tuning.weight θ i d` in place, so both sides are already `frequency`s
and only the weights differ. -/
theorem support_frequency_congr_weights
    {gs gs' : List (Nat × (Unit → SPMF α))}
    (hsnd : gs'.map Prod.snd = gs.map Prod.snd)
    (hpos : ∀ p ∈ gs', 0 < p.1) (hpos' : ∀ p ∈ gs, 0 < p.1)
    (h : 0 < List.sum (List.map Prod.fst gs)) (h' : 0 < List.sum (List.map Prod.fst gs')) :
    support (frequency gs' h') = support (frequency gs h) := by
  rw [support_frequency, support_frequency]
  ext a
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨w, g, hmem, _, ha⟩
    have : g ∈ gs.map Prod.snd := hsnd ▸ List.mem_map.mpr ⟨(w, g), hmem, rfl⟩
    obtain ⟨⟨w', g'⟩, hmem', hg⟩ := List.mem_map.mp this
    cases hg
    exact ⟨w', g', hmem', hpos' _ hmem', ha⟩
  · rintro ⟨w, g, hmem, _, ha⟩
    have : g ∈ gs'.map Prod.snd := hsnd ▸ List.mem_map.mpr ⟨(w, g), hmem, rfl⟩
    obtain ⟨⟨w', g'⟩, hmem', hg⟩ := List.mem_map.mp this
    cases hg
    exact ⟨w', g', hmem', hpos _ hmem', ha⟩

theorem mem_support_chooseNat_iff {lo hi k : Nat} {h : lo ≤ hi} :
    k ∈ (chooseNat lo hi h : SPMF Nat).support ↔ lo ≤ k ∧ k ≤ hi := by
  unfold chooseNat
  simp only [mem_support_map_iff, mem_support_choose_iff, true_and]
  constructor
  · rintro ⟨⟨⟨x, hx⟩⟩, rfl⟩
    exact hx
  · intro hk
    exact ⟨⟨⟨k, hk⟩⟩, rfl⟩

theorem mem_support_chooseInt_iff {lo hi k : Int} {h : lo ≤ hi} :
    k ∈ (chooseInt lo hi h : SPMF Int).support ↔ lo ≤ k ∧ k ≤ hi := by
  unfold chooseInt
  simp only [mem_support_bind_iff, mem_support_chooseNat_iff, mem_support_pure_iff]
  constructor
  · rintro ⟨j, ⟨-, hj⟩, rfl⟩
    omega
  · intro hk
    exact ⟨(k - lo).toNat, ⟨Nat.zero_le _, by omega⟩, by omega⟩

/-! ## QuickCheck's combinators

The support laws of the combinators `QuickCheck` adds that read no size; the others are these, or
the ones above, once a size is chosen (`size_erasure`). -/

section quickCheck

open QuickCheck

theorem mem_support_sublistOf_iff {xs ys : List α} :
    ys ∈ (sublistOf xs : SPMF (List α)).support ↔ ys.Sublist xs := by
  induction xs generalizing ys with
  | nil => simp [sublistOf]
  | cons x xs ih =>
    simp only [sublistOf, mem_support_bind_iff, mem_support_chooseNat_iff, mem_support_pure_iff, ih,
      List.sublist_cons_iff]
    constructor
    · rintro ⟨keep, -, zs, hzs, rfl⟩
      split
      · exact Or.inr ⟨zs, rfl, hzs⟩
      · exact Or.inl hzs
    · rintro (h | ⟨r, rfl, h⟩)
      · exact ⟨0, by omega, ys, h, by simp⟩
      · exact ⟨1, by omega, r, h, by simp⟩

theorem perm_of_mem_support_shuffle {xs ys : List α}
    (h : ys ∈ (shuffle xs : SPMF (List α)).support) : ys.Perm xs := by
  unfold shuffle at h
  simp only [mem_support_bind_iff, mem_support_vectorOf_iff, mem_support_pure_iff] at h
  obtain ⟨ks, ⟨hlen, -⟩, rfl⟩ := h
  have := (List.mergeSort_perm (ks.zip xs) fun a b => decide (a.1 ≤ b.1)).map Prod.snd
  rwa [List.map_snd_zip (by omega)] at this

/-- Keys for `xs` that pair its entries as `zs` pairs those of `ys`, for any `zs` of that length. -/
private theorem exists_keys_zip_perm {xs ys : List α} (h : xs.Perm ys) :
    ∀ zs : List Int, zs.length = ys.length →
      ∃ ks : List Int, ks.Perm zs ∧ (ks.zip xs).Perm (zs.zip ys) := by
  induction h with
  | nil =>
    intro zs hz
    exact ⟨zs, List.Perm.refl _, by simp⟩
  | cons x _ ih =>
    rintro (_ | ⟨z, zs⟩) hz
    · simp at hz
    · obtain ⟨ks, hk, hz'⟩ := ih zs (by simpa using hz)
      exact ⟨z :: ks, hk.cons z, by simpa using hz'.cons (z, x)⟩
  | swap x y l =>
    rintro (_ | ⟨a, _ | ⟨b, zs⟩⟩) hz
    · simp at hz
    · simp at hz
    · exact ⟨b :: a :: zs, List.Perm.swap a b zs, by simpa using List.Perm.swap (a, x) (b, y) _⟩
  | trans h₁₂ h₂₃ ih₁ ih₂ =>
    intro zs hz
    obtain ⟨ks₂, hk₂, h₂⟩ := ih₂ zs hz
    obtain ⟨ks₁, hk₁, h₁⟩ := ih₁ ks₂ (by rw [hk₂.length_eq, hz, h₂₃.length_eq])
    exact ⟨ks₁, hk₁.trans hk₂, h₁.trans h₂⟩

/-- Every permutation, for a list short enough to give each entry its own 64-bit key: past that,
keys tie, and a stable sort keeps tied entries in order. -/
theorem mem_support_shuffle_of_perm {xs ys : List α} (hn : xs.length ≤ 2 ^ 64)
    (h : ys.Perm xs) : ys ∈ (shuffle xs : SPMF (List α)).support := by
  have hn : xs.length ≤ 18446744073709551616 := by simpa using hn
  let zs : List Int := (List.range xs.length).map fun j : Nat => (j : Int) - 9223372036854775808
  have hzlen : zs.length = ys.length := by simp [zs, h.length_eq]
  obtain ⟨ks, hks, hperm⟩ := exists_keys_zip_perm h.symm zs hzlen
  unfold shuffle
  simp only [mem_support_bind_iff, mem_support_vectorOf_iff, mem_support_chooseInt_iff,
    mem_support_pure_iff]
  refine ⟨ks, ⟨by simp [hks.length_eq, zs], fun k hk => ?_⟩, ?_⟩
  · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp (hks.subset hk)
    have := List.mem_range.mp hj
    omega
  · have hM := (List.mergeSort_perm (ks.zip xs) fun a b => decide (a.1 ≤ b.1)).trans hperm
    have hnodup : ((zs.zip ys).map Prod.fst).Nodup := by
      rw [List.map_fst_zip (by omega)]
      exact List.nodup_range.map fun a b hab => by simpa using hab
    have hP : (zs.zip ys).Pairwise fun a b => a.1 ≤ b.1 := by
      rw [List.pairwise_iff_getElem]
      intro i j hi hj hij
      simp [zs, List.getElem_zip]
      omega
    have hsorted := List.pairwise_mergeSort (le := fun a b : Int × α => decide (a.1 ≤ b.1))
      (fun a b c hab hbc => by simp at *; omega) (fun a b => by simp; omega) (ks.zip xs)
    rw [List.Perm.eq_of_pairwise (le := fun a b : Int × α => a.1 ≤ b.1)
      (fun a b ha hb hab hba =>
        List.inj_on_of_nodup_map hnodup (hM.subset ha) hb (le_antisymm hab hba))
      (hsorted.imp fun h => by simpa using h) hP hM, List.map_snd_zip (by omega)]

theorem mem_support_trySizes {gs : Nat → SPMF α} {f : α → Option β} {m k : Nat} {b : β}
    (h : some b ∈ (trySizes gs f m k).support) :
    ∃ j a, m ≤ j ∧ j < m + k ∧ a ∈ (gs j).support ∧ f a = some b := by
  induction k generalizing m with
  | zero => simp [trySizes] at h
  | succ k ih =>
    simp only [trySizes, mem_support_bind_iff] at h
    obtain ⟨a, ha, hb⟩ := h
    split at hb
    · exact ⟨m, a, le_rfl, by omega, ha, (mem_support_pure_iff.mp hb).symm⟩
    · obtain ⟨j, a', hj, hj', ha', hf⟩ := ih hb
      exact ⟨j, a', by omega, by omega, ha', hf⟩

/-- The first draw can be the one `f` accepts. -/
theorem some_mem_support_trySizes {gs : Nat → SPMF α} {f : α → Option β} {m k : Nat} {a : α}
    {b : β} (ha : a ∈ (gs m).support) (hf : f a = some b) :
    some b ∈ (trySizes gs f m (k + 1)).support := by
  simp only [trySizes, mem_support_bind_iff]
  exact ⟨a, ha, by simp [hf]⟩

theorem mem_support_suchThatFrom {gs : Nat → SPMF α} {f : α → Option β} {n : Nat} {b : β}
    (h : b ∈ (suchThatFrom gs f n).support) :
    ∃ j a, n ≤ j ∧ a ∈ (gs j).support ∧ f a = some b := by
  refine suchThatFrom.fixpoint_induct gs f
    (fun z => ∀ n b, b ∈ (z n).support → ∃ j a, n ≤ j ∧ a ∈ (gs j).support ∧ f a = some b)
    (admissible_pi_apply
      (fun n (x : SPMF β) => ∀ b, b ∈ x.support → ∃ j a, n ≤ j ∧ a ∈ (gs j).support ∧ f a = some b)
      fun n c hc hall b hb => ?_) (fun z ih n b h => ?_) n b h
  · obtain ⟨x, hx, hb⟩ := (mem_support_csup hc).mp hb
    exact hall x hx b hb
  · obtain ⟨o, ho, hb⟩ := mem_support_bind_iff.mp h
    rcases o with _ | b'
    · obtain ⟨j, a, hj, ha, hf⟩ := ih (n + 1) b hb
      exact ⟨j, a, by omega, ha, hf⟩
    · obtain rfl := mem_support_pure_iff.mp hb
      obtain ⟨j, a, hj, -, ha, hf⟩ := mem_support_trySizes ho
      exact ⟨j, a, hj, ha, hf⟩

/-- The first draw, at size `n`, can be the one `f` accepts. -/
theorem mem_support_suchThatFrom_of {gs : Nat → SPMF α} {f : α → Option β} {n : Nat} {a : α}
    {b : β} (ha : a ∈ (gs n).support) (hf : f a = some b) :
    b ∈ (suchThatFrom gs f n).support := by
  rw [suchThatFrom]
  exact mem_support_bind_iff.mpr ⟨some b, some_mem_support_trySizes ha hf, by simp⟩

end quickCheck

end support

end SPMF
