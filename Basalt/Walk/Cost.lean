/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Mathlib.Data.ENat.Lattice
import Basalt.SPMF.Cost
import Basalt.Walk.Entry

/-!
# Walking Cost Bounds

What the walk needs of `SPMF.Cost.alwaysObs`, on which `IsCostBounded g c` is
`alwaysObs.spec g fun v n_v => n_v ≤ c v`: how a fact closes a leaf, the rules of the list
combinators, and the admissibility `walk fixpoint` inducts with. The worst-case cost of a combinator
term, which a list combinator falls back on when no fact bounds its argument, is an upper bound on
`SPMF.Cost.worstObs` in the `sup` algebra.
-/

open RandomChoice

namespace SPMF.Cost

open Lean.Order in
theorem alwaysObs.admissible (Q : α → Nat → Prop) :
    admissible fun x : SPMF.Cost α => alwaysObs.spec x Q := by
  intro c hc ih p hp
  rw [SPMF.mem_support_csup hc] at hp
  obtain ⟨x, hxc, hxp⟩ := hp
  exact ih x hxc p hxp

/-- A cost bound on a generator argument, when no fact gives one: the argument's worst case, a bound
that ignores the value. -/
theorem always_of_worst {g : SPMF.Cost α} {b : ℕ∞} {k : Nat}
    (h : worstObs.spec g (fun _ n => (n : ℕ∞)) ≤ b) (hb : b = (k : ℕ∞)) :
    alwaysObs.spec g fun _ n => n ≤ k := fun p hp =>
  Nat.cast_le.mp ((le_iSup₂_of_le p hp le_rfl).trans (h.trans hb.le))

/-! ## Leaves

A fact about a sub-generator is used under the postcondition the walk arrives with: what it has to
imply is the bound. -/

@[obs_leaf]
theorem le_always_of_always {x : SPMF.Cost α} {R p : α → Nat → Prop} (hx : alwaysObs.spec x R) :
    (∀ a n, R a n → p a n) ≤ alwaysObs.spec x p := fun h q hq => h _ _ (hx q hq)

/-! ## The combinators that take a generator

They ask for the generator's cost bound, which the list's postcondition says nothing about: a fact
supplies it, or else, in the rule declared after it, its worst case. -/

section generatorArgument

variable {α : Type} {g : SPMF.Cost α} {c : α → Nat} {p : List α → Nat → Prop}

private theorem always_vectorOf_sum (hg : alwaysObs.spec g fun a n => n ≤ c a) {k : Nat} :
    alwaysObs.spec (vectorOf k g : SPMF.Cost (List α)) fun a n => n ≤ (a.map c).sum := by
  induction k with
  | zero =>
    show alwaysObs.spec (Pure.pure [] : SPMF.Cost (List α)) _
    walk
    simp
  | succ k ih =>
    rw [vectorOf_succ]
    walk
    simp only [List.map_cons, List.sum_cons]
    omega

@[gen_rule]
theorem le_always_vectorOf {k : Nat} (hg : alwaysObs.spec g fun a n => n ≤ c a) :
    (∀ a n, n ≤ (a.map c).sum → p a n) ≤ alwaysObs.spec (vectorOf k g) p :=
  le_always_of_always (always_vectorOf_sum hg)

@[gen_rule]
theorem le_always_vectorOf_worst {k K : Nat} {b : ℕ∞}
    (hg : worstObs.spec g (fun _ n => (n : ℕ∞)) ≤ b) (hb : b = (K : ℕ∞)) :
    (∀ a n, n ≤ (a.map fun _ => K).sum → p a n) ≤ alwaysObs.spec (vectorOf k g) p :=
  le_always_vectorOf (always_of_worst hg hb)

private theorem always_listOfMaxLength {n : Nat} {Q : List α → Nat → Prop}
    (h : ∀ j, j ≤ n → alwaysObs.spec (vectorOf j g) fun a m => Q a (1 + 0 + m)) :
    alwaysObs.spec (listOfMaxLength n g) Q := by
  unfold listOfMaxLength
  refine (iff_of_eq <| congrFun ((alwaysObs.map_bind _ _).trans
    (congrArg (· >>= _) ((alwaysObs.map_map _ _).trans
      (congrArg _ (alwaysObs.map_choose 0 n (Nat.zero_le n)))))) Q).mpr ?_
  exact (Mix.range_demonic _).mpr fun j hj => h j hj.2

@[gen_rule]
theorem le_always_listOfMaxLength {k : Nat} (hg : alwaysObs.spec g fun a n => n ≤ c a) :
    (∀ a n, n ≤ 1 + (a.map c).sum → p a n) ≤ alwaysObs.spec (listOfMaxLength k g) p :=
  fun h => always_listOfMaxLength fun _ _ =>
    le_always_of_always (always_vectorOf_sum hg) fun a n hn => h a (1 + 0 + n) (by omega)

@[gen_rule]
theorem le_always_listOfMaxLength_worst {k K : Nat} {b : ℕ∞}
    (hg : worstObs.spec g (fun _ n => (n : ℕ∞)) ≤ b) (hb : b = (K : ℕ∞)) :
    (∀ a n, n ≤ 1 + (a.map fun _ => K).sum → p a n) ≤ alwaysObs.spec (listOfMaxLength k g) p :=
  le_always_listOfMaxLength (always_of_worst hg hb)

private theorem always_listOf (hg : alwaysObs.spec g fun a n => n ≤ c a) :
    alwaysObs.spec (listOf g : SPMF.Cost (List α)) fun a n =>
      n ≤ a.length + (a.map c).sum + 1 := by
  refine listOf.fixpoint_induct g _ (alwaysObs.admissible _) (fun listOf ih => ?_)
  walk
  all_goals simp only [List.length_cons, List.map_cons, List.sum_cons, List.length_nil,
    List.map_nil, List.sum_nil]; omega

private theorem always_nonEmptyListOf (hg : alwaysObs.spec g fun a n => n ≤ c a) :
    alwaysObs.spec (nonEmptyListOf g : SPMF.Cost (List α)) fun a n =>
      n ≤ a.length + (a.map c).sum := by
  refine nonEmptyListOf.fixpoint_induct g _ (alwaysObs.admissible _)
    (fun nonEmptyListOf ih => ?_)
  walk
  all_goals simp only [List.length_cons, List.map_cons, List.sum_cons, List.length_nil,
    List.map_nil, List.sum_nil]; omega

@[gen_rule]
theorem le_always_listOf (hg : alwaysObs.spec g fun a n => n ≤ c a) :
    (∀ a n, n ≤ a.length + (a.map c).sum + 1 → p a n) ≤ alwaysObs.spec (listOf g) p :=
  le_always_of_always (always_listOf hg)

@[gen_rule]
theorem le_always_listOf_worst {K : Nat} {b : ℕ∞}
    (hg : worstObs.spec g (fun _ n => (n : ℕ∞)) ≤ b) (hb : b = (K : ℕ∞)) :
    (∀ a n, n ≤ a.length + (a.map fun _ => K).sum + 1 → p a n) ≤ alwaysObs.spec (listOf g) p :=
  le_always_listOf (always_of_worst hg hb)

@[gen_rule]
theorem le_always_nonEmptyListOf (hg : alwaysObs.spec g fun a n => n ≤ c a) :
    (∀ a n, n ≤ a.length + (a.map c).sum → p a n) ≤ alwaysObs.spec (nonEmptyListOf g) p :=
  le_always_of_always (always_nonEmptyListOf hg)

@[gen_rule]
theorem le_always_nonEmptyListOf_worst {K : Nat} {b : ℕ∞}
    (hg : worstObs.spec g (fun _ n => (n : ℕ∞)) ≤ b) (hb : b = (K : ℕ∞)) :
    (∀ a n, n ≤ a.length + (a.map fun _ => K).sum → p a n) ≤
      alwaysObs.spec (nonEmptyListOf g) p :=
  le_always_nonEmptyListOf (always_of_worst hg hb)

end generatorArgument

end SPMF.Cost

/-! ## Worst-case costs

A combinator term passed as a generator argument has no law to supply its cost bound; its worst
case, the most choices any run can make, is `SPMF.Cost.worstObs`, and these are its bounds in the
`sup` algebra. -/

namespace SPMF.Cost

@[obs_leaf]
theorem worst_le_add_of_le {x : SPMF.Cost α} {p : α → Nat → ℕ∞} {k B : ℕ∞}
    (hx : worstObs.spec x (fun _ n => (n : ℕ∞)) ≤ B) (hp : ∀ a n, p a n = k + (n : ℕ∞)) :
    worstObs.spec x p ≤ k + B :=
  iSup₂_le fun q hq => (hp q.1 q.2).le.trans
    (add_le_add le_rfl ((le_iSup₂_of_le q hq le_rfl).trans hx))

@[obs_leaf]
theorem worst_le_add_of_always {x : SPMF.Cost α} {p : α → Nat → ℕ∞} {k : ℕ∞} {K : Nat}
    (hx : alwaysObs.spec x fun _ n => n ≤ K) (hp : ∀ a n, p a n = k + (n : ℕ∞)) :
    worstObs.spec x p ≤ k + (K : ℕ∞) :=
  worst_le_add_of_le (iSup₂_le fun q hq => Nat.cast_le.mpr (hx q hq)) hp

end SPMF.Cost

namespace Mix

@[gen_rule] theorem sup_range_le {lo hi : Nat} {h : lo ≤ hi}
    {F : ULift.{u} {x : Nat // lo ≤ x ∧ x ≤ hi} → ℕ∞} {d : ℕ∞}
    (hF : ∀ x (hx : lo ≤ x ∧ x ≤ hi), F ⟨⟨x, hx⟩⟩ ≤ d) : Mix.sup.range lo hi h F ≤ d :=
  iSup_le fun a => hF _ a.down.property

@[gen_rule] theorem sup_threshold_le {n : Nat} {k : ℤ} {t e c d : ℕ∞} (ht : t ≤ c) (he : e ≤ d) :
    (Mix.sup.{u}).threshold n k t e ≤ max c d := by
  refine iSup_le fun a => ?_
  dsimp only
  split
  · exact ht.trans (le_max_left _ _)
  · exact he.trans (le_max_right _ _)

private theorem le_foldr_max {γ : Type v} {F : γ → ℕ∞} {cs : List ℕ∞} {l : List γ}
    (h : List.Forall₂ (fun c g => F g ≤ c) cs l) : ∀ g ∈ l, F g ≤ cs.foldr max 0 := by
  induction h with
  | nil => simp
  | cons hc _ ih =>
    intro g hg
    rcases List.mem_cons.mp hg with rfl | hg
    · exact hc.trans (le_max_left _ _)
    · exact (ih g hg).trans (le_max_right _ _)

@[gen_rule] theorem sup_index_le {γ : Type v} {l : List γ} {hne : l ≠ []} {F : γ → ℕ∞}
    {cs : List ℕ∞} (h : List.Forall₂ (fun c g => F g ≤ c) cs l) :
    (Mix.sup.{u}).index l hne F ≤ cs.foldr max 0 :=
  iSup_le fun _ => le_foldr_max h _ (List.getElem_mem _)

@[gen_rule] theorem sup_element_le {γ : Type v} {l : List γ} {hne : l ≠ []} {F : γ → ℕ∞} {d : ℕ∞}
    (h : ∀ a ∈ l, F a ≤ d) : (Mix.sup.{u}).element l hne F ≤ d :=
  iSup_le fun _ => h _ (List.getElem_mem _)

private theorem selectD_le {l : List (Nat × ℕ∞)} {b : ℕ∞} (h : ∀ p ∈ l, p.2 ≤ b) (d : ℕ∞) :
    ∀ n, n < (l.map Prod.fst).sum → Obs.selectD l n d ≤ b := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    obtain ⟨k, x⟩ := hd
    intro n hn
    simp only [Obs.selectD]
    split
    · exact h (k, x) List.mem_cons_self
    · exact ih (fun p hp => h p (List.mem_cons_of_mem _ hp)) _
        (by simp only [List.map_cons, List.sum_cons] at hn; omega)

@[gen_rule] theorem sup_select_le {γ : Type v} {l : List (Nat × γ)}
    {hpos : 0 < (l.map Prod.fst).sum} {F : γ → ℕ∞} {d : ℕ∞} {cs : List (Nat × ℕ∞)}
    (h : Weighted (· ≤ ·) F cs l) :
    (Mix.sup.{u}).select l hpos F d ≤ (cs.map Prod.snd).foldr max 0 := by
  have key : ∀ q ∈ l, F q.2 ≤ (cs.map Prod.snd).foldr max 0 := by
    clear hpos
    induction h with
    | nil => simp
    | cons hc _ ih =>
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact hc.trans (le_max_left _ _)
      · exact (ih q hq).trans (le_max_right _ _)
  refine iSup_le fun a => selectD_le (fun p hp => ?_) d _ ?_
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    exact key q hq
  · have h1 := a.down.property.2
    have h2 : ((l.map fun p => (p.1, F p.2)).map Prod.fst).sum = (l.map Prod.fst).sum := by
      simp [Function.comp_def]
    omega

@[gen_rule] theorem sup_rangeInt_le {lo hi : ℤ} {h : lo ≤ hi} {F : ℤ → ℕ∞} {d : ℕ∞}
    (hF : ∀ x, lo ≤ x ∧ x ≤ hi → F x ≤ d) : (Mix.sup.{0}).rangeInt lo hi h F ≤ d := by
  refine iSup_le fun a => hF _ ⟨by omega, ?_⟩
  have := a.down.property
  omega

end Mix

namespace SPMF.Cost

/-! The list combinators of fixed or bounded length, bridged to the worst-case walk. -/

variable {α : Type} {g : SPMF.Cost α} {b k : ℕ∞} {p : List α → Nat → ℕ∞}

private theorem always_vectorOf {n k : Nat} (hg : alwaysObs.spec g fun _ m => m ≤ k) :
    alwaysObs.spec (vectorOf n g : SPMF.Cost (List α)) fun _ m => m ≤ n * k := by
  induction n with
  | zero =>
    show alwaysObs.spec (Pure.pure [] : SPMF.Cost (List α)) _
    walk
    omega
  | succ n ih =>
    rw [vectorOf_succ]
    -- The recursive occurrence is a combinator term, which the walk would bound by its rule.
    generalize (vectorOf n g : SPMF.Cost (List α)) = v at ih ⊢
    walk
    rw [Nat.succ_mul]
    omega

private theorem always_listOfMaxLength_const {n k : Nat} (hg : alwaysObs.spec g fun _ m => m ≤ k) :
    alwaysObs.spec (listOfMaxLength n g : SPMF.Cost (List α)) fun _ m => m ≤ 1 + n * k := by
  refine always_listOfMaxLength (Q := fun _ m => m ≤ 1 + n * k)
    fun j hj => le_always_of_always (always_vectorOf hg) fun a m hm => ?_
  have := Nat.mul_le_mul_right k hj
  show 1 + 0 + m ≤ 1 + n * k
  omega

@[gen_rule]
theorem worst_vectorOf_le {n : Nat} (hg : worstObs.spec g (fun _ m => (m : ℕ∞)) ≤ b)
    (hp : ∀ a m, p a m = k + (m : ℕ∞)) : worstObs.spec (vectorOf n g) p ≤ k + n * b := by
  induction b using ENat.recTopCoe with
  | top =>
    cases n with
    | zero =>
      refine (congrFun (worstObs.map_pure _) p).le.trans ?_
      show p [] 0 ≤ _
      rw [hp]
      simp
    | succ n => simp
  | coe K =>
    refine (worst_le_add_of_always (always_vectorOf (always_of_worst hg rfl)) hp).trans ?_
    push_cast
    exact le_rfl

@[gen_rule]
theorem worst_listOfMaxLength_le {n : Nat} (hg : worstObs.spec g (fun _ m => (m : ℕ∞)) ≤ b)
    (hp : ∀ a m, p a m = k + (m : ℕ∞)) :
    worstObs.spec (listOfMaxLength n g) p ≤ k + (1 + n * b) := by
  induction b using ENat.recTopCoe with
  | top =>
    cases n with
    | zero =>
      have h0 : alwaysObs.spec (listOfMaxLength 0 g : SPMF.Cost (List α)) fun _ m => m ≤ 1 := by
        refine always_listOfMaxLength (Q := fun _ m => m ≤ 1) fun j hj => ?_
        obtain rfl : j = 0 := by omega
        exact (iff_of_eq (congrFun (alwaysObs.map_pure _) _)).mpr (show 1 + 0 + 0 ≤ 1 by omega)
      exact (worst_le_add_of_always h0 hp).trans (by simp)
    | succ n => simp
  | coe K =>
    refine (worst_le_add_of_always
      (always_listOfMaxLength_const (always_of_worst hg rfl)) hp).trans ?_
    push_cast
    exact le_rfl

/-! `permutationOf` takes no generator: it draws one insertion index per element of its list. Its
body destructures each draw with a `match`, which the walk does not enter, so its bound is proved
by support inversion. -/

private theorem always_permutationOf {xs : List α} :
    alwaysObs.spec (permutationOf xs : SPMF.Cost { ys // xs.Perm ys }) fun _ n =>
      n ≤ xs.length := by
  induction xs with
  | nil =>
    rintro ⟨a, n⟩ h
    rw [permutationOf, mem_support_pure_iff] at h
    exact h.2.le
  | cons x xs ih =>
    rintro ⟨a, n⟩ h
    rw [permutationOf] at h
    obtain ⟨_, n1, n2, h1, h2, rfl⟩ := mem_support_bind_iff.mp h
    obtain ⟨⟨k, _, _⟩, n3, n4, h3, h4, rfl⟩ := mem_support_bind_iff.mp h2
    obtain ⟨_, h3, -⟩ := mem_support_map_iff.mp h3
    obtain ⟨-, rfl⟩ := mem_support_pure_iff.mp h4
    have : n1 ≤ xs.length := ih _ h1
    rw [mem_support_choose_iff.mp h3]
    show _ ≤ xs.length + 1
    omega

@[gen_rule]
theorem le_always_permutationOf {xs : List α} {p : { ys // xs.Perm ys } → Nat → Prop} :
    (∀ a n, n ≤ xs.length → p a n) ≤ alwaysObs.spec (permutationOf xs) p :=
  le_always_of_always always_permutationOf

@[gen_rule]
theorem worst_permutationOf_le {xs : List α} {p : { ys // xs.Perm ys } → Nat → ℕ∞}
    (hp : ∀ a m, p a m = k + (m : ℕ∞)) : worstObs.spec (permutationOf xs) p ≤ k + xs.length :=
  worst_le_add_of_always always_permutationOf hp

end SPMF.Cost
