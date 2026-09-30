/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Segev Elazar Mittelman
-/
import Basalt.Graded

/-!
# The Interpretations of a Graded Enumeration Agree

`Agrees m s` says the values `m` enumerates at each level are exactly the specification `s`'s — soundness
and completeness at once, at the exact level, since levels are disjoint — and `Counts m c` that `c` counts
them. Every operation preserves both, so they lift to a closed recursion.
-/

namespace Basalt

universe u

variable {α β : Type}

/-! ## Unfolding the two interpretations -/

@[simp] theorem Lv.nothing_apply (n : Nat) :
    (Choice.nothing : Lv α) n = [] := rfl
@[simp] theorem Lv.union_apply (x y : Lv α) (n : Nat) :
    (Choice.union x y : Lv α) n = x n ++ y n := rfl
@[simp] theorem Lv.single_apply (a : α) (n : Nat) :
    (Graded.single a : Lv α) n = if n = 0 then [a] else [] := rfl
@[simp] theorem Lv.pay_zero (x : Lv α) :
    (Graded.pay x : Lv α) 0 = [] := rfl
@[simp] theorem Lv.pay_succ (x : Lv α) (n : Nat) :
    (Graded.pay x : Lv α) (n + 1) = x n := rfl
@[simp] theorem Lv.pair_apply (x : Lv α) (y : Lv β) (n : Nat) :
    (Graded.pair x y : Lv (α × β)) n
      = (List.range (n + 1)).flatMap fun i => (x i).flatMap fun a => (y (n - i)).map (a, ·) := rfl
@[simp] theorem Lv.gmap_apply (g : α → β) (x : Lv α) (n : Nat) :
    (Graded.gmap g x : Lv β) n = (x n).map g := rfl
@[simp] theorem Lv.bind_apply (x : Lv α) (k : α → Lv β) (n : Nat) :
    (GradedBind.bind x k : Lv β) n = (x n).flatMap fun a => k a n := rfl
@[simp] theorem Lv.bindC_apply (x : Lv α) (k : α → Lv β) (n : Nat) :
    (GradedBind.bindC x k : Lv β) n
      = (List.range (n + 1)).flatMap fun i => (x i).flatMap fun a => k a (n - i) := rfl
@[simp] theorem Lv.guard_apply (p : α → V) (x : Lv α) (n : Nat) :
    (GradedBind.guard p x : Lv (α × Bool)) n
      = (x n).filterMap fun a =>
          match p a with
          | .yes => some (a, true)
          | .inconclusive => some (a, false)
          | .no => none := rfl

@[simp] theorem SetE.nothing_apply (n : Nat) (a : α) :
    (Choice.nothing : SetE α) n a ↔ False := Iff.rfl
@[simp] theorem SetE.union_apply (x y : SetE α) (n : Nat) (a : α) :
    (Choice.union x y : SetE α) n a ↔ x n a ∨ y n a := Iff.rfl
@[simp] theorem SetE.single_apply (a b : α) (n : Nat) :
    (Graded.single a : SetE α) n b ↔ n = 0 ∧ b = a := Iff.rfl
@[simp] theorem SetE.pay_zero (x : SetE α) (a : α) :
    (Graded.pay x : SetE α) 0 a ↔ False := Iff.rfl
@[simp] theorem SetE.pay_succ (x : SetE α) (n : Nat) (a : α) :
    (Graded.pay x : SetE α) (n + 1) a ↔ x n a := Iff.rfl
@[simp] theorem SetE.pair_apply (x : SetE α) (y : SetE β) (n : Nat) (p : α × β) :
    (Graded.pair x y : SetE (α × β)) n p ↔ ∃ i ≤ n, x i p.1 ∧ y (n - i) p.2 := Iff.rfl
@[simp] theorem SetE.gmap_apply (g : α → β) (x : SetE α) (n : Nat) (b : β) :
    (Graded.gmap g x : SetE β) n b ↔ ∃ a, x n a ∧ g a = b := Iff.rfl
@[simp] theorem SetE.bind_apply (x : SetE α) (k : α → SetE β) (n : Nat) (b : β) :
    (GradedBind.bind x k : SetE β) n b ↔ ∃ a, x n a ∧ k a n b := Iff.rfl
@[simp] theorem SetE.bindC_apply (x : SetE α) (k : α → SetE β) (n : Nat) (b : β) :
    (GradedBind.bindC x k : SetE β) n b ↔ ∃ i ≤ n, ∃ a, x i a ∧ k a (n - i) b := Iff.rfl
@[simp] theorem SetE.guard_apply (p : α → V) (x : SetE α) (n : Nat) (q : α × Bool) :
    (GradedBind.guard p x : SetE (α × Bool)) n q
      ↔ x n q.1 ∧ (match p q.1 with
        | .yes => q.2 = true
        | .inconclusive => q.2 = false
        | .no => False) := Iff.rfl

/-! ## Agreement -/

/-- The value enumeration and the specification describe the same levels: left to right soundness,
right to left completeness. -/
def Agrees (m : Lv α) (s : SetE α) : Prop := ∀ n a, a ∈ m n ↔ s n a

theorem agrees_nothing : Agrees (Choice.nothing : Lv α) (Choice.nothing : SetE α) := by
  intro n a; simp

theorem Agrees.union {x y : Lv α} {s t : SetE α}
    (hx : Agrees x s) (hy : Agrees y t) :
    Agrees (Choice.union x y) (Choice.union s t) := by
  intro n a; simp [hx n a, hy n a]

theorem agrees_single (a : α) : Agrees (Graded.single a) (Graded.single a) := by
  intro n b
  by_cases h : n = 0 <;> simp [h]

theorem Agrees.pay {x : Lv α} {s : SetE α} (hx : Agrees x s) :
    Agrees (Graded.pay x) (Graded.pay s) := by
  intro n a
  cases n with
  | zero => simp
  | succ n => simpa using hx n a

theorem Agrees.gmap {x : Lv α} {s : SetE α} (g : α → β) (hx : Agrees x s) :
    Agrees (Graded.gmap g x) (Graded.gmap g s) := by
  intro n b
  simp only [Lv.gmap_apply, SetE.gmap_apply, List.mem_map]
  constructor
  · rintro ⟨a, ha, rfl⟩; exact ⟨a, (hx n a).mp ha, rfl⟩
  · rintro ⟨a, ha, rfl⟩; exact ⟨a, (hx n a).mpr ha, rfl⟩

/-- Convolution: `range (n + 1)` in `Lv` is exactly `i ≤ n` in `SetE`. -/
theorem Agrees.pair {x : Lv α} {s : SetE α} {y : Lv β} {t : SetE β}
    (hx : Agrees x s) (hy : Agrees y t) :
    Agrees (Graded.pair x y) (Graded.pair s t) := by
  intro n p
  simp only [Lv.pair_apply, SetE.pair_apply, List.mem_flatMap, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi, a, ha, b, hb, rfl⟩
    exact ⟨i, Nat.lt_succ_iff.mp hi, (hx i a).mp ha, (hy (n - i) b).mp hb⟩
  · rintro ⟨i, hi, h1, h2⟩
    exact ⟨i, Nat.lt_succ_iff.mpr hi, p.1, (hx i p.1).mpr h1, p.2, (hy (n - i) p.2).mpr h2, rfl⟩

theorem Agrees.bind {x : Lv α} {s : SetE α} {k : α → Lv β} {h : α → SetE β}
    (hx : Agrees x s) (hk : ∀ a, Agrees (k a) (h a)) :
    Agrees (GradedBind.bind x k) (GradedBind.bind s h) := by
  intro n b
  simp only [Lv.bind_apply, SetE.bind_apply, List.mem_flatMap]
  constructor
  · rintro ⟨a, ha, hb⟩; exact ⟨a, (hx n a).mp ha, (hk a n b).mp hb⟩
  · rintro ⟨a, ha, hb⟩; exact ⟨a, (hx n a).mpr ha, (hk a n b).mpr hb⟩

/-- The convolving bind, for an auxiliary output that carries its own size. Same `i ≤ n` / `range (n+1)`
reconciliation as `Agrees.pair`, with a value-dependent continuation instead of an independent operand. -/
theorem Agrees.bindC {x : Lv α} {s : SetE α} {k : α → Lv β} {h : α → SetE β}
    (hx : Agrees x s) (hk : ∀ a, Agrees (k a) (h a)) :
    Agrees (GradedBind.bindC x k) (GradedBind.bindC s h) := by
  intro n b
  simp only [Lv.bindC_apply, SetE.bindC_apply, List.mem_flatMap, List.mem_range]
  constructor
  · rintro ⟨i, hi, a, ha, hb⟩
    exact ⟨i, Nat.lt_succ_iff.mp hi, a, (hx i a).mp ha, (hk a (n - i) b).mp hb⟩
  · rintro ⟨i, hi, a, ha, hb⟩
    exact ⟨i, Nat.lt_succ_iff.mpr hi, a, (hx i a).mpr ha, (hk a (n - i) b).mpr hb⟩

/-- A checked premise. The `inconclusive` element is *kept*, flagged `false` — the point being that the
spec side says the same thing, so `Agrees` cannot be satisfied by a version that silently drops it. -/
theorem Agrees.guard {x : Lv α} {s : SetE α} (p : α → V) (hx : Agrees x s) :
    Agrees (GradedBind.guard p x) (GradedBind.guard p s) := by
  intro n q
  simp only [Lv.guard_apply, SetE.guard_apply, List.mem_filterMap]
  constructor
  · rintro ⟨a, ha, heq⟩
    cases hp : p a with
    | yes =>
      rw [hp] at heq
      simp only [Option.some.injEq] at heq
      subst heq
      exact ⟨(hx n a).mp ha, by simp [hp]⟩
    | no => rw [hp] at heq; simp at heq
    | inconclusive =>
      rw [hp] at heq
      simp only [Option.some.injEq] at heq
      subst heq
      exact ⟨(hx n a).mp ha, by simp [hp]⟩
  · rintro ⟨hs, hv⟩
    refine ⟨q.1, (hx n q.1).mpr hs, ?_⟩
    -- `cases hp :` substitutes the scrutinee in the goal but not in `hv`, hence `rw ... at hv`; and the
    -- resulting `match` on a literal constructor is only *defeq* to its branch, hence `replace`/`show`.
    cases hp : p q.1 with
    | yes =>
      rw [hp] at hv
      replace hv : q.2 = true := hv
      show some (q.1, true) = some q
      rw [← hv]
    | no =>
      rw [hp] at hv
      exact (show False from hv).elim
    | inconclusive =>
      rw [hp] at hv
      replace hv : q.2 = false := hv
      show some (q.1, false) = some q
      rw [← hv]

/-- A side condition decided on the inputs, such as a rule whose conclusion fixes an index. -/
theorem Agrees.ite {c : Prop} [Decidable c] {x y : Lv α} {s t : SetE α}
    (hx : Agrees x s) (hy : Agrees y t) :
    Agrees (if c then x else y) (if c then s else t) := by
  by_cases h : c
  · simpa only [ite_eq_left h] using hx
  · simpa only [ite_eq_right h] using hy

/-- One level of agreement lifts to the closed recursion, for any number of levels. -/
theorem agrees_gradedIter {stepL : Lv α → Lv α} {stepS : SetE α → SetE α}
    (h : ∀ x s, Agrees x s → Agrees (stepL x) (stepS s)) :
    ∀ n, Agrees (gradedIter stepL n) (gradedIter stepS n)
  | 0 => agrees_nothing
  | n + 1 => h _ _ (agrees_gradedIter h n)

/-! ## The graded leaves -/

theorem agrees_natStep (x : Lv Nat) (s : SetE Nat) (hx : Agrees x s) :
    Agrees (natStep x) (natStep s) :=
  (agrees_single 0).union ((hx.gmap (· + 1)).pay)

theorem agrees_boolStep (x : Lv Bool) (s : SetE Bool) (_hx : Agrees x s) :
    Agrees (boolStep x) (boolStep s) :=
  (agrees_single false).union (agrees_single true)

theorem agrees_listStep {e : Lv α} {es : SetE α} (he : Agrees e es)
    (x : Lv (List α)) (s : SetE (List α)) (hx : Agrees x s) :
    Agrees (listStep e x) (listStep es s) :=
  (agrees_single []).union (((he.pair hx).gmap fun p => p.1 :: p.2).pay)

/-- `Nat` graded by magnitude is sound and complete against its specification. -/
theorem agrees_nat (n : Nat) : Agrees (gradedIter natStep n) (gradedIter natStep n) :=
  agrees_gradedIter agrees_natStep n

theorem agrees_bool (n : Nat) : Agrees (gradedIter boolStep n) (gradedIter boolStep n) :=
  agrees_gradedIter agrees_boolStep n

theorem agrees_list {e : Lv α} {es : SetE α} (he : Agrees e es) (n : Nat) :
    Agrees (gradedIter (listStep e) n) (gradedIter (listStep es) n) :=
  agrees_gradedIter (agrees_listStep he) n

/-! ## Containment at the specification carrier

For combining results found at different iteration counts, as a completeness proof by induction on a
derivation does when its premises bring different budgets. -/

/-- Pointwise containment of two specifications. -/
def SubE (x y : SetE α) : Prop := ∀ n a, x n a → y n a

theorem SubE.refl (x : SetE α) : SubE x x := fun _ _ h => h

theorem SubE.trans {x y z : SetE α} (h₁ : SubE x y) (h₂ : SubE y z) : SubE x z :=
  fun n a h => h₂ n a (h₁ n a h)

theorem subE_nothing (y : SetE α) : SubE (Choice.nothing) y := by
  intro n a h; exact absurd h (by simp)

theorem SubE.union {x y s t : SetE α} (hx : SubE x s) (hy : SubE y t) :
    SubE (Choice.union x y) (Choice.union s t) := by
  intro n a h
  simp only [SetE.union_apply] at h ⊢
  exact h.imp (hx n a) (hy n a)

theorem SubE.pay {x s : SetE α} (hx : SubE x s) : SubE (Graded.pay x) (Graded.pay s) := by
  intro n a h
  cases n with
  | zero => exact absurd h (by simp)
  | succ n => simpa using hx n a (by simpa using h)

theorem SubE.gmap {x s : SetE α} (g : α → β) (hx : SubE x s) :
    SubE (Graded.gmap g x) (Graded.gmap g s) := by
  intro n b h
  simp only [SetE.gmap_apply] at h ⊢
  obtain ⟨a, ha, rfl⟩ := h
  exact ⟨a, hx n a ha, rfl⟩

theorem SubE.pair {x s : SetE α} {y t : SetE β} (hx : SubE x s) (hy : SubE y t) :
    SubE (Graded.pair x y) (Graded.pair s t) := by
  intro n p h
  simp only [SetE.pair_apply] at h ⊢
  obtain ⟨i, hi, h1, h2⟩ := h
  exact ⟨i, hi, hx i p.1 h1, hy (n - i) p.2 h2⟩

theorem SubE.bindC {x s : SetE α} {k h : α → SetE β}
    (hx : SubE x s) (hk : ∀ a, SubE (k a) (h a)) :
    SubE (GradedBind.bindC x k) (GradedBind.bindC s h) := by
  intro n b hb
  simp only [SetE.bindC_apply] at hb ⊢
  obtain ⟨i, hi, a, ha, hkb⟩ := hb
  exact ⟨i, hi, a, hx i a ha, hk a (n - i) b hkb⟩

theorem SubE.ite {c : Prop} [Decidable c] {x y s t : SetE α}
    (hx : SubE x s) (hy : SubE y t) :
    SubE (if c then x else y) (if c then s else t) := by
  by_cases h : c
  · simpa only [ite_eq_left h] using hx
  · simpa only [ite_eq_right h] using hy

/-! ## Indexed families

An enumeration per index, for a dependent relation; agreement lifts pointwise. -/

/-- Pointwise agreement of two indexed families. -/
def AgreesIx {ι : Type} (m : ι → Lv α) (s : ι → SetE α) : Prop := ∀ i, Agrees (m i) (s i)

/-- The unindexed iteration is monotone in its level count too — needed to raise a *leaf* enumeration's
budget, as opposed to the recursion's. -/
theorem subE_gradedIter_succ {step : SetE α → SetE α}
    (hmono : ∀ x y, SubE x y → SubE (step x) (step y)) :
    ∀ n, SubE (gradedIter step n) (gradedIter step (n + 1))
  | 0 => subE_nothing _
  | n + 1 => hmono _ _ (subE_gradedIter_succ hmono n)

theorem subE_gradedIter_le {step : SetE α → SetE α}
    (hmono : ∀ x y, SubE x y → SubE (step x) (step y)) :
    ∀ {m n}, m ≤ n → SubE (gradedIter step m) (gradedIter step n) := by
  intro m n hmn
  induction n with
  | zero => have : m = 0 := Nat.le_zero.mp hmn; subst this; exact SubE.refl _
  | succ n ih =>
    rcases Nat.lt_or_ge m (n + 1) with h | h
    · exact SubE.trans (ih (Nat.lt_succ_iff.mp h)) (subE_gradedIter_succ hmono n)
    · have : m = n + 1 := Nat.le_antisymm hmn h
      subst this; exact SubE.refl _

/-- Pointwise containment of two indexed families. -/
def SubIxE {ι : Type} (x y : ι → SetE α) : Prop := ∀ i, SubE (x i) (y i)

/-- A monotone step makes the indexed iteration monotone in its iteration count. This is what lets a
completeness proof raise one premise's budget to match another's. -/
theorem subIxE_gradedIterIx_succ {ι : Type} {step : (ι → SetE α) → ι → SetE α}
    (hmono : ∀ x y, SubIxE x y → SubIxE (step x) (step y)) :
    ∀ n, SubIxE (gradedIterIx step n) (gradedIterIx step (n + 1))
  | 0 => fun _ => subE_nothing _
  | n + 1 => hmono _ _ (subIxE_gradedIterIx_succ hmono n)

theorem subIxE_gradedIterIx_le {ι : Type} {step : (ι → SetE α) → ι → SetE α}
    (hmono : ∀ x y, SubIxE x y → SubIxE (step x) (step y)) :
    ∀ {m n}, m ≤ n → SubIxE (gradedIterIx step m) (gradedIterIx step n) := by
  intro m n hmn
  induction n with
  | zero =>
    have : m = 0 := Nat.le_zero.mp hmn
    subst this; exact fun i => SubE.refl _
  | succ n ih =>
    rcases Nat.lt_or_ge m (n + 1) with h | h
    · exact fun i => SubE.trans (ih (Nat.lt_succ_iff.mp h) i)
        (subIxE_gradedIterIx_succ hmono n i)
    · have : m = n + 1 := Nat.le_antisymm hmn h
      subst this; exact fun i => SubE.refl _

theorem agrees_gradedIterIx {ι : Type} {stepL : (ι → Lv α) → ι → Lv α}
    {stepS : (ι → SetE α) → ι → SetE α}
    (h : ∀ x s, AgreesIx x s → AgreesIx (stepL x) (stepS s)) :
    ∀ n, AgreesIx (gradedIterIx stepL n) (gradedIterIx stepS n)
  | 0 => fun _ => agrees_nothing
  | n + 1 => h _ _ (agrees_gradedIterIx h n)

/-! ## Cardinality

Only the `Graded` operations: there is no `GradedBind Cnt`, so an enumeration with a checked premise has
no exact count. -/

@[simp] theorem Cnt.nothing_apply (n : Nat) :
    (Choice.nothing : Cnt α) n = 0 := rfl
@[simp] theorem Cnt.union_apply (x y : Cnt α) (n : Nat) :
    (Choice.union x y : Cnt α) n = x n + y n := rfl
@[simp] theorem Cnt.single_apply (a : α) (n : Nat) :
    (Graded.single a : Cnt α) n = if n = 0 then 1 else 0 := rfl
@[simp] theorem Cnt.pay_zero (x : Cnt α) :
    (Graded.pay x : Cnt α) 0 = 0 := rfl
@[simp] theorem Cnt.pay_succ (x : Cnt α) (n : Nat) :
    (Graded.pay x : Cnt α) (n + 1) = x n := rfl
@[simp] theorem Cnt.pair_apply (x : Cnt α) (y : Cnt β) (n : Nat) :
    (Graded.pair x y : Cnt (α × β)) n = ((List.range (n + 1)).map fun i => x i * y (n - i)).sum := rfl
@[simp] theorem Cnt.gmap_apply (g : α → β) (x : Cnt α) (n : Nat) :
    (Graded.gmap g x : Cnt β) n = x n := rfl

/-- `Cnt` counts what `Lv` produces, level by level. -/
def Counts (m : Lv α) (c : Cnt α) : Prop := ∀ n, (m n).length = c n

private theorem sum_map_const (l : List α) (k : Nat) :
    (l.map fun _ => k).sum = l.length * k := by
  induction l with
  | nil => simp
  | cons _ t ih => simp [ih, Nat.succ_mul, Nat.add_comm]

theorem counts_nothing : Counts (Choice.nothing : Lv α) (Choice.nothing : Cnt α) := by
  intro n; simp

theorem Counts.union {x y : Lv α} {cx cy : Cnt α}
    (hx : Counts x cx) (hy : Counts y cy) :
    Counts (Choice.union x y) (Choice.union cx cy) := by
  intro n; simp [List.length_append, hx n, hy n]

theorem counts_single (a : α) : Counts (Graded.single a) (Graded.single a) := by
  intro n; by_cases h : n = 0 <;> simp [h]

theorem Counts.pay {x : Lv α} {cx : Cnt α} (hx : Counts x cx) :
    Counts (Graded.pay x) (Graded.pay cx) := by
  intro n
  cases n with
  | zero => simp
  | succ n => simpa using hx n

theorem Counts.gmap {x : Lv α} {cx : Cnt α} (g : α → β) (hx : Counts x cx) :
    Counts (Graded.gmap g x) (Graded.gmap g cx) := by
  intro n; simpa [List.length_map] using hx n

/-- Convolution counts correctly: the nested `flatMap` has exactly `Σ_{i≤n} |xᵢ| · |y_{n-i}|` elements.
This is the step that would break silently if `pair` ever dropped or duplicated a split. -/
theorem Counts.pair {x : Lv α} {cx : Cnt α} {y : Lv β} {cy : Cnt β}
    (hx : Counts x cx) (hy : Counts y cy) :
    Counts (Graded.pair x y) (Graded.pair cx cy) := by
  intro n
  simp only [Lv.pair_apply, Cnt.pair_apply, List.length_flatMap]
  refine congrArg List.sum (List.map_congr_left ?_)
  intro i _
  simp only [List.length_map]
  rw [sum_map_const, hx i, hy (n - i)]

theorem Counts.ite {c : Prop} [Decidable c] {x y : Lv α} {cx cy : Cnt α}
    (hx : Counts x cx) (hy : Counts y cy) :
    Counts (if c then x else y) (if c then cx else cy) := by
  by_cases h : c
  · simpa only [ite_eq_left h] using hx
  · simpa only [ite_eq_right h] using hy

theorem counts_gradedIter {stepL : Lv α → Lv α} {stepC : Cnt α → Cnt α}
    (h : ∀ x c, Counts x c → Counts (stepL x) (stepC c)) :
    ∀ n, Counts (gradedIter stepL n) (gradedIter stepC n)
  | 0 => counts_nothing
  | n + 1 => h _ _ (counts_gradedIter h n)

theorem counts_natStep (x : Lv Nat) (c : Cnt Nat) (hx : Counts x c) :
    Counts (natStep x) (natStep c) :=
  (counts_single 0).union ((hx.gmap (· + 1)).pay)

theorem counts_boolStep (x : Lv Bool) (c : Cnt Bool) (_hx : Counts x c) :
    Counts (boolStep x) (boolStep c) :=
  (counts_single false).union (counts_single true)

theorem counts_listStep {e : Lv α} {ce : Cnt α} (he : Counts e ce)
    (x : Lv (List α)) (c : Cnt (List α)) (hx : Counts x c) :
    Counts (listStep e x) (listStep ce c) :=
  (counts_single []).union (((he.pair hx).gmap fun p => p.1 :: p.2).pay)

/-- Every level of the magnitude-graded `Nat` really is a singleton — the finiteness invariant the whole
level discipline rests on, now as a theorem rather than an evaluated example. -/
theorem counts_nat (n : Nat) : Counts (gradedIter natStep n) (gradedIter natStep n) :=
  counts_gradedIter counts_natStep n

theorem counts_bool (n : Nat) : Counts (gradedIter boolStep n) (gradedIter boolStep n) :=
  counts_gradedIter counts_boolStep n

theorem counts_list {e : Lv α} {ce : Cnt α} (he : Counts e ce) (n : Nat) :
    Counts (gradedIter (listStep e) n) (gradedIter (listStep ce) n) :=
  counts_gradedIter (counts_listStep he) n

/-- Pointwise counting for an indexed family. -/
def CountsIx {ι : Type} (m : ι → Lv α) (c : ι → Cnt α) : Prop := ∀ i, Counts (m i) (c i)

theorem counts_gradedIterIx {ι : Type} {stepL : (ι → Lv α) → ι → Lv α}
    {stepC : (ι → Cnt α) → ι → Cnt α}
    (h : ∀ x c, CountsIx x c → CountsIx (stepL x) (stepC c)) :
    ∀ n, CountsIx (gradedIterIx stepL n) (gradedIterIx stepC n)
  | 0 => fun _ => counts_nothing
  | n + 1 => h _ _ (counts_gradedIterIx h n)

end Basalt
