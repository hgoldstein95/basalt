/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
module

public import Basalt.Enum.Memo

/-!
# Memoizing Changes Nothing but the Work

`KeyedStep.memoPure` runs a recursion at `MemoM`, `Finite` with a table threaded through it, and
`KeyedStep.fix` runs it at `Finite`. They agree, key for key (`KeyedStep.memoPure_eq`), for every
step that relates itself between the two.

`MemoM.Rel V m y` says `m`, run from any table satisfying `V`, returns `y` and leaves a table
satisfying `V`. Every construct preserves it, for every `V` (`rel_pure`, `rel_bind`, …), so a step
written from them relates itself; `V` is then taken to be "every entry is `fix`'s value at its key",
which `memoFix` preserves because it only ever records `fix`'s value.
-/

@[expose] public section

namespace Basalt

namespace MemoM

variable {κ α β γ : Type} [BEq κ] [Hashable κ]

/-- Run from any table satisfying `V`, `m` returns `y` and leaves a table satisfying `V`. -/
def Rel (V : Std.HashMap κ (Finite α) → Prop) (m : MemoM κ α β) (y : Finite β) : Prop :=
  ∀ c, V c → (m c).1 = y ∧ V (m c).2

variable {V : Std.HashMap κ (Finite α) → Prop}

theorem rel_pure (b : β) : Rel V (Pure.pure b : MemoM κ α β) (Pure.pure b) := fun _ hc => ⟨rfl, hc⟩

theorem rel_fail : Rel V (Fail.fail : MemoM κ α β) (Fail.fail : Finite β) := fun _ hc => ⟨rfl, hc⟩

theorem rel_choose (lo hi : Nat) (h : lo ≤ hi) :
    Rel V (RandomChoice.choose lo hi h : MemoM κ α _) (RandomChoice.choose lo hi h) :=
  fun _ hc => ⟨rfl, hc⟩

theorem rel_map {m : MemoM κ α β} {y : Finite β} (g : β → γ) (h : Rel V m y) :
    Rel V (g <$> m) (g <$> y) := fun c hc => by
  obtain ⟨h₁, h₂⟩ := h c hc
  exact ⟨by show (m c).1.map g = _; rw [h₁]; rfl, h₂⟩

theorem rel_seq {mf : MemoM κ α (β → γ)} {yf : Finite (β → γ)} {m : MemoM κ α β} {y : Finite β}
    (hf : Rel V mf yf) (h : Rel V m y) : Rel V (mf <*> m) (yf <*> y) := fun c hc => by
  obtain ⟨hf₁, hf₂⟩ := hf c hc
  obtain ⟨h₁, h₂⟩ := h _ hf₂
  exact ⟨by show Finite.seq (mf c).1 (m (mf c).2).1 = _; rw [hf₁, h₁]; rfl, h₂⟩

theorem rel_dite {p : Prop} [Decidable p] {m₁ : p → MemoM κ α β} {m₂ : ¬p → MemoM κ α β}
    {y₁ : p → Finite β} {y₂ : ¬p → Finite β} (h₁ : ∀ h, Rel V (m₁ h) (y₁ h))
    (h₂ : ∀ h, Rel V (m₂ h) (y₂ h)) :
    Rel V (if h : p then m₁ h else m₂ h) (if h : p then y₁ h else y₂ h) := by
  split
  · exact h₁ _
  · exact h₂ _

theorem rel_ite {p : Prop} [Decidable p] {m₁ m₂ : MemoM κ α β} {y₁ y₂ : Finite β}
    (h₁ : p → Rel V m₁ y₁) (h₂ : ¬p → Rel V m₂ y₂) :
    Rel V (if p then m₁ else m₂) (if p then y₁ else y₂) := by
  split
  · exact h₁ ‹_›
  · exact h₂ ‹_›

/-- The fold `bind` runs over `x`'s entries returns their continuations' results, in order, and keeps
`V`. -/
theorem parts_rel {n : Nat} (f : β → MemoM κ α γ) (idx : Fin n → β) (g : β → Finite γ)
    (hf : ∀ b, Rel V (f b) (g b)) (c : Std.HashMap κ (Finite α)) (hc : V c) :
    (parts f idx c).1.reverse = List.ofFn (fun i => g (idx i)) ∧ V (parts f idx c).2 := by
  induction n with
  | zero => exact ⟨rfl, hc⟩
  | succ n ih =>
    unfold parts at ih ⊢
    rw [Fin.foldl_succ_last]
    obtain ⟨ih₁, ih₂⟩ := ih (fun i => idx i.castSucc)
    generalize Fin.foldl n _ ([], c) = r at ih₁ ih₂ ⊢
    obtain ⟨acc, c'⟩ := r
    obtain ⟨hy₁, hy₂⟩ := hf (idx (Fin.last n)) c' ih₂
    dsimp only
    generalize f (idx (Fin.last n)) c' = q at hy₁ hy₂ ⊢
    obtain ⟨y, c''⟩ := q
    refine ⟨?_, hy₂⟩
    show (y :: acc).reverse = _
    simp only at hy₁ ih₁
    rw [List.reverse_cons, ih₁, hy₁, List.ofFn_succ_last]

theorem rel_bind {m : MemoM κ α β} {y : Finite β} {f : β → MemoM κ α γ} {g : β → Finite γ}
    (hf : ∀ b, Rel V (f b) (g b)) (h : Rel V m y) : Rel V (m >>= f) (y >>= g) := fun c hc => by
  obtain ⟨h₁, h₂⟩ := h c hc
  show (MemoM.bind m f c).1 = Finite.bind y g ∧ V (MemoM.bind m f c).2
  unfold MemoM.bind
  generalize hmc : m c = r at h₁ h₂
  obtain ⟨z, c'⟩ := r
  simp only at h₁ h₂
  subst h₁
  cases z with
  | undef => exact ⟨rfl, h₂⟩
  | mk n idx =>
    obtain ⟨p₁, p₂⟩ := parts_rel f idx g hf c' h₂
    dsimp only
    generalize parts f idx c' = r at p₁ p₂ ⊢
    obtain ⟨ps, c''⟩ := r
    exact ⟨by show Finite.flatten ps.reverse = _; rw [p₁]; rfl, p₂⟩

theorem rel_pickFrom (l : List β) : Rel V (pickFrom l : MemoM κ α β) (pickFrom l : Finite β) := by
  cases l with
  | nil => exact rel_fail
  | cons x xs => exact rel_bind (fun _ => rel_pure _) (rel_choose _ _ _)

end MemoM

namespace KeyedStep

variable {κ : Type} {rank : κ → Nat} {α : Type} [BEq κ] [Hashable κ]

/-- Every entry of the table is `fix`'s value at its key. -/
def Valid (stepF : KeyedStep κ rank Finite α) (c : Std.HashMap κ (Finite α)) : Prop :=
  ∀ k v, c[k]? = some v → v = fix stepF k

/-- `memoFix` is `fix`, keeping the table valid, for a step that relates itself between the two. -/
theorem memoFix_rel [LawfulBEq κ] [LawfulHashable κ]
    (stepM : KeyedStep κ rank (MemoM κ α) α) (stepF : KeyedStep κ rank Finite α)
    (hstep : ∀ (V : Std.HashMap κ (Finite α) → Prop) k
      (recM : (k' : κ) → rank k' < rank k → MemoM κ α α) (recF : (k' : κ) → rank k' < rank k → Finite α),
      (∀ k' hk, MemoM.Rel V (recM k' hk) (recF k' hk)) → MemoM.Rel V (stepM k recM) (stepF k recF))
    (k : κ) : MemoM.Rel (Valid stepF) (memoFix stepM k) (fix stepF k) := by
  suffices ∀ n k, rank k = n → MemoM.Rel (Valid stepF) (memoFix stepM k) (fix stepF k) from
    this _ k rfl
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro k hk c hc
    rw [memoFix]
    cases hck : c[k]? with
    | some v => exact ⟨hc k v hck, hc⟩
    | none =>
      have hs := hstep (Valid stepF) k (fun k' _ => memoFix stepM k') (fun k' _ => fix stepF k')
        (fun k' hlt => ih _ (hk ▸ hlt) k' rfl) c hc
      generalize hr : stepM k (fun k' _ => memoFix stepM k') c = r at hs
      obtain ⟨v, c'⟩ := r
      obtain ⟨hv, hc'⟩ := hs
      have hfix : v = fix stepF k := by rw [fix]; exact hv
      refine ⟨hfix, fun k'' v'' h'' => ?_⟩
      rw [Std.HashMap.getElem?_insert] at h''
      split at h''
      · rename_i heq
        cases h''
        rw [← (beq_iff_eq.mp heq)]
        exact hfix
      · exact hc' k'' v'' h''

/-- Memoizing changes nothing: `memoPure` is `fix` at every key. -/
theorem memoPure_eq [LawfulBEq κ] [LawfulHashable κ]
    (stepM : KeyedStep κ rank (MemoM κ α) α) (stepF : KeyedStep κ rank Finite α)
    (hstep : ∀ (V : Std.HashMap κ (Finite α) → Prop) k
      (recM : (k' : κ) → rank k' < rank k → MemoM κ α α) (recF : (k' : κ) → rank k' < rank k → Finite α),
      (∀ k' hk, MemoM.Rel V (recM k' hk) (recF k' hk)) → MemoM.Rel V (stepM k recM) (stepF k recF))
    (ks : List κ) : memoPure stepM ks = ks.map (fix stepF) := by
  have key : ∀ (ks : List κ) (vs : List (Finite α)) c, Valid stepF c →
      (ks.foldl (fun (vs, c) k => let (v, c) := memoFix stepM k c; (v :: vs, c)) (vs, c)).1.reverse =
        vs.reverse ++ ks.map (fix stepF) := by
    intro ks
    induction ks with
    | nil => intro vs c _; simp
    | cons k ks ih =>
      intro vs c hc
      obtain ⟨h₁, h₂⟩ := memoFix_rel stepM stepF hstep k c hc
      simp only [List.foldl_cons]
      generalize hr : memoFix stepM k c = r at h₁ h₂
      obtain ⟨v, c'⟩ := r
      simp only at h₁ h₂ ⊢
      rw [ih _ _ h₂, h₁]
      simp
  have := key ks [] {} fun k v h => by simp at h
  simpa [memoPure] using this

end KeyedStep

end Basalt
