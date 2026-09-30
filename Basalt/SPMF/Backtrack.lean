/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Segev Elazar Mittelman
-/
import Basalt.BacktrackGen
import Basalt.SPMF.Support

/-!
# Support of Backtracking Generators

What `BacktrackGen.backtrack` can produce at `SPMF`, in terms of what its branches can: its successes
are its positive-weight branches' successes, it refutes exactly when every branch can, and it cannot
fail if one positive-weight branch cannot.
-/

open RandomChoice

namespace BacktrackGen

variable {α : Type}

/-! ## `pickDrop` -/

section pickDrop

@[simp] theorem sumWeights_nil {β : Type} : sumWeights ([] : List (Nat × β)) = 0 := rfl

@[simp] theorem sumWeights_cons {β : Type} (p : Nat × β) (rest : List (Nat × β)) :
    sumWeights (p :: rest) = p.1 + sumWeights rest := by
  simp [sumWeights]

variable {β : Type} [Inhabited β]

theorem pickDrop_cons_lt (k : Nat) (g : β) (rest : List (Nat × β)) {n : Nat} (hk : n < k) :
    pickDrop ((k, g) :: rest) n = (k, g, rest) := by
  simp [pickDrop, hk]

theorem pickDrop_cons_ge (k : Nat) (g : β) (rest : List (Nat × β)) {n : Nat} (hk : ¬ n < k) :
    pickDrop ((k, g) :: rest) n
      = ((pickDrop rest (n - k)).1, (pickDrop rest (n - k)).2.1,
         (k, g) :: (pickDrop rest (n - k)).2.2) := by
  simp [pickDrop, hk]

/-- The selected entry is a member, or `default` when `n` overshoots the total weight. -/
theorem pickDrop_mem_or_default : ∀ (gs : List (Nat × β)) (n : Nat),
    ((pickDrop gs n).1, (pickDrop gs n).2.1) ∈ gs ∨ (pickDrop gs n).2.1 = default
  | [], _ => Or.inr rfl
  | (k, g) :: rest, n => by
    by_cases hk : n < k
    · exact Or.inl (by simp [pickDrop, hk])
    · rcases pickDrop_mem_or_default rest (n - k) with h | h
      · exact Or.inl (by rw [pickDrop_cons_ge k g rest hk]; exact List.mem_cons_of_mem _ h)
      · exact Or.inr (by rw [pickDrop_cons_ge k g rest hk]; exact h)

/-- Every positive-weight entry is selected by some offset inside the total weight. -/
theorem exists_pickDrop_eq : ∀ (gs : List (Nat × β)) (p : Nat × β), p ∈ gs → 0 < p.1 →
    ∃ n, n < sumWeights gs ∧ (pickDrop gs n).1 = p.1 ∧ (pickDrop gs n).2.1 = p.2
  | [], _, hp, _ => by simp at hp
  | (k, g) :: rest, p, hp, hk => by
    rcases List.mem_cons.mp hp with rfl | hrest
    · exact ⟨0, by simp only [sumWeights_cons]; omega, by simp [pickDrop, hk],
        by simp [pickDrop, hk]⟩
    · obtain ⟨n, hn, h1, h2⟩ := exists_pickDrop_eq rest p hrest hk
      have hge : ¬ k + n < k := by omega
      refine ⟨k + n, by simp only [sumWeights_cons]; omega, ?_, ?_⟩ <;>
        rw [pickDrop_cons_ge k g rest hge, Nat.add_sub_cancel_left] <;> assumption

theorem mem_pickDrop_cases : ∀ (gs : List (Nat × β)) (n : Nat) (p : Nat × β), p ∈ gs →
    p = ((pickDrop gs n).1, (pickDrop gs n).2.1) ∨ p ∈ (pickDrop gs n).2.2
  | [], _, _, hp => by simp at hp
  | (k, g) :: rest, n, p, hp => by
    by_cases hk : n < k
    · rw [pickDrop_cons_lt k g rest hk]
      rcases List.mem_cons.mp hp with rfl | hrest
      · exact Or.inl rfl
      · exact Or.inr hrest
    · rw [pickDrop_cons_ge k g rest hk]
      rcases List.mem_cons.mp hp with rfl | hrest
      · exact Or.inr (List.mem_cons_self ..)
      · rcases mem_pickDrop_cases rest (n - k) p hrest with h | h
        · exact Or.inl h
        · exact Or.inr (List.mem_cons_of_mem _ h)

theorem pickDrop_rest_subset : ∀ (gs : List (Nat × β)) (n : Nat) (p : Nat × β),
    p ∈ (pickDrop gs n).2.2 → p ∈ gs
  | [], _, _, hp => by simp [pickDrop] at hp
  | (k, g) :: rest, n, p, hp => by
    by_cases hk : n < k
    · rw [pickDrop_cons_lt k g rest hk] at hp
      exact List.mem_cons_of_mem _ hp
    · rw [pickDrop_cons_ge k g rest hk, List.mem_cons] at hp
      rcases hp with rfl | h
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (pickDrop_rest_subset rest (n - k) p h)

omit [Inhabited β] in
theorem le_sumWeights_of_mem : ∀ (gs : List (Nat × β)) (p : Nat × β), p ∈ gs → p.1 ≤ sumWeights gs
  | [], _, hp => by simp at hp
  | (k, g) :: rest, p, hp => by
    rcases List.mem_cons.mp hp with rfl | hrest
    · simp only [sumWeights_cons]; omega
    · have := le_sumWeights_of_mem rest p hrest
      simp only [sumWeights_cons]; omega

theorem pickDrop_length : ∀ (gs : List (Nat × β)) (n : Nat), n < sumWeights gs →
    (pickDrop gs n).2.2.length + 1 = gs.length
  | [], n, h => by simp at h
  | (k, g) :: rest, n, h => by
    by_cases hk : n < k
    · rw [pickDrop_cons_lt k g rest hk]; simp only [List.length_cons]
    · have ih := pickDrop_length rest (n - k) (by simp only [sumWeights_cons] at h; omega)
      rw [pickDrop_cons_ge k g rest hk]
      simp only [List.length_cons]
      omega

theorem pickDrop_sumWeights : ∀ (gs : List (Nat × β)) (n : Nat), n < sumWeights gs →
    sumWeights (pickDrop gs n).2.2 + (pickDrop gs n).1 = sumWeights gs
  | [], n, h => by simp at h
  | (k, g) :: rest, n, h => by
    by_cases hk : n < k
    · rw [pickDrop_cons_lt k g rest hk]; simp only [sumWeights_cons]; omega
    · have ih := pickDrop_sumWeights rest (n - k) (by simp only [sumWeights_cons] at h; omega)
      rw [pickDrop_cons_ge k g rest hk]
      simp only [sumWeights_cons]
      omega

end pickDrop

/-! ## Successes -/

/-- The out-of-range `default` branch never succeeds. -/
theorem not_mem_support_default_run {a : α} :
    Outcome.ok a ∉ ((default : Unit → BacktrackGen SPMF α) ()).run.support := by
  change Outcome.ok a ∉ (Pure.pure Outcome.exhausted : SPMF _).support
  simp

theorem mem_support_go_ok : ∀ (fuel total : Nat) (gs : List (Nat × (Unit → BacktrackGen SPMF α)))
    (flag : Bool) (a : α), Outcome.ok a ∈ (backtrack.go fuel total gs flag).support →
      ∃ p ∈ gs, Outcome.ok a ∈ (p.2 ()).run.support
  | _, _, [], flag, a, h => by cases flag <;> simp [backtrack.go] at h
  | 0, _, _ :: _, _, a, h => by simp [backtrack.go] at h
  | fuel + 1, total, p :: rest, flag, a, h => by
    simp only [backtrack.go, SPMF.mem_support_bind_iff] at h
    obtain ⟨n, _, o, ho, hres⟩ := h
    cases o with
    | ok a' =>
      obtain rfl : a = a' := by simpa using hres
      rcases pickDrop_mem_or_default (p :: rest) n.down.val with hmem | hdef
      · exact ⟨_, hmem, ho⟩
      · exact absurd (hdef ▸ ho) not_mem_support_default_run
    | refuted =>
      obtain ⟨q, hq, hqa⟩ := mem_support_go_ok fuel _ _ _ a hres
      exact ⟨q, pickDrop_rest_subset _ _ _ hq, hqa⟩
    | exhausted =>
      obtain ⟨q, hq, hqa⟩ := mem_support_go_ok fuel _ _ _ a hres
      exact ⟨q, pickDrop_rest_subset _ _ _ hq, hqa⟩

/-- **Soundness.** A success of `backtrack` is a success of one of its branches. -/
theorem mem_support_backtrack_ok (gs : List (Nat × (Unit → BacktrackGen SPMF α))) (a : α)
    (h : Outcome.ok a ∈ (backtrack gs).run.support) : ∃ p ∈ gs, Outcome.ok a ∈ (p.2 ()).run.support :=
  mem_support_go_ok gs.length (sumWeights gs) gs false a h

/-- **Completeness**, for positive-weight branches: a zero-weight branch is never drawn. -/
theorem mem_support_backtrack_of_branch (gs : List (Nat × (Unit → BacktrackGen SPMF α)))
    (p : Nat × (Unit → BacktrackGen SPMF α)) (hp : p ∈ gs) (hk : 0 < p.1) (a : α)
    (h : Outcome.ok a ∈ (p.2 ()).run.support) : Outcome.ok a ∈ (backtrack gs).run.support := by
  obtain ⟨n, hn, _, hsel⟩ := exists_pickDrop_eq gs p hp hk
  cases gs with
  | nil => simp at hp
  | cons q rest =>
    show Outcome.ok a ∈ (backtrack.go (q :: rest).length (sumWeights (q :: rest)) (q :: rest) false).support
    simp only [List.length_cons, backtrack.go, SPMF.mem_support_bind_iff]
    exact ⟨ULift.up ⟨n, Nat.zero_le _, by omega⟩, by simp, Outcome.ok a, hsel ▸ h, by simp⟩

theorem mem_support_backtrack_ok_iff (gs : List (Nat × (Unit → BacktrackGen SPMF α))) (a : α)
    (hpos : ∀ p ∈ gs, 0 < p.1) :
    Outcome.ok a ∈ (backtrack gs).run.support ↔ ∃ p ∈ gs, Outcome.ok a ∈ (p.2 ()).run.support :=
  ⟨mem_support_backtrack_ok gs a, fun ⟨p, hp, h⟩ => mem_support_backtrack_of_branch gs p hp (hpos p hp) a h⟩

/-! ## Refutations -/

theorem mem_support_go_refuted : ∀ (fuel total : Nat) (gs : List (Nat × (Unit → BacktrackGen SPMF α)))
    (flag : Bool), Outcome.refuted ∈ (backtrack.go fuel total gs flag).support →
      flag = false ∧ ∀ p ∈ gs, Outcome.refuted ∈ (p.2 ()).run.support
  | _, _, [], flag, h => by cases flag <;> simp [backtrack.go] at h ⊢
  | 0, _, _ :: _, _, h => by simp [backtrack.go] at h
  | fuel + 1, total, q :: rest, flag, h => by
    simp only [backtrack.go, SPMF.mem_support_bind_iff] at h
    obtain ⟨n, _, o, ho, hres⟩ := h
    cases o with
    | ok a => simp at hres
    | refuted =>
      obtain ⟨hflag, hall⟩ := mem_support_go_refuted fuel _ _ _ hres
      refine ⟨hflag, fun p hp => ?_⟩
      rcases mem_pickDrop_cases (q :: rest) n.down.val p hp with rfl | hrest
      · exact ho
      · exact hall p hrest
    | exhausted => exact absurd (mem_support_go_refuted fuel _ _ _ hres).1 (by simp)

/-- A refutation from `backtrack` means every branch can refute. -/
theorem mem_support_backtrack_refuted (gs : List (Nat × (Unit → BacktrackGen SPMF α)))
    (h : Outcome.refuted ∈ (backtrack gs).run.support) :
    ∀ p ∈ gs, Outcome.refuted ∈ (p.2 ()).run.support :=
  (mem_support_go_refuted gs.length (sumWeights gs) gs false h).2

theorem go_refuted_of_all : ∀ (fuel total : Nat) (gs : List (Nat × (Unit → BacktrackGen SPMF α))),
    gs.length ≤ fuel → total = sumWeights gs → (∀ p ∈ gs, 0 < p.1) →
    (∀ p ∈ gs, Outcome.refuted ∈ (p.2 ()).run.support) →
    Outcome.refuted ∈ (backtrack.go fuel total gs false).support
  | _, _, [], _, _, _, _ => by simp [backtrack.go]
  | 0, _, _ :: _, hlen, _, _, _ => by simp at hlen
  | fuel + 1, total, q :: rest, hlen, hsum, hpos, hall => by
    have hq : 0 < q.1 := hpos q (List.mem_cons_self ..)
    have htot : 0 < total := by rw [hsum]; simp only [sumWeights_cons]; omega
    have hpick : pickDrop (q :: rest) 0 = (q.1, q.2, rest) := pickDrop_cons_lt q.1 q.2 rest hq
    simp only [backtrack.go, SPMF.mem_support_bind_iff]
    refine ⟨ULift.up ⟨0, Nat.zero_le _, Nat.zero_le _⟩, by simp, ?_⟩
    simp only [hpick]
    refine ⟨Outcome.refuted, hall q (List.mem_cons_self ..), ?_⟩
    refine go_refuted_of_all fuel (total - q.1) rest (by simp at hlen; omega) ?_
      (fun p hp => hpos p (List.mem_cons_of_mem _ hp)) (fun p hp => hall p (List.mem_cons_of_mem _ hp))
    rw [hsum]; simp only [sumWeights_cons]; omega

/-- Conversely, if every branch has positive weight and can refute, so can `backtrack`. -/
theorem mem_support_backtrack_refuted_of_all (gs : List (Nat × (Unit → BacktrackGen SPMF α)))
    (hpos : ∀ p ∈ gs, 0 < p.1) (hall : ∀ p ∈ gs, Outcome.refuted ∈ (p.2 ()).run.support) :
    Outcome.refuted ∈ (backtrack gs).run.support :=
  go_refuted_of_all gs.length (sumWeights gs) gs (Nat.le_refl _) rfl hpos hall

@[simp] theorem mem_support_refutedToExhausted_ok_iff {k : ProducerKind} (g : Producer k SPMF α) (a : α) :
    Outcome.ok a ∈ (Producer.refutedToExhausted g).run.support ↔ Outcome.ok a ∈ g.run.support := by
  simp only [Producer.refutedToExhausted, SPMF.mem_support_bind_iff]
  constructor
  · rintro ⟨o, ho, hres⟩
    cases o <;> simp_all
  · exact fun h => ⟨_, h, by simp⟩

/-- `refutedToExhausted` makes `refuted` unreachable. -/
theorem not_mem_support_refutedToExhausted {k : ProducerKind} (g : Producer k SPMF α) :
    Outcome.refuted ∉ (Producer.refutedToExhausted g).run.support := by
  simp only [Producer.refutedToExhausted, SPMF.mem_support_bind_iff, not_exists, not_and]
  intro o _
  cases o <;> simp

/-! ## Cannot fail -/

/-- Every outcome `g` can produce is a success. -/
def NeverFails (g : BacktrackGen SPMF α) : Prop :=
  ∀ o ∈ g.run.support, ∃ a, o = Outcome.ok a

theorem go_neverFails (p : Nat × (Unit → BacktrackGen SPMF α)) (hp0 : 0 < p.1)
    (hnf : NeverFails (p.2 ())) : ∀ (fuel total : Nat) (gs : List (Nat × (Unit → BacktrackGen SPMF α)))
    (flag : Bool), p ∈ gs → gs.length ≤ fuel → total = sumWeights gs →
      ∀ o ∈ (backtrack.go fuel total gs flag).support, ∃ a, o = Outcome.ok a
  | _, _, [], _, hmem, _, _ => by simp at hmem
  | 0, _, _ :: _, _, _, hlen, _ => by simp at hlen
  | fuel + 1, total, q :: rest, flag, hmem, hlen, hsum => by
    intro o ho
    simp only [backtrack.go, SPMF.mem_support_bind_iff] at ho
    obtain ⟨n, _, ores, hores, hres⟩ := ho
    have hpos : 0 < sumWeights (q :: rest) := Nat.lt_of_lt_of_le hp0 (le_sumWeights_of_mem _ p hmem)
    have hlt : n.down.val < sumWeights (q :: rest) := by
      have := n.down.property.2
      omega
    have hlenr : (pickDrop (q :: rest) n.down.val).2.2.length ≤ fuel := by
      have := pickDrop_length (q :: rest) n.down.val hlt
      simp only [List.length_cons] at this hlen; omega
    have hsumr : total - (pickDrop (q :: rest) n.down.val).1
        = sumWeights (pickDrop (q :: rest) n.down.val).2.2 := by
      have := pickDrop_sumWeights (q :: rest) n.down.val hlt; omega
    -- If the drawn branch was `p` it could not have failed, so after a failure `p` is still in the pool.
    have hp_rest (hfail : ∀ a, ores ≠ Outcome.ok a) : p ∈ (pickDrop (q :: rest) n.down.val).2.2 := by
      rcases mem_pickDrop_cases (q :: rest) n.down.val p hmem with heq | hr
      · obtain ⟨a, ha⟩ := hnf ores (by rw [show p.2 = _ from congrArg Prod.snd heq]; exact hores)
        exact absurd ha (hfail a)
      · exact hr
    cases ores with
    | ok a' => exact ⟨a', by simpa using hres⟩
    | refuted =>
      exact go_neverFails p hp0 hnf fuel _ _ flag (hp_rest (by simp)) hlenr hsumr o hres
    | exhausted =>
      exact go_neverFails p hp0 hnf fuel _ _ true (hp_rest (by simp)) hlenr hsumr o hres

/-- If one positive-weight branch cannot fail, neither can `backtrack`: a failed draw is dropped and
retried, and the fuel is the number of branches, so the pool cannot run out before that branch. -/
theorem neverFails_backtrack (gs : List (Nat × (Unit → BacktrackGen SPMF α)))
    (p : Nat × (Unit → BacktrackGen SPMF α)) (hp : p ∈ gs) (hp0 : 0 < p.1)
    (hnf : NeverFails (p.2 ())) : NeverFails (backtrack gs) :=
  fun o ho => go_neverFails p hp0 hnf gs.length (sumWeights gs) gs false hp (Nat.le_refl _) rfl o ho

theorem neverFails_pure (a : α) : NeverFails (pure a : BacktrackGen SPMF α) := by
  intro o ho
  change o ∈ (Pure.pure (Outcome.ok a) : SPMF _).support at ho
  exact ⟨a, SPMF.mem_support_pure_iff.mp ho⟩

theorem neverFails_liftGen (g : SPMF α) : NeverFails (liftGen g) := by
  intro o ho
  simp only [liftGen, Producer.lift, SPMF.mem_support_bind_iff, SPMF.mem_support_pure_iff] at ho
  obtain ⟨a, _, rfl⟩ := ho
  exact ⟨a, rfl⟩

theorem neverFails_bind {β : Type} {g : BacktrackGen SPMF α} {f : α → BacktrackGen SPMF β}
    (hg : NeverFails g) (hf : ∀ a, Outcome.ok a ∈ g.run.support → NeverFails (f a)) :
    NeverFails (g >>= f) := by
  intro o ho
  have hrun : (g >>= f).run = g.run >>= fun o => match o with
      | .ok a => (f a).run
      | .refuted => pure .refuted
      | .exhausted => pure .exhausted := rfl
  rw [hrun, SPMF.mem_support_bind_iff] at ho
  obtain ⟨oa, hoa, hb⟩ := ho
  obtain ⟨a, rfl⟩ := hg oa hoa
  exact hf a hoa o hb

theorem neverFails_refutedToExhausted {g : BacktrackGen SPMF α} (hg : NeverFails g) :
    NeverFails (refutedToExhausted g) := by
  intro o ho
  simp only [refutedToExhausted, Producer.refutedToExhausted, SPMF.mem_support_bind_iff] at ho
  obtain ⟨oa, hoa, hb⟩ := ho
  obtain ⟨a, rfl⟩ := hg oa hoa
  exact ⟨a, by simpa using hb⟩

end BacktrackGen
