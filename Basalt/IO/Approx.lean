/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt.GenRel
import Basalt.IO
import Basalt.Walk.Attr

/-!
# `IO` Runs `IOModel`

`IOModel.Approx m x` says that, if `ioGen` behaves as SplitMix specifies (`IOModel.IOGenLaws`), then
wherever `m` terminates the `IO` action `x` does what `m` does run against `ioGen`. A faithful
generator's `IsFaithful.approx` is this relation between it at `IOModel` and at `IO`, which
`walk fixpoint` proves.
-/

open Lean.Order

namespace WordModel

private abbrev word : WordModel SplitMix UInt64 := fun s => some (WordSource.next s)

private theorem drawDigitsVia_go_run (acc n : Nat) (g : SplitMix) :
    (drawDigitsVia.go word acc n).run g = some (SplitMix.drawDigits.go acc n g) := by
  induction n generalizing acc g with
  | zero => rfl
  | succ n ih => exact ih _ _

private theorem drawDigitsVia_run (mask : UInt64) (rest : Nat) (g : SplitMix) :
    (drawDigitsVia word mask rest).run g = some (SplitMix.drawDigits mask rest g) :=
  drawDigitsVia_go_run _ _ _

private theorem rejectVia_run (range : Nat) (mask : UInt64) (rest : Nat) :
    ∀ g p, (rejectVia (drawDigitsVia word mask rest) range).run g = some p →
      SplitMix.boundedLoop range mask rest g = p := by
  refine rejectVia.fixpoint_induct (m := WordModel SplitMix) _ range _
    (admissible_pi_apply (β := fun _ => Option ({x // x ≤ range} × SplitMix))
      (fun g o => ∀ p, o = some p → SplitMix.boundedLoop range mask rest g = p)
      fun g => admissible_flatOrder _ nofun) fun z ih g p hrun => ?_
  rw [SplitMix.boundedLoop]
  rcases hd : SplitMix.drawDigits mask rest g with ⟨x, g'⟩
  change StateT.run (drawDigitsVia word mask rest >>= fun x =>
    if h : x ≤ range then pure ⟨x, h⟩ else z) g = some p at hrun
  rw [StateT.run_bind, drawDigitsVia_run, hd] at hrun
  change (if h : x ≤ range then pure ⟨x, h⟩ else z).run g' = some p at hrun
  split at hrun
  · rename_i h
    simp only [h, dite_true]
    exact Option.some.inj hrun
  · rename_i h
    simp only [h, dite_false]
    exact ih _ _ hrun

/-- A draw on SplitMix's words that terminates is `SplitMix.randNatRef`'s. -/
theorem choose_run_splitMix {lo hi : Nat} (h : lo ≤ hi) (g : SplitMix) {a g'}
    (hrun : (RandomChoice.choose lo hi h : WordModel SplitMix _).run g = some (a, g')) :
    SplitMix.randNatRef g lo hi = (a.down.val, g') := by
  change (chooseVia word lo hi h).run g = _ at hrun
  unfold chooseVia at hrun
  unfold SplitMix.randNatRef SplitMix.boundedRef
  split at hrun
  · rename_i hlt
    rcases hs : SplitMix.rangeShape (hi - lo) with ⟨mask, rest⟩
    simp only [hs, StateT.run_map] at hrun
    rcases hp : StateT.run (rejectVia (drawDigitsVia word mask rest) (hi - lo)) g with _ | p
    · simp [hp] at hrun
    · simp only [hp] at hrun
      obtain ⟨rfl, rfl⟩ := hrun
      simp only [hlt, ite_true, rejectVia_run _ _ _ _ _ hp]
  · obtain rfl : lo = hi := by omega
    simp only [StateT.run_pure] at hrun
    obtain ⟨rfl, rfl⟩ := hrun
    simp

end WordModel

namespace IOModel

/-- `ioGen` read as a cell holding a SplitMix state: the laws of a state cell, and SplitMix's
specification of a draw. What they read `IO`'s world as is `ioGen`'s contents. That is a model, not
a hypothesis Lean could check: `IO.RealWorld` is opaque, as is the state `EST` threads, and every
operation on `ioGen` is opaque C, so Lean fixes no world and decides none of these equations;
`idealized_faithful` (`Basalt/IO/Faithful.lean`) takes them as a premise. The reading is exact for
what the premise is applied to: a generator's `IO` term reaches the world only through
`ioGen.randNat`, so projecting the world onto `ioGen`'s state loses nothing the term can observe.
It fails when another thread uses `ioGen` between two operations, and it is checked against the
compiled C by `BasaltTest/IO.lean`. -/
structure IOGenLaws : Prop where
  /-- Reading the state and writing it back does nothing: the C `get` copies the state out, and
  `set` copies it back in. -/
  get_set : ((ioGen.get : IO SplitMix) >>= fun s => (ioGen.set s : IO Unit)) = pure ()
  /-- A read after a write sees the write: `get` returns the fields `set` stored. SplitMix tests
  this. -/
  set_get : ∀ s : SplitMix,
    ((ioGen.set s : IO Unit) >>= fun _ => (ioGen.get : IO SplitMix))
      = ((ioGen.set s : IO Unit) >>= fun _ => pure s)
  /-- A second write replaces the first: `set` overwrites every field. -/
  set_set : ∀ s t : SplitMix,
    ((ioGen.set s : IO Unit) >>= fun _ => (ioGen.set t : IO Unit)) = ioGen.set t
  /-- A draw is `randNatRef` on the state, leaving the state `randNatRef` returns: SplitMix
  specifies the C this way, and tests the two against each other. Asked only where the model's draw
  terminates. Where it does not, no candidate is ever accepted, and the C loops forever on the same
  candidates, so the condition sets nothing aside. -/
  rand_nat : ∀ (lo hi : Nat) (h : lo ≤ hi) (s : SplitMix),
    (RandomChoice.choose lo hi h : IOModel _).run s ≠ none →
    ((ioGen.set s : IO Unit) >>= fun _ => Subtype.val <$> (ioGen.randNat lo hi : IO _))
      = ((ioGen.set (SplitMix.randNatRef s lo hi).2 : IO Unit) >>= fun _ =>
          pure (SplitMix.randNatRef s lo hi).1)

private theorem lift_bind_apply (a : BaseIO γ) (g : γ → IO β) (w) :
    ((a : IO γ) >>= g) w = match a w with | ⟨s, w'⟩ => g s w' := by
  show (match (BaseIO.toEIO a) w with | .ok s w' => g s w' | .error e w' => .error e w') = _
  unfold BaseIO.toEIO
  cases a w; rfl

private theorem io_bind_assoc (x : IO α) (f : α → IO β) (g : β → IO γ) :
    x >>= f >>= g = x >>= fun a => f a >>= g := by
  funext w
  show EST.bind (EST.bind x f) g w = EST.bind x (fun a => EST.bind (f a) g) w
  unfold EST.bind
  cases x w <;> rfl

private theorem IOGenLaws.get_set_bind (hc : IOGenLaws) (k : IO β) :
    ((ioGen.get : IO SplitMix) >>= fun s => (ioGen.set s : IO Unit) >>= fun _ => k) = k := by
  rw [← io_bind_assoc, hc.get_set]
  rfl

private theorem IOGenLaws.set_get_bind (hc : IOGenLaws) (s : SplitMix) (f : SplitMix → IO β) :
    ((ioGen.set s : IO Unit) >>= fun _ => (ioGen.get : IO SplitMix) >>= f)
      = ((ioGen.set s : IO Unit) >>= fun _ => f s) := by
  rw [← io_bind_assoc, hc.set_get, io_bind_assoc]
  rfl

private theorem IOGenLaws.set_set_bind (hc : IOGenLaws) (s t : SplitMix) (k : IO β) :
    ((ioGen.set s : IO Unit) >>= fun _ => (ioGen.set t : IO Unit) >>= fun _ => k)
      = ((ioGen.set t : IO Unit) >>= fun _ => k) := by
  rw [← io_bind_assoc, hc.set_set]

private theorem IOGenLaws.rand_nat_bind (hc : IOGenLaws) (lo hi : Nat) (h : lo ≤ hi)
    (s : SplitMix) (k : Nat → IO β) (hs : (RandomChoice.choose lo hi h : IOModel _).run s ≠ none) :
    ((ioGen.set s : IO Unit) >>= fun _ => (Subtype.val <$> (ioGen.randNat lo hi : IO _)) >>= k)
      = ((ioGen.set (SplitMix.randNatRef s lo hi).2 : IO Unit) >>= fun _ =>
          k (SplitMix.randNatRef s lo hi).1) := by
  rw [← io_bind_assoc, hc.rand_nat lo hi h s hs, io_bind_assoc]
  rfl

private theorem bot_rel (x : IO α) : (EST.bot : IO α) ⊑ x := fun _ => FlatOrder.rel.bot

private theorem set_bot (s : SplitMix) :
    ((ioGen.set s : IO Unit) >>= fun _ => (EST.bot : IO α)) = EST.bot := by
  funext w
  show (match (BaseIO.toEIO (ioGen.set s)) w with
    | .ok a w' => (fun _ => (EST.bot : IO α)) a w' | .error e w' => .error e w') = _
  unfold BaseIO.toEIO
  cases ioGen.set s w
  rfl

private theorem finish_bind_some (a : α) (s' : SplitMix) (g : α → IO β) :
    finish (some (a, s')) >>= g = (ioGen.set s' : IO Unit) >>= fun _ => g a := by
  rw [finish, io_bind_assoc]
  rfl

theorem toIO_pure (hc : IOGenLaws) (a : α) : (pure a : IOModel α).toIO = pure a := by
  exact hc.get_set_bind (pure a)

theorem toIO_bind (hc : IOGenLaws) (m : IOModel α) (k : α → IOModel β) :
    (m >>= k).toIO = m.toIO >>= fun a => (k a).toIO := by
  simp only [toIO]
  rw [io_bind_assoc]
  congr 1
  funext s
  rw [StateT.run_bind]
  rcases m.run s with _ | ⟨a, s'⟩
  · rfl
  · rw [finish_bind_some, hc.set_get_bind]
    show finish ((k a).run s') = _
    rcases (k a).run s' with _ | ⟨b, s''⟩
    · exact (set_bot s').symm
    · exact (hc.set_set_bind s' s'' (pure b)).symm

/-- `x` runs `m` wherever `m` terminates, if `ioGen` is lawful: `m.toIO ⊑ x` in `IO`'s order, which
is flat at each world, with divergence at the bottom. -/
@[walk_rel]
def Approx (m : IOModel α) (x : IO α) : Prop := IOGenLaws → m.toIO ⊑ x

/-- Fixpoint induction on the `IOModel` side needs nothing of `ioGen`: `toIO` is continuous. -/
theorem Approx.admissible (x : IO α) : admissible fun m : IOModel α => Approx m x := by
  have key : ∀ m : IOModel α, m.toIO ⊑ x ↔ ∀ s, (fun s (o : Option (α × SplitMix)) =>
      ∀ w w', ioGen.get w = ⟨s, w'⟩ → @FlatOrder.rel _ (EST.bot w) (finish o w') (x w))
        s (m s) := by
    intro m
    constructor
    · intro h s w w' hg
      have := h w
      rw [toIO, lift_bind_apply, hg] at this
      exact this
    · intro h w
      show @FlatOrder.rel _ (EST.bot w) (m.toIO w) (x w)
      rw [toIO, lift_bind_apply]
      rcases hg : ioGen.get w with ⟨s, w'⟩
      exact h s w w' hg
  have hadm : Lean.Order.admissible fun m : IOModel α => m.toIO ⊑ x := by
    rw [show (fun m : IOModel α => m.toIO ⊑ x) = fun m => ∀ s, _ from
      funext fun m => propext (key m)]
    exact admissible_pi_apply (β := fun _ => Option (α × SplitMix)) _ fun s =>
      admissible_flatOrder (b := (none : Option (α × SplitMix))) (fun o => ∀ w w',
        ioGen.get w = ⟨s, w'⟩ → @FlatOrder.rel _ (EST.bot w) (finish o w') (x w))
        fun _ _ _ => FlatOrder.rel.bot
  intro c hchain ih hc
  exact hadm c hchain fun m hm => ih m hm hc

@[gen_rule]
theorem approx_pure (a : α) : Approx (pure a) (pure a) := fun hc => by
  rw [toIO_pure hc]
  exact PartialOrder.rel_refl

@[gen_rule]
theorem approx_bind {m : IOModel α} {x : IO α} {k : α → IOModel β} {f : α → IO β}
    (hk : ∀ a, Approx (k a) (f a)) (hm : Approx m x) : Approx (m >>= k) (x >>= f) := fun hc => by
  rw [toIO_bind hc]
  exact PartialOrder.rel_trans (MonoBind.bind_mono_right fun a => hk a hc)
    (MonoBind.bind_mono_left (hm hc))

@[gen_rule]
theorem approx_map {m : IOModel α} {x : IO α} (f : α → β) (hm : Approx m x) :
    Approx (f <$> m) (f <$> x) := by
  rw [← bind_pure_comp, show (f <$> x : IO β) = x >>= fun a => pure (f a) from rfl]
  exact approx_bind (fun a => approx_pure (f a)) hm

@[gen_rule]
theorem approx_ite {p : Prop} [Decidable p] {m₁ m₂ : IOModel α} {x₁ x₂ : IO α}
    (h₁ : p → Approx m₁ x₁) (h₂ : ¬p → Approx m₂ x₂) :
    Approx (if p then m₁ else m₂) (if p then x₁ else x₂) :=
  GenRel.ite h₁ h₂

@[gen_rule]
theorem approx_dite {p : Prop} [Decidable p] {m₁ : p → IOModel α} {m₂ : ¬p → IOModel α}
    {x₁ : p → IO α} {x₂ : ¬p → IO α}
    (h₁ : ∀ h, Approx (m₁ h) (x₁ h)) (h₂ : ∀ h, Approx (m₂ h) (x₂ h)) :
    Approx (if h : p then m₁ h else m₂ h) (if h : p then x₁ h else x₂ h) :=
  GenRel.dite h₁ h₂

@[gen_rule]
theorem approx_default (x : IO α) : Approx default x := fun _ w => by
  rw [toIO, lift_bind_apply]
  cases ioGen.get w
  exact FlatOrder.rel.bot

/-- `IO`'s `choose` is `randNat`'s value, clamped to the range it is already in. -/
private theorem choose_io (lo hi : Nat) (h : lo ≤ hi) :
    (RandomChoice.choose lo hi h : IO _) = (Subtype.val <$> (ioGen.randNat lo hi : IO _)) >>=
      fun x => pure (if hx : lo ≤ x ∧ x ≤ hi then ULift.up ⟨x, hx⟩
        else ULift.up ⟨lo, Nat.le_refl lo, h⟩) := by
  rw [show (Subtype.val <$> (ioGen.randNat lo hi : IO _)) = (ioGen.randNat lo hi : IO _) >>=
    fun p => pure p.val from rfl, io_bind_assoc]
  show (do let ⟨x, hx⟩ ← (ioGen.randNat lo hi : IO _)
           pure (ULift.up (⟨x, (by omega : lo ≤ x ∧ x ≤ hi)⟩ : {x // lo ≤ x ∧ x ≤ hi}))) = _
  refine congrArg (_ >>= ·) (funext fun ⟨x, hx⟩ => ?_)
  have : lo ≤ x ∧ x ≤ hi := by omega
  show pure _ = pure _
  rw [dite_eq_left this]

/-- The step Lean does not see: a draw at `IO` is SplitMix's draw at `IOModel`. -/
@[gen_rule]
theorem approx_choose (lo hi : Nat) (h : lo ≤ hi) :
    Approx (RandomChoice.choose lo hi h) (RandomChoice.choose lo hi h) := fun hc => by
  rw [choose_io, toIO, ← hc.get_set_bind ((Subtype.val <$> (ioGen.randNat lo hi : IO _)) >>= _)]
  refine MonoBind.bind_mono_right fun s => ?_
  rcases hrun : (RandomChoice.choose lo hi h : IOModel _).run s with _ | ⟨a, s'⟩
  · exact bot_rel _
  · rw [hc.rand_nat_bind lo hi h s _ (by simp [hrun]), WordModel.choose_run_splitMix h s hrun]
    have ha : (if hx : lo ≤ a.down.val ∧ a.down.val ≤ hi then ULift.up ⟨a.down.val, hx⟩
        else ULift.up ⟨lo, Nat.le_refl lo, h⟩) = a := by
      rw [dite_eq_left a.down.property]
    show finish (some (a, s')) ⊑ ((ioGen.set s' : IO Unit) >>= fun _ =>
      pure (if hx : lo ≤ a.down.val ∧ a.down.val ≤ hi then ULift.up ⟨a.down.val, hx⟩
        else ULift.up ⟨lo, Nat.le_refl lo, h⟩))
    rw [ha]
    exact PartialOrder.rel_refl

end IOModel
