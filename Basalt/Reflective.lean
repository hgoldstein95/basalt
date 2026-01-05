import Basalt.Gen

open Lean.Order RandomChoice

/-!
# Reflective Generators

_Reflective generators_ (Goldstein and Frohlich et al., 2023) were originally conceptualized as a
fundamentally different kind of generator than the standard generator presentation. Users annotate
generators with partial inverse functions that undo specific steps of the computation, and then the
generator can automatically be re-interpreted as a mapping from values to sequences of choices.

Here, we take a different approach. Generators are not changed at all; instead, the inverse
annotations are provided as part of a simple deductive synthesis process (similar to the one
Palamedes uses).
-/

/-- A generator can be interpreted as a parser of randomness. -/
def ParserGen (α : Type) := StateT (List Nat) Option α

instance : Inhabited (ParserGen α) where
  default := fun _ => none

instance : Monad ParserGen := inferInstanceAs (Monad (StateT (List Nat) Option))

instance : RandomChoice ParserGen where
  choose lo hi _ := fun
    | [] => none
    | c :: cs => if lo ≤ c ∧ c ≤ hi then some (c, cs) else none

instance : CCPO (ParserGen α) := inferInstanceAs (CCPO (StateT (List Nat) Option α))

instance : MonoBind ParserGen := inferInstanceAs (MonoBind (StateT (List Nat) Option))

/-- We can interpret a `Gen` as a parser of sequences of natural number choices. -/
def parse (g : Gen α) : List Nat → Option α := (g : ParserGen α).run'

/-- A parser is "well-behaved" if it consumes a prefix of the input string. -/
def WellBehaved (g : ParserGen α) : Prop :=
  ∀ input output a, g.run input = some (a, output) → ∃ consumed, input = consumed ++ output

theorem pure_WellBehaved : WellBehaved (pure a) := by
  intros input output a' h
  simp [StateT.run, pure, StateT.pure] at h
  obtain ⟨rfl, rfl⟩ := h
  exists []

theorem bind_WellBehaved
    (hx : WellBehaved x)
    (hf : ∀ a, WellBehaved (f a)) :
    WellBehaved (x >>= f) := by
  intros input output b h
  simp [StateT.run, bind, StateT.bind, Option.bind] at h
  split at h
  · cases h
  case _ ox of p heq =>
    obtain ⟨a, middle⟩ := p
    have ⟨consumed1, h1⟩ := hx input middle a heq
    have ⟨consumed2, h2⟩ := hf a middle output b h
    exists consumed1 ++ consumed2
    rw [h1, h2, List.append_assoc]

theorem choose_WellBehaved : WellBehaved (choose lo hi h) := by
  intros input output a' heq
  simp [StateT.run, choose] at heq
  cases input with
  | nil => cases heq
  | cons c cs =>
    by_cases hc : lo ≤ c ∧ c ≤ hi
    · simp [hc] at heq
      obtain ⟨rfl, rfl⟩ := heq
      exists [c]
    · simp [hc] at heq

def Reflector (α : Type) := α → List (List Nat)

/-- A reflector `r` reflects a generator `g` if `g` is well-behaved and `g` produces a value given
  some choices iff `r` can reflect on that value to get the choices back. -/
def Reflects (g : ParserGen α) (r : Reflector α) : Prop :=
  WellBehaved g ∧
  ∀ (a : α) (cs₁ cs₂ : List Nat), g.run (cs₁ ++ cs₂) = some (a, cs₂) ↔ cs₁ ∈ r a

theorem pure_reflects [BEq α] [LawfulBEq α] {a : α} :
    Reflects (pure a) (fun a' => if a == a' then [[]] else []) := by
  constructor
  . exact pure_WellBehaved
  . intros a' cs₁ cs₂
    simp [StateT.run, pure, StateT.pure]

theorem bind_reflects {x : ParserGen α} {f : α → ParserGen β} {rf : α → Reflector β}
    (inv : β → Option α)
    (hinv : ∀ a b cs cs' cs'',
      x.run cs = some (a, cs') →
      (f a).run cs' = some (b, cs'') →
      inv b = some a)
    (hx : Reflects x rx)
    (hf : ∀ a, Reflects (f a) (rf a)) :
    Reflects (x >>= f) (fun b =>
      (inv b).toList |>.flatMap fun a =>
      rx a |>.flatMap fun cs₁ =>
      rf a b |>.flatMap fun cs₂ =>
      [cs₁ ++ cs₂]) := by
  constructor
  . exact bind_WellBehaved hx.1 (fun a => (hf a).1)
  . intros b cs₁ cs₂
    simp [StateT.run, bind, StateT.bind, Option.bind]
    split
    case _ ox of heq =>
      constructor
      · intro h; cases h
      · intro ⟨a, hleft_inv, left, hleft, right, hright, hcs_eq⟩
        subst hcs_eq
        have : x (left ++ (right ++ cs₂)) = some (a, right ++ cs₂) :=
          (hx.2 a left (right ++ cs₂)).mpr hleft
        simp_all
    case _ ox of p heq =>
      have ⟨a, cs'⟩ := p
      simp
      constructor
      · intro h
        have hinv_eq : inv b = some a := hinv a b (cs₁ ++ cs₂) cs' cs₂ heq h
        have ⟨right, hright_eq⟩ : ∃ right, cs' = right ++ cs₂ := by
          by_cases h_eq : ∃ right, cs' = right ++ cs₂
          · exact h_eq
          · exfalso
            apply h_eq
            exact (hf a).1 cs' cs₂ b h
        subst hright_eq
        have hright_mem : right ∈ rf a b := ((hf a).2 b right cs₂).mp h
        have ⟨left, hleft_eq⟩ : ∃ left, cs₁ = left ++ right := by
          have ⟨consumed, h_decomp⟩ := hx.1 (cs₁ ++ cs₂) (right ++ cs₂) a heq
          exists consumed
          have : cs₁ ++ cs₂ = consumed ++ right ++ cs₂ := by
            rw [List.append_assoc]; exact h_decomp
          exact List.append_cancel_right this
        subst hleft_eq
        have hleft_mem : left ∈ rx a := by
          have : x (left ++ (right ++ cs₂)) = some (a, right ++ cs₂) := by grind
          exact (hx.2 a left (right ++ cs₂)).mp this
        simp [hinv_eq]
        exists left, hleft_mem, right, hright_mem
      · intro ⟨a', hleft_inv, left, hleft_mem, right, hright_mem, hcs_eq⟩
        subst hcs_eq
        have ha : x (left ++ (right ++ cs₂)) = some (a', right ++ cs₂) :=
          (hx.2 a' left (right ++ cs₂)).mpr hleft_mem
        rw [← List.append_assoc] at ha
        have : some (a, cs') = some (a', right ++ cs₂) := Eq.trans heq.symm ha
        simp at this
        have ⟨h_a, h_cs⟩ := this
        subst h_cs
        rw [h_a]
        exact ((hf a').2 b right cs₂).mpr hright_mem

theorem choose_reflects :
    Reflects (choose lo hi h) (fun a => if lo ≤ a ∧ a ≤ hi then [[a]] else []) := by
  constructor
  . exact choose_WellBehaved
  . intros a' cs₁ cs₂
    simp [StateT.run, choose, StateT.run]
    cases cs₁
    . split <;> simp_all
    . simp_all

def reflectPure [BEq α] [LawfulBEq α] : {r : Reflector α // Reflects (pure a) r} :=
  Subtype.mk (fun a' => if a == a' then [[]] else []) pure_reflects

def reflectBind {x : ParserGen α} {f : α → ParserGen β}
    (inv : β → Option α)
    (hinv : ∀ a b cs cs' cs'', x.run cs = some (a, cs') → (f a).run cs' = some (b, cs'') → inv b = some a)
    (hx : {r : Reflector α // Reflects x r})
    (hf : ∀ a, {r : Reflector β // Reflects (f a) r}) :
    {r : Reflector β // Reflects (x >>= f) r} :=
  Subtype.mk (fun b =>
      (inv b).toList |>.flatMap fun a =>
      hx.val a |>.flatMap fun cs₁ =>
      (hf a).val b |>.flatMap fun cs₂ =>
      [cs₁ ++ cs₂]) <| by
    exact bind_reflects inv hinv hx.property (fun a => (hf a).property)

def reflectChoose : {r : Reflector Nat // Reflects (choose lo hi h) r} :=
  Subtype.mk (fun a => if lo ≤ a ∧ a ≤ hi then [[a]] else []) choose_reflects

section simple_example

/-!
Here's a simple example. This generator produces 1 or 2, and we should be able to reflect on 1 or 2
to get choices `[0]` or `[1]` respectively.
-/

def genOneOrTwo : Gen Nat := do
  if (← choose 0 1 (by simp)) == 0 then
    pure 1
  else
    pure 2

def reflectOneOrTwo : {r : Reflector Nat // Reflects genOneOrTwo r} := by
  unfold genOneOrTwo
  -- Unlike with normal reflectives, we provide this inverse in a _proof_ not in the generator.
  apply reflectBind (inv := fun | 1 => some 0 | 2 => some 1 | _ => none)
  -- We also need to prove that the inverse is actually an inverse.
  case hinv =>
    intro a b cs cs' cs'' h₁ h₂
    simp_all [StateT.run, pure]
    by_cases heq : a = 0
    . simp [heq, StateT.pure] at h₂
      rw [← h₂.1]
      grind
    . simp [heq, StateT.pure] at h₂
      rw [← h₂.1]
      simp
      simp [choose] at h₁
      cases cs <;> grind
  -- After that, the rest of the proof is trivial.
  . apply reflectChoose
  . intro a
    split
    . apply reflectPure
    . apply reflectPure

end simple_example
