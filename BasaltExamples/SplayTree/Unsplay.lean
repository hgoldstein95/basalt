/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import BasaltExamples.SplayTree.Packed
import BasaltExamples.SplayTree.Special

open RandomChoice

/-!
# Splay Trees: the Special Structure, Constructed

`Tree.genSpecialUnsplay n lo hi` generates the benchmark's *additional property* (Dewey, Nichols and
Hardekopf, ICSE 2015, §V) without filtering. Its trees are pre-images of a splay — a node carrying
the subtree the splay will leave to its right, wrapped in the rotation patterns `Tree.splay`
consumes — which pins the node count and bounds the height from below and the height after one
splay from above, so every draw is special by construction rather than by test.
-/

namespace SplayTree

/-- The node count of a `k`-level unsplay tree with a `c`-node core subtree and hanging subtrees of
`s` nodes each. -/
def unsplaySize (s c k : Nat) : Nat := 1 + c + 2 * k * (s + 1)

/-- The depth cap of a hanging subtree: the least depth that holds `s` nodes, so that a hanging
subtree of exactly `s` nodes has exactly this height. -/
def hangDepth (s : Nat) : Nat := Nat.clog 2 (s + 1)

/-- The depth each side of the splayed node starts at, before the levels add one apiece. -/
def postDepth (s c : Nat) : Nat := max (hangDepth c) (hangDepth s + 1)

theorem unsplaySize_succ (s c k : Nat) :
    unsplaySize s c (k + 1) = unsplaySize s c k + 2 * (s + 1) := by
  simp only [unsplaySize]; ring

theorem hangDepth_spec (s : Nat) : s + 1 ≤ 2 ^ hangDepth s :=
  Nat.le_pow_clog (by norm_num) _

/-- A `k`-fold wrapping of the node `x` — which carries a `c`-node subtree of its own — in the
patterns `Tree.splay` consumes, with `s`-node subtrees hanging off every level. Every level is one
of `Tree.splay`'s four double rotations, so one splay of `x` unwinds the whole access path in a
single pass; the three blocks of a level always occupy `[lo, p₁ - 1]`, `[p₁ + 1, p₂ - 1]` and
`[p₂ + 1, hi]`, and the constructors differ only in which block continues the wrapping and where
the two pivots sit. -/
inductive Tree.IsUnsplay (s c : Nat) : Nat → Int → Int → Int → Tree → Prop
  | core {lo hi x C} (hlo : lo ≤ x) (hhi : x ≤ hi)
      (hC : Tree.isPacked c (hangDepth c) (x + 1) hi C) :
      Tree.IsUnsplay s c 0 lo hi x (.node .leaf x C)
  | zigzig {k lo hi x b₁ p₁ b₂ p₂ b₃}
      (h₁ : Tree.IsUnsplay s c k lo (p₁ - 1) x b₁)
      (h₂ : Tree.isPacked s (hangDepth s) (p₁ + 1) (p₂ - 1) b₂)
      (h₃ : Tree.isPacked s (hangDepth s) (p₂ + 1) hi b₃)
      (hp : p₁ < p₂) (hhi : p₂ ≤ hi) :
      Tree.IsUnsplay s c (k + 1) lo hi x (.node (.node b₁ p₁ b₂) p₂ b₃)
  | zigzag {k lo hi x b₁ p₁ b₂ p₂ b₃}
      (h₁ : Tree.isPacked s (hangDepth s) lo (p₁ - 1) b₁)
      (h₂ : Tree.IsUnsplay s c k (p₁ + 1) (p₂ - 1) x b₂)
      (h₃ : Tree.isPacked s (hangDepth s) (p₂ + 1) hi b₃)
      (hlo : lo ≤ p₁) (hhi : p₂ ≤ hi) :
      Tree.IsUnsplay s c (k + 1) lo hi x (.node (.node b₁ p₁ b₂) p₂ b₃)
  | zagzig {k lo hi x b₁ p₁ b₂ p₂ b₃}
      (h₁ : Tree.isPacked s (hangDepth s) lo (p₁ - 1) b₁)
      (h₂ : Tree.IsUnsplay s c k (p₁ + 1) (p₂ - 1) x b₂)
      (h₃ : Tree.isPacked s (hangDepth s) (p₂ + 1) hi b₃)
      (hlo : lo ≤ p₁) (hhi : p₂ ≤ hi) :
      Tree.IsUnsplay s c (k + 1) lo hi x (.node b₁ p₁ (.node b₂ p₂ b₃))
  | zagzag {k lo hi x b₁ p₁ b₂ p₂ b₃}
      (h₁ : Tree.isPacked s (hangDepth s) lo (p₁ - 1) b₁)
      (h₂ : Tree.isPacked s (hangDepth s) (p₁ + 1) (p₂ - 1) b₂)
      (h₃ : Tree.IsUnsplay s c k (p₂ + 1) hi x b₃)
      (hlo : lo ≤ p₁) (hp : p₁ < p₂) :
      Tree.IsUnsplay s c (k + 1) lo hi x (.node b₁ p₁ (.node b₂ p₂ b₃))

namespace Tree.IsUnsplay

variable {s c k : Nat} {lo hi x : Int} {t : Tree}

theorem bounds (h : Tree.IsUnsplay s c k lo hi x t) : lo ≤ x ∧ x ≤ hi := by
  induction h with
  | core hlo hhi => exact ⟨hlo, hhi⟩
  | zigzig h₁ h₂ h₃ hp hhi ih => omega
  | zigzag h₁ h₂ h₃ hlo hhi ih => omega
  | zagzig h₁ h₂ h₃ hlo hhi ih => omega
  | zagzag h₁ h₂ h₃ hlo hp ih => omega

theorem size (h : Tree.IsUnsplay s c k lo hi x t) : t.size = unsplaySize s c k := by
  induction h with
  | core hlo hhi hC => simp only [Tree.size, unsplaySize, hC.1]; omega
  | zigzig h₁ h₂ h₃ hp hhi ih =>
    rw [unsplaySize_succ]; simp only [Tree.size, ih, h₂.1, h₃.1]; omega
  | zigzag h₁ h₂ h₃ hlo hhi ih =>
    rw [unsplaySize_succ]; simp only [Tree.size, ih, h₁.1, h₃.1]; omega
  | zagzig h₁ h₂ h₃ hlo hhi ih =>
    rw [unsplaySize_succ]; simp only [Tree.size, ih, h₁.1, h₃.1]; omega
  | zagzag h₁ h₂ h₃ hlo hp ih =>
    rw [unsplaySize_succ]; simp only [Tree.size, ih, h₁.1, h₂.1]; omega

theorem isBST (h : Tree.IsUnsplay s c k lo hi x t) : t.isBST lo hi := by
  induction h with
  | core hlo hhi hC => exact ⟨hlo, hhi, trivial, hC.2.2⟩
  | zigzig h₁ h₂ h₃ hp hhi ih =>
    have hb := h₁.bounds
    exact ⟨by omega, hhi, ⟨by omega, by omega, ih, h₂.2.2⟩, h₃.2.2⟩
  | zigzag h₁ h₂ h₃ hlo hhi ih =>
    have hb := h₂.bounds
    exact ⟨by omega, hhi, ⟨hlo, by omega, h₁.2.2, ih⟩, h₃.2.2⟩
  | zagzig h₁ h₂ h₃ hlo hhi ih =>
    have hb := h₂.bounds
    exact ⟨hlo, by omega, h₁.2.2, by omega, hhi, ih, h₃.2.2⟩
  | zagzag h₁ h₂ h₃ hlo hp ih =>
    have hb := h₃.bounds
    exact ⟨hlo, by omega, h₁.2.2, hp, by omega, h₂.2.2, ih⟩

theorem mem_keys (h : Tree.IsUnsplay s c k lo hi x t) : x ∈ t.keys := by
  induction h with
  | core => simp [Tree.keys]
  | zigzig h₁ h₂ h₃ hp hhi ih | zigzag h₁ h₂ h₃ hlo hhi ih
  | zagzig h₁ h₂ h₃ hlo hhi ih | zagzag h₁ h₂ h₃ hlo hp ih => simp [Tree.keys]; tauto

theorem height_ge (h : Tree.IsUnsplay s c k lo hi x t) :
    hangDepth c + 1 + 2 * k ≤ t.height := by
  induction h with
  | core hlo hhi hC =>
    have := hC.1 ▸ Tree.clog_size_le_height _
    simp only [Tree.height, hangDepth] at *; omega
  | zigzig h₁ h₂ h₃ hp hhi ih | zigzag h₁ h₂ h₃ hlo hhi ih
  | zagzig h₁ h₂ h₃ hlo hhi ih | zagzag h₁ h₂ h₃ hlo hp ih => simp only [Tree.height]; omega

theorem height_ge_hang : ∀ {k : Nat} {lo hi x : Int} {t : Tree},
    Tree.IsUnsplay s c k lo hi x t → 1 ≤ k → hangDepth s + 2 * k ≤ t.height := by
  intro k
  induction k with
  | zero => intro _ _ _ _ _ hk; omega
  | succ k ih =>
    intro lo hi x t h _
    have key : ∀ b : Tree, b.size = s → hangDepth s ≤ b.height :=
      fun b hb => hb ▸ Tree.clog_size_le_height b
    cases h with
    | zigzig h₁ h₂ h₃ hp hhi =>
      have := key _ h₂.1
      match k with
      | 0 => simp only [Tree.height, hangDepth] at *; omega
      | k + 1 => have := ih h₁ (by omega); simp only [Tree.height, hangDepth] at *; omega
    | zigzag h₁ h₂ h₃ hlo hhi =>
      have := key _ h₁.1
      match k with
      | 0 => simp only [Tree.height, hangDepth] at *; omega
      | k + 1 => have := ih h₂ (by omega); simp only [Tree.height, hangDepth] at *; omega
    | zagzig h₁ h₂ h₃ hlo hhi =>
      have := key _ h₃.1
      match k with
      | 0 => simp only [Tree.height, hangDepth] at *; omega
      | k + 1 => have := ih h₂ (by omega); simp only [Tree.height, hangDepth] at *; omega
    | zagzag h₁ h₂ h₃ hlo hp =>
      have := key _ h₂.1
      match k with
      | 0 => simp only [Tree.height, hangDepth] at *; omega
      | k + 1 => have := ih h₃ (by omega); simp only [Tree.height, hangDepth] at *; omega

/-- One splay of `x` unwinds every level at once: the two subtrees it leaves either side of `x` each
grow by one level apiece, so the result is within depth `postDepth s c + k`. -/
theorem splay_eq (h : Tree.IsUnsplay s c k lo hi x t) :
    ∃ A B, t.splay x = .node A x B ∧
      A.height ≤ postDepth s c + k ∧ B.height ≤ postDepth s c + k := by
  induction h with
  | core hlo hhi hC =>
    rename_i C
    refine ⟨.leaf, C, ?_, by simp [Tree.height], ?_⟩
    · rw [Tree.splay.eq_def]; simp
    · have := hC.2.1; simp only [postDepth]; omega
  | zigzig h₁ h₂ h₃ hp hhi ih =>
    rename_i k' lo' hi' x' b₁ p₁ b₂ p₂ b₃
    obtain ⟨A, B, heq, hA, hB⟩ := ih
    have hb := h₁.bounds
    have hM : hangDepth s + 1 ≤ postDepth s c := le_max_right _ _
    refine ⟨A, .node B p₁ (.node b₂ p₂ b₃), ?_, by omega, ?_⟩
    · rw [Tree.splay.eq_def]
      simp only [if_neg (show ¬ x' = p₂ by omega), if_pos (show x' < p₂ by omega),
                 if_neg (show ¬ x' = p₁ by omega), if_pos (show x' < p₁ by omega), heq]
    · have := h₂.2.1; have := h₃.2.1; simp only [Tree.height]; omega
  | zigzag h₁ h₂ h₃ hlo hhi ih =>
    rename_i k' lo' hi' x' b₁ p₁ b₂ p₂ b₃
    obtain ⟨A, B, heq, hA, hB⟩ := ih
    have hb := h₂.bounds
    have hM : hangDepth s + 1 ≤ postDepth s c := le_max_right _ _
    refine ⟨.node b₁ p₁ A, .node B p₂ b₃, ?_, ?_, ?_⟩
    · rw [Tree.splay.eq_def]
      simp only [if_neg (show ¬ x' = p₂ by omega), if_pos (show x' < p₂ by omega),
                 if_neg (show ¬ x' = p₁ by omega), if_neg (show ¬ x' < p₁ by omega), heq]
    · have := h₁.2.1; simp only [Tree.height]; omega
    · have := h₃.2.1; simp only [Tree.height]; omega
  | zagzig h₁ h₂ h₃ hlo hhi ih =>
    rename_i k' lo' hi' x' b₁ p₁ b₂ p₂ b₃
    obtain ⟨A, B, heq, hA, hB⟩ := ih
    have hb := h₂.bounds
    have hM : hangDepth s + 1 ≤ postDepth s c := le_max_right _ _
    refine ⟨.node b₁ p₁ A, .node B p₂ b₃, ?_, ?_, ?_⟩
    · rw [Tree.splay.eq_def]
      simp only [if_neg (show ¬ x' = p₁ by omega), if_neg (show ¬ x' < p₁ by omega),
                 if_neg (show ¬ x' = p₂ by omega), if_neg (show ¬ p₂ < x' by omega), heq]
    · have := h₁.2.1; simp only [Tree.height]; omega
    · have := h₃.2.1; simp only [Tree.height]; omega
  | zagzag h₁ h₂ h₃ hlo hp ih =>
    rename_i k' lo' hi' x' b₁ p₁ b₂ p₂ b₃
    obtain ⟨A, B, heq, hA, hB⟩ := ih
    have hb := h₃.bounds
    have hM : hangDepth s + 1 ≤ postDepth s c := le_max_right _ _
    refine ⟨.node (.node b₁ p₁ b₂) p₂ A, B, ?_, ?_, by omega⟩
    · rw [Tree.splay.eq_def]
      simp only [if_neg (show ¬ x' = p₁ by omega), if_neg (show ¬ x' < p₁ by omega),
                 if_neg (show ¬ x' = p₂ by omega), if_pos (show p₂ < x' by omega), heq]
    · have := h₁.2.1; have := h₂.2.1; simp only [Tree.height]; omega

end Tree.IsUnsplay

/-- Generates a `k`-level unsplay tree with `s`-node subtrees hanging off every level and keys in
`[lo, hi]`. `dy` places the outer pivot in the window that leaves the last block room and `dz`
places the inner pivot between the start of its own window and the outer pivot; the two `pick`s
choose which of `Tree.splay`'s four double rotations the level is built to feed. Every draw is an
offset from `0`, so the generator carries no feasibility proof. -/
def Tree.genUnsplay [Gen G] (s c : Nat) : (k : Nat) → (lo hi : Int) → G Tree
  | 0, lo, hi => do
    let d ← chooseNat 0 (hi - lo - (c : Int)).toNat
    let C ← Tree.genPacked c (hangDepth c) (lo + d + 1) hi
    pure (.node .leaf (lo + d) C)
  | k + 1, lo, hi => do
    let dy ← chooseNat 0 (hi - lo + 1 - (unsplaySize s c k : Int) - 2 * ((s : Int) + 1)).toNat
    let dz ← chooseNat 0 dy
    pick
      (fun () => pick
        (fun () => do
          let p₁ := lo + (unsplaySize s c k : Int) + (dz : Int)
          let p₂ := lo + (unsplaySize s c k : Int) + (s : Int) + 1 + (dy : Int)
          let b₁ ← Tree.genUnsplay s c k lo (p₁ - 1)
          let b₂ ← Tree.genPacked s (hangDepth s) (p₁ + 1) (p₂ - 1)
          let b₃ ← Tree.genPacked s (hangDepth s) (p₂ + 1) hi
          pure (.node (.node b₁ p₁ b₂) p₂ b₃))
        (fun () => do
          let p₁ := lo + (s : Int) + (dz : Int)
          let p₂ := lo + (s : Int) + (unsplaySize s c k : Int) + 1 + (dy : Int)
          let b₁ ← Tree.genPacked s (hangDepth s) lo (p₁ - 1)
          let b₂ ← Tree.genUnsplay s c k (p₁ + 1) (p₂ - 1)
          let b₃ ← Tree.genPacked s (hangDepth s) (p₂ + 1) hi
          pure (.node (.node b₁ p₁ b₂) p₂ b₃)))
      (fun () => pick
        (fun () => do
          let p₁ := lo + (s : Int) + (dz : Int)
          let p₂ := lo + (s : Int) + (unsplaySize s c k : Int) + 1 + (dy : Int)
          let b₁ ← Tree.genPacked s (hangDepth s) lo (p₁ - 1)
          let b₂ ← Tree.genUnsplay s c k (p₁ + 1) (p₂ - 1)
          let b₃ ← Tree.genPacked s (hangDepth s) (p₂ + 1) hi
          pure (.node b₁ p₁ (.node b₂ p₂ b₃)))
        (fun () => do
          let p₁ := lo + (s : Int) + (dz : Int)
          let p₂ := lo + (s : Int) + (s : Int) + 1 + (dy : Int)
          let b₁ ← Tree.genPacked s (hangDepth s) lo (p₁ - 1)
          let b₂ ← Tree.genPacked s (hangDepth s) (p₁ + 1) (p₂ - 1)
          let b₃ ← Tree.genUnsplay s c k (p₂ + 1) hi
          pure (.node b₁ p₁ (.node b₂ p₂ b₃))))

theorem Tree.genUnsplay_mem_support (s c k : Nat) (lo hi : Int) (t : Tree)
    (hw : (unsplaySize s c k : Int) ≤ hi - lo + 1) :
    t ∈ SPMF.support (Tree.genUnsplay s c k lo hi) ↔ ∃ x, Tree.IsUnsplay s c k lo hi x t := by
  induction k generalizing lo hi t with
  | zero =>
    rw [Tree.genUnsplay]
    simp only [unsplaySize] at hw
    have hpc := hangDepth_spec c
    support_simp
    constructor
    · rintro ⟨d, ⟨-, hd⟩, C, hC, rfl⟩
      exact ⟨lo + d, .core (by omega) (by omega)
        ((Tree.genPacked_mem_support C c _ _ _ hpc (by omega)).mp hC)⟩
    · rintro ⟨x, h⟩
      cases h with
      | core hlo hhi hC =>
        rename_i C
        have e : (C.size : Int) ≤ max 0 (hi - (x + 1) + 1) := Tree.size_le_of_isBST hC.2.2
        rw [hC.1] at e
        refine ⟨(x - lo).toNat, ⟨Nat.zero_le _, by omega⟩, ?_⟩
        rw [show lo + ((x - lo).toNat : Int) = x from by omega]
        exact ⟨C, (Tree.genPacked_mem_support C c _ _ _ hpc (by omega)).mpr hC, rfl⟩
  | succ k ih =>
    rw [Tree.genUnsplay]
    have hmk : 1 ≤ unsplaySize s c k := by simp only [unsplaySize]; omega
    have hpk := hangDepth_spec s
    rw [unsplaySize_succ] at hw
    support_simp
    constructor
    · rintro ⟨dy, ⟨-, hdy⟩, dz, ⟨-, hdz⟩, (hb | hb) | (hb | hb)⟩
      · obtain ⟨b₁, hb₁, b₂, hb₂, b₃, hb₃, rfl⟩ := hb
        obtain ⟨x, hx⟩ := (ih lo _ b₁ (by omega)).mp hb₁
        exact ⟨x, .zigzig hx
          ((Tree.genPacked_mem_support b₂ s _ _ _ hpk (by omega)).mp hb₂)
          ((Tree.genPacked_mem_support b₃ s _ _ _ hpk (by omega)).mp hb₃) (by omega) (by omega)⟩
      · obtain ⟨b₁, hb₁, b₂, hb₂, b₃, hb₃, rfl⟩ := hb
        obtain ⟨x, hx⟩ := (ih _ _ b₂ (by omega)).mp hb₂
        exact ⟨x, .zigzag ((Tree.genPacked_mem_support b₁ s _ _ _ hpk (by omega)).mp hb₁) hx
          ((Tree.genPacked_mem_support b₃ s _ _ _ hpk (by omega)).mp hb₃) (by omega) (by omega)⟩
      · obtain ⟨b₁, hb₁, b₂, hb₂, b₃, hb₃, rfl⟩ := hb
        obtain ⟨x, hx⟩ := (ih _ _ b₂ (by omega)).mp hb₂
        exact ⟨x, .zagzig ((Tree.genPacked_mem_support b₁ s _ _ _ hpk (by omega)).mp hb₁) hx
          ((Tree.genPacked_mem_support b₃ s _ _ _ hpk (by omega)).mp hb₃) (by omega) (by omega)⟩
      · obtain ⟨b₁, hb₁, b₂, hb₂, b₃, hb₃, rfl⟩ := hb
        obtain ⟨x, hx⟩ := (ih _ _ b₃ (by omega)).mp hb₃
        exact ⟨x, .zagzag ((Tree.genPacked_mem_support b₁ s _ _ _ hpk (by omega)).mp hb₁)
          ((Tree.genPacked_mem_support b₂ s _ _ _ hpk (by omega)).mp hb₂) hx (by omega) (by omega)⟩
    · rintro ⟨x, h⟩
      cases h with
      | zigzig h₁ h₂ h₃ hp hhi =>
        rename_i b₁ p₁ b₂ p₂ b₃
        have e₁ : (b₁.size : Int) ≤ max 0 (p₁ - 1 - lo + 1) := Tree.size_le_of_isBST h₁.isBST
        have e₂ : (b₂.size : Int) ≤ max 0 (p₂ - 1 - (p₁ + 1) + 1) := Tree.size_le_of_isBST h₂.2.2
        have e₃ : (b₃.size : Int) ≤ max 0 (hi - (p₂ + 1) + 1) := Tree.size_le_of_isBST h₃.2.2
        rw [h₁.size] at e₁; rw [h₂.1] at e₂; rw [h₃.1] at e₃
        refine ⟨(p₂ - lo - (unsplaySize s c k : Int) - (s : Int) - 1).toNat, ⟨Nat.zero_le _, by omega⟩,
                (p₁ - lo - (unsplaySize s c k : Int)).toNat, ⟨Nat.zero_le _, by omega⟩,
                Or.inl (Or.inl ?_)⟩
        rw [show lo + (unsplaySize s c k : Int) + ((p₁ - lo - (unsplaySize s c k : Int)).toNat : Int)
              = p₁ from by omega,
            show lo + (unsplaySize s c k : Int) + (s : Int) + 1
                + ((p₂ - lo - (unsplaySize s c k : Int) - (s : Int) - 1).toNat : Int)
              = p₂ from by omega]
        exact ⟨b₁, (ih lo (p₁ - 1) b₁ (by omega)).mpr ⟨x, h₁⟩,
               b₂, (Tree.genPacked_mem_support b₂ s _ _ _ hpk (by omega)).mpr h₂,
               b₃, (Tree.genPacked_mem_support b₃ s _ _ _ hpk (by omega)).mpr h₃, rfl⟩
      | zigzag h₁ h₂ h₃ hlo hhi =>
        rename_i b₁ p₁ b₂ p₂ b₃
        have e₁ : (b₁.size : Int) ≤ max 0 (p₁ - 1 - lo + 1) := Tree.size_le_of_isBST h₁.2.2
        have e₂ : (b₂.size : Int) ≤ max 0 (p₂ - 1 - (p₁ + 1) + 1) := Tree.size_le_of_isBST h₂.isBST
        have e₃ : (b₃.size : Int) ≤ max 0 (hi - (p₂ + 1) + 1) := Tree.size_le_of_isBST h₃.2.2
        rw [h₁.1] at e₁; rw [h₂.size] at e₂; rw [h₃.1] at e₃
        refine ⟨(p₂ - lo - (s : Int) - (unsplaySize s c k : Int) - 1).toNat,
                ⟨Nat.zero_le _, by omega⟩,
                (p₁ - lo - (s : Int)).toNat, ⟨Nat.zero_le _, by omega⟩, Or.inl (Or.inr ?_)⟩
        rw [show lo + (s : Int) + ((p₁ - lo - (s : Int)).toNat : Int) = p₁ from by omega,
            show lo + (s : Int) + (unsplaySize s c k : Int) + 1
                + ((p₂ - lo - (s : Int) - (unsplaySize s c k : Int) - 1).toNat : Int)
              = p₂ from by omega]
        exact ⟨b₁, (Tree.genPacked_mem_support b₁ s _ _ _ hpk (by omega)).mpr h₁,
               b₂, (ih (p₁ + 1) (p₂ - 1) b₂ (by omega)).mpr ⟨x, h₂⟩,
               b₃, (Tree.genPacked_mem_support b₃ s _ _ _ hpk (by omega)).mpr h₃, rfl⟩
      | zagzig h₁ h₂ h₃ hlo hhi =>
        rename_i b₁ p₁ b₂ p₂ b₃
        have e₁ : (b₁.size : Int) ≤ max 0 (p₁ - 1 - lo + 1) := Tree.size_le_of_isBST h₁.2.2
        have e₂ : (b₂.size : Int) ≤ max 0 (p₂ - 1 - (p₁ + 1) + 1) := Tree.size_le_of_isBST h₂.isBST
        have e₃ : (b₃.size : Int) ≤ max 0 (hi - (p₂ + 1) + 1) := Tree.size_le_of_isBST h₃.2.2
        rw [h₁.1] at e₁; rw [h₂.size] at e₂; rw [h₃.1] at e₃
        refine ⟨(p₂ - lo - (s : Int) - (unsplaySize s c k : Int) - 1).toNat,
                ⟨Nat.zero_le _, by omega⟩,
                (p₁ - lo - (s : Int)).toNat, ⟨Nat.zero_le _, by omega⟩, Or.inr (Or.inl ?_)⟩
        rw [show lo + (s : Int) + ((p₁ - lo - (s : Int)).toNat : Int) = p₁ from by omega,
            show lo + (s : Int) + (unsplaySize s c k : Int) + 1
                + ((p₂ - lo - (s : Int) - (unsplaySize s c k : Int) - 1).toNat : Int)
              = p₂ from by omega]
        exact ⟨b₁, (Tree.genPacked_mem_support b₁ s _ _ _ hpk (by omega)).mpr h₁,
               b₂, (ih (p₁ + 1) (p₂ - 1) b₂ (by omega)).mpr ⟨x, h₂⟩,
               b₃, (Tree.genPacked_mem_support b₃ s _ _ _ hpk (by omega)).mpr h₃, rfl⟩
      | zagzag h₁ h₂ h₃ hlo hp =>
        rename_i b₁ p₁ b₂ p₂ b₃
        have e₁ : (b₁.size : Int) ≤ max 0 (p₁ - 1 - lo + 1) := Tree.size_le_of_isBST h₁.2.2
        have e₂ : (b₂.size : Int) ≤ max 0 (p₂ - 1 - (p₁ + 1) + 1) := Tree.size_le_of_isBST h₂.2.2
        have e₃ : (b₃.size : Int) ≤ max 0 (hi - (p₂ + 1) + 1) := Tree.size_le_of_isBST h₃.isBST
        rw [h₁.1] at e₁; rw [h₂.1] at e₂; rw [h₃.size] at e₃
        refine ⟨(p₂ - lo - (s : Int) - (s : Int) - 1).toNat, ⟨Nat.zero_le _, by omega⟩,
                (p₁ - lo - (s : Int)).toNat, ⟨Nat.zero_le _, by omega⟩, Or.inr (Or.inr ?_)⟩
        rw [show lo + (s : Int) + ((p₁ - lo - (s : Int)).toNat : Int) = p₁ from by omega,
            show lo + (s : Int) + (s : Int) + 1
                + ((p₂ - lo - (s : Int) - (s : Int) - 1).toNat : Int) = p₂ from by omega]
        exact ⟨b₁, (Tree.genPacked_mem_support b₁ s _ _ _ hpk (by omega)).mpr h₁,
               b₂, (Tree.genPacked_mem_support b₂ s _ _ _ hpk (by omega)).mpr h₂,
               b₃, (ih (p₂ + 1) hi b₃ (by omega)).mpr ⟨x, h₃⟩, rfl⟩

theorem Tree.genUnsplay.sound_complete {s c k : Nat} {lo hi : Int}
    (hw : (unsplaySize s c k : Int) ≤ hi - lo + 1) :
    IsSoundAndComplete (Tree.genUnsplay s c k lo hi)
      (fun t => ∃ x, Tree.IsUnsplay s c k lo hi x t) :=
  fun t => Tree.genUnsplay_mem_support s c k lo hi t hw

theorem Tree.genUnsplay.terminates (s c k : Nat) (lo hi : Int) :
    IsAlmostSurelyTerminating (Tree.genUnsplay s c k lo hi) := by
  induction k generalizing lo hi with
  | zero =>
    rw [Tree.genUnsplay]
    exact SPMF.IsPMF_bind (SPMF.IsPMF_chooseNat _ _ _) fun _ =>
      SPMF.IsPMF_bind (Tree.genPacked.terminates _ _ _ _) fun _ => SPMF.IsPMF_pure _
  | succ k ih =>
    rw [Tree.genUnsplay]
    refine SPMF.IsPMF_bind (SPMF.IsPMF_chooseNat _ _ _) fun _ => ?_
    refine SPMF.IsPMF_bind (SPMF.IsPMF_chooseNat _ _ _) fun _ => ?_
    refine SPMF.IsPMF_pick (SPMF.IsPMF_pick ?_ ?_) (SPMF.IsPMF_pick ?_ ?_) <;>
      refine SPMF.IsPMF_bind ?_ fun _ => SPMF.IsPMF_bind ?_ fun _ =>
        SPMF.IsPMF_bind ?_ fun _ => SPMF.IsPMF_pure _ <;>
      first
        | exact ih _ _
        | exact Tree.genPacked.terminates _ _ _ _

theorem Tree.genUnsplay.cost_bounded (s c k : Nat) (lo hi : Int) :
    IsCostBounded (Tree.genUnsplay s c k lo hi) (fun t => 2 * t.size) := by
  unfold IsCostBounded
  induction k generalizing lo hi with
  | zero =>
    rw [Tree.genUnsplay, IsBounded_iff]
    rintro ⟨t, n⟩ hmem
    cost_support_simp at hmem
    obtain ⟨d, nd, m2, ⟨-, hnd⟩, ⟨C, nC, m3, hC, ⟨rfl, hm3⟩, hm2⟩, hn⟩ := hmem
    have g := Tree.genPacked.cost_bounded c (hangDepth c) _ _ (C, nC) hC
    simp only [Tree.size]
    simp only at g ⊢
    omega
  | succ k ih =>
    rw [Tree.genUnsplay, IsBounded_iff]
    rintro ⟨t, n⟩ hmem
    cost_support_simp at hmem
    obtain ⟨dy, ny, m2, ⟨-, hny⟩, ⟨dz, nz, m3, ⟨-, hnz⟩,
      ⟨mo, hmo, ⟨mi, hmi, hbr⟩ | ⟨mi, hmi, hbr⟩⟩, hm3⟩, hn⟩ := hmem
    all_goals
      rcases hbr with
        ⟨c₁, n₁, r₁, hc₁, ⟨c₂, n₂, r₂, hc₂, ⟨c₃, n₃, r₃, hc₃, ⟨rfl, e₃⟩, e₂⟩, e₁⟩, e₀⟩ |
        ⟨c₁, n₁, r₁, hc₁, ⟨c₂, n₂, r₂, hc₂, ⟨c₃, n₃, r₃, hc₃, ⟨rfl, e₃⟩, e₂⟩, e₁⟩, e₀⟩
    all_goals
      first
        | (have g₁ := ih _ _ (c₁, n₁) hc₁
           have g₂ := Tree.genPacked.cost_bounded s (hangDepth s) _ _ (c₂, n₂) hc₂
           have g₃ := Tree.genPacked.cost_bounded s (hangDepth s) _ _ (c₃, n₃) hc₃)
        | (have g₁ := Tree.genPacked.cost_bounded s (hangDepth s) _ _ (c₁, n₁) hc₁
           have g₂ := ih _ _ (c₂, n₂) hc₂
           have g₃ := Tree.genPacked.cost_bounded s (hangDepth s) _ _ (c₃, n₃) hc₃)
        | (have g₁ := Tree.genPacked.cost_bounded s (hangDepth s) _ _ (c₁, n₁) hc₁
           have g₂ := Tree.genPacked.cost_bounded s (hangDepth s) _ _ (c₂, n₂) hc₂
           have g₃ := ih _ _ (c₃, n₃) hc₃)
    all_goals (simp only [Tree.size]; simp only at g₁ g₂ g₃ ⊢; omega)

/-- The `(levels, hanging size, core size)` triples whose unsplay trees are the special splay trees
of the benchmark within a budget of `n` nodes. `Tree.IsUnsplay` pins the node count and bounds the
height from below and the height after a splay from above, all in closed form in the three
parameters, so both of the paper's conjuncts become a decidable scan of a polynomial grid and the
generator itself never rejects a tree. -/
def unsplayParams (n : Nat) : List (Nat × Nat × Nat) :=
  ((List.range (n + 1)).flatMap fun k => (List.range (n + 1)).flatMap fun s =>
      (List.range (n - 2 * k * (s + 1))).map fun c => (k, s, c)).filter
    fun p => decide (1 ≤ p.1 ∧ unsplaySize p.2.1 p.2.2 p.1 ≤ n ∧
      splayBound (unsplaySize p.2.1 p.2.2 p.1) + 1
        < max (hangDepth p.2.2 + 1) (hangDepth p.2.1) + 2 * p.1 ∧
      postDepth p.2.1 p.2.2 + p.1 + 1 ≤ splayBound (unsplaySize p.2.1 p.2.2 p.1) + 1)

theorem unsplayParams_spec {n k s c : Nat} (h : (k, s, c) ∈ unsplayParams n) :
    1 ≤ k ∧ unsplaySize s c k ≤ n ∧
      splayBound (unsplaySize s c k) + 1 < max (hangDepth c + 1) (hangDepth s) + 2 * k ∧
      postDepth s c + k + 1 ≤ splayBound (unsplaySize s c k) + 1 := by
  simpa using (List.mem_filter.mp h).2

/-- Two levels with nothing hanging — a five-node left spine — is feasible under every budget the
property admits, which is what keeps `Tree.genSpecialUnsplay`'s parameter list nonempty. Five is not
a slack bound: `Tree.not_isSpecial_of_size_le_four` rules out everything smaller, so the hypothesis
here is exactly the condition under which there is anything to generate. -/
theorem mem_unsplayParams {n : Nat} (h5 : 5 ≤ n) : (2, 0, 0) ∈ unsplayParams n := by
  simp only [unsplayParams, List.mem_filter, List.mem_flatMap, List.mem_map, List.mem_range,
    decide_eq_true_eq]
  exact ⟨⟨2, by omega, 0, by omega, 0, by omega, rfl⟩, by omega,
    by simp only [unsplaySize]; omega, by decide, by decide⟩

/-- Generates a special splay tree of at most `n` nodes with keys in `[lo, hi]`, by drawing feasible
shape parameters and then *constructing* a tree that satisfies the benchmark's property. -/
def Tree.genSpecialUnsplay [Gen G] (n : Nat) (lo hi : Int) (h5 : 5 ≤ n) : G Tree := do
  let p ← elements (unsplayParams n) (List.ne_nil_of_mem (mem_unsplayParams h5))
  Tree.genUnsplay p.2.1 p.2.2 p.1 lo hi

/-- The support of `Tree.genSpecialUnsplay`: an unsplay tree at some feasible parameter triple. -/
def Tree.isUnsplaySpecial (n : Nat) (lo hi : Int) (t : Tree) : Prop :=
  ∃ p ∈ unsplayParams n, ∃ x, Tree.IsUnsplay p.2.1 p.2.2 p.1 lo hi x t

theorem Tree.genSpecialUnsplay_mem_support (n : Nat) (lo hi : Int) (h5 : 5 ≤ n)
    (hw : (n : Int) ≤ hi - lo + 1) (t : Tree) :
    t ∈ SPMF.support (Tree.genSpecialUnsplay n lo hi h5) ↔ Tree.isUnsplaySpecial n lo hi t := by
  unfold Tree.genSpecialUnsplay Tree.isUnsplaySpecial
  support_simp
  constructor
  · rintro ⟨⟨k, s, c⟩, hp, ht⟩
    dsimp only at ht ⊢
    have := (unsplayParams_spec hp).2.1
    exact ⟨(k, s, c), hp, (Tree.genUnsplay_mem_support _ _ _ _ _ _ (by dsimp only; omega)).mp ht⟩
  · rintro ⟨⟨k, s, c⟩, hp, hx⟩
    dsimp only at hx ⊢
    have := (unsplayParams_spec hp).2.1
    exact ⟨(k, s, c), hp, (Tree.genUnsplay_mem_support _ _ _ _ _ _ (by dsimp only; omega)).mpr hx⟩

theorem Tree.genSpecialUnsplay.sound_complete {n : Nat} {lo hi : Int} (h5 : 5 ≤ n)
    (hw : (n : Int) ≤ hi - lo + 1) :
    IsSoundAndComplete (Tree.genSpecialUnsplay n lo hi h5) (Tree.isUnsplaySpecial n lo hi) :=
  fun t => Tree.genSpecialUnsplay_mem_support n lo hi h5 hw t

theorem Tree.genSpecialUnsplay.terminates {n : Nat} {lo hi : Int} (h5 : 5 ≤ n) :
    IsAlmostSurelyTerminating (Tree.genSpecialUnsplay n lo hi h5) :=
  SPMF.IsPMF_bind (SPMF.IsPMF_elements _ _) fun _ => Tree.genUnsplay.terminates _ _ _ _ _

theorem Tree.genSpecialUnsplay.cost_bounded {n : Nat} {lo hi : Int} (h5 : 5 ≤ n) :
    IsCostBounded (Tree.genSpecialUnsplay n lo hi h5) (fun t => 2 * t.size + 1) := by
  unfold IsCostBounded Tree.genSpecialUnsplay
  refine IsBounded_bind (cx := fun _ => 1) (cf := fun (_ : Nat × Nat × Nat) (t : Tree) => 2 * t.size)
    (IsBounded_elements _) (fun p => Tree.genUnsplay.cost_bounded p.2.1 p.2.2 p.1 lo hi) ?_
  intro p _ q _
  omega

/-- Every tree the constructive generator can produce satisfies the benchmark's property. -/
theorem Tree.isSpecial_of_isUnsplaySpecial {n : Nat} {lo hi : Int} {t : Tree}
    (h : Tree.isUnsplaySpecial n lo hi t) : t.isSpecial n lo hi := by
  obtain ⟨⟨k, s, c⟩, hp, x, hx⟩ := h
  dsimp only at hx
  obtain ⟨hk, hn, hdeep, hflat⟩ := unsplayParams_spec hp
  have hsz := hx.size
  have h1 := hx.height_ge
  have h2 := hx.height_ge_hang hk
  obtain ⟨A, B, hb, hAh, hBh⟩ := hx.splay_eq
  refine ⟨⟨by omega, hx.isBST⟩, ?_, x, hx.mem_keys, ?_⟩
  · rw [Tree.hasDeeperNode, hsz]; omega
  · rw [Tree.allWithinDepth, hb, hsz]
    simp only [Tree.height]
    omega

/-! ## Mixing: a rate for the filter

`Tree.genSpecial` is complete but can reject; `Tree.genSpecialUnsplay` cannot reject but is
incomplete. Drawing from the two with equal probability keeps the *support* of the first — nothing
the filter could produce becomes unreachable — while inheriting half the *acceptance* of the second,
which is `1`. That is the whole trick: an incomplete constructive family is still worth having when
what you need from it is a branch that never fails. -/

/-- The benchmark's special splay trees, drawn by an even mix of the constructive family and the
filter. Sound and complete like the filter alone, and productive at rate `1/2` like the constructive
family alone. -/
def Tree.genSpecialMixed [Gen G] (n : Nat) (lo hi : Int) (h5 : 5 ≤ n) : G (Option Tree) :=
  pick (fun () => some <$> Tree.genSpecialUnsplay n lo hi h5)
       (fun () => Tree.genSpecial n lo hi)

theorem Tree.genSpecialMixed.sound_complete {n : Nat} {lo hi : Int} (h5 : 5 ≤ n)
    (hw : (n : Int) ≤ hi - lo + 1) :
    IsSoundAndComplete (Tree.genSpecialMixed n lo hi h5) (isSpecialOutcome n lo hi) := by
  rintro (_ | t)
  · refine ⟨fun _ => trivial, fun _ => ?_⟩
    rw [Tree.genSpecialMixed, SPMF.mem_support_pick_iff]
    exact Or.inr (Tree.none_mem_support_genSpecial n lo hi)
  · rw [Tree.genSpecialMixed, SPMF.mem_support_pick_iff]
    constructor
    · rintro (hu | hf)
      · obtain ⟨t', ht', heq⟩ := SPMF.mem_support_map_iff.mp hu
        obtain rfl : t = t' := by simpa using heq
        exact Tree.isSpecial_of_isUnsplaySpecial
          ((Tree.genSpecialUnsplay.sound_complete h5 hw t).mp ht')
      · exact (Tree.genSpecial_mem_support t n lo hi).mp hf
    · exact fun h => Or.inr ((Tree.genSpecial_mem_support t n lo hi).mpr h)

theorem Tree.genSpecialMixed.terminates {n : Nat} {lo hi : Int} (h5 : 5 ≤ n) :
    IsAlmostSurelyTerminating (Tree.genSpecialMixed n lo hi h5) :=
  SPMF.IsPMF_pick (SPMF.IsPMF_map (Tree.genSpecialUnsplay.terminates h5))
    (Tree.genSpecial.terminates n lo hi)

/-- **Half the draws cannot fail, so at least half of them succeed.** With
`IsProductiveAtRate.expectedAttempts_le` this caps the retry loop at two draws in expectation —
a bound on the cost of rejection sampling, proved rather than measured. -/
theorem Tree.genSpecialMixed.productive_at_rate {n : Nat} {lo hi : Int} (h5 : 5 ≤ n) :
    IsProductiveAtRate (Tree.genSpecialMixed n lo hi h5) (1 / 2) := by
  rw [IsProductiveAtRate, Tree.genSpecialMixed, SPMF.massSome_pick, SPMF.massSome_map_some,
    Tree.genSpecialUnsplay.terminates h5]
  exact le_add_right (by rw [mul_one])

theorem Tree.genSpecialMixed.productive {n : Nat} {lo hi : Int} (h5 : 5 ≤ n) :
    IsProductive (Tree.genSpecialMixed n lo hi h5) :=
  IsProductive_of_IsProductiveAtRate (by norm_num) (Tree.genSpecialMixed.productive_at_rate h5)

/-- The retry loop over the mixed generator runs at most two draws in expectation. -/
theorem Tree.genSpecialMixed.expectedAttempts_le {n : Nat} {lo hi : Int} (h5 : 5 ≤ n) :
    SPMF.expectedAttempts (Tree.genSpecialMixed n lo hi h5) ≤ 2 := by
  have := (Tree.genSpecialMixed.productive_at_rate (lo := lo) (hi := hi) h5).expectedAttempts_le
    (Tree.genSpecialMixed.terminates (lo := lo) (hi := hi) h5)
  rwa [show (1 : ENNReal) / (1 / 2) = 2 by rw [one_div, one_div, inv_inv]] at this

/-- The five-node left spine is special whenever the budget and the key interval admit it, so the
filtering `Tree.genSpecial` succeeds with positive probability. With
`Tree.not_isSpecial_of_size_le_four` this is tight in `n`: below five nodes there is nothing to
find, and from five on the filter can find something. -/
theorem Tree.genSpecial.productive {n : Nat} {lo hi : Int} (h5 : 5 ≤ n) (hw : lo + 4 ≤ hi) :
    IsProductive (Tree.genSpecial n lo hi) := by
  have hp : ∀ a b : Int, Tree.isPacked 0 (hangDepth 0) a b .leaf :=
    fun a b => ⟨rfl, by simp [Tree.height, hangDepth], trivial⟩
  have h0 : Tree.IsUnsplay 0 0 0 lo lo lo (.node .leaf lo .leaf) :=
    .core le_rfl le_rfl (hp _ _)
  have h1 := Tree.IsUnsplay.zigzig (s := 0) (c := 0) (p₁ := lo + 1) (p₂ := lo + 2) (hi := lo + 2)
    (by rw [show lo + 1 - 1 = lo from by ring]; exact h0) (hp _ _) (hp _ _) (by omega) le_rfl
  have h2 := Tree.IsUnsplay.zigzig (s := 0) (c := 0) (p₁ := lo + 3) (p₂ := lo + 4) (hi := hi)
    (by rw [show lo + 3 - 1 = lo + 2 from by ring]; exact h1) (hp _ _) (hp _ _) (by omega)
    (by omega)
  exact Tree.IsProductive_genSpecial
    (Tree.isSpecial_of_isUnsplaySpecial ⟨(2, 0, 0), mem_unsplayParams h5, lo, h2⟩)

end SplayTree
