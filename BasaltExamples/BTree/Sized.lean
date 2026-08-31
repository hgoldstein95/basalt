/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt
import Basalt.Combinators
import BasaltExamples.BTree.Basic

open RandomChoice

/-!
# Generating B-Trees of a Given Node Count

`genBTreeSized t h s lo hi` generates the B-trees of order `t` and height `h` that hold exactly `s`
nodes, and `genBTreeUpTo t N lo hi` unions those over every `(h, s)` a tree of at most `N` nodes can
have — the paper's bound. A node's children no longer all claim the same width: each claims what its
own share of the node budget forces it to hold, so the keys are spaced by a *list* of reserves
(`GappedL`) rather than by one uniform `gap`.
-/

namespace BTree

/-! ## Node count -/

mutual

/-- The number of nodes in a tree. -/
def Tree.size : Tree → Nat
  | ⟨_, cs⟩ => 1 + Tree.sizes cs

/-- The number of nodes in a forest. -/
def Tree.sizes : List Tree → Nat
  | [] => 0
  | c :: cs => Tree.size c + Tree.sizes cs

end

theorem Tree.sizes_eq (cs : List Tree) : Tree.sizes cs = (cs.map Tree.size).sum := by
  induction cs with
  | nil => simp [Tree.sizes]
  | cons c cs ih => simp [Tree.sizes, ih]

theorem Tree.size_mk (ks : List Int) (cs : List Tree) :
    Tree.size ⟨ks, cs⟩ = 1 + (cs.map Tree.size).sum := by
  rw [Tree.size, Tree.sizes_eq]

theorem Tree.one_le_size (tr : Tree) : 1 ≤ tr.size := by
  match tr with
  | ⟨ks, cs⟩ => rw [Tree.size_mk]; omega

/-! ## What a node count forces

A subtree's node count bounds its height from both sides, and — because every node but the root
holds at least `t - 1` keys — forces the interval it sits in to be at least `(t - 1) * s` wide.
These are the two facts the generator's guards are built from.
-/

/-- The fewest nodes in a height-`h` subtree of a tree of order `t`: every node has the least
arity it may, `t`. -/
def minSize (t : Nat) : Nat → Nat
  | 0 => 1
  | h + 1 => 1 + t * minSize t h

/-- The most nodes in a height-`h` subtree of a tree of order `t`: every node has the greatest
arity it may, `2 * t`. -/
def maxSize (t : Nat) : Nat → Nat
  | 0 => 1
  | h + 1 => 1 + 2 * t * maxSize t h

/-- The fewest nodes in a height-`h` tree whose root holds at least `kmin` keys. The root is the one
node allowed fewer than `t` children, so it gets its own recurrence. -/
def rootMinSize (t kmin : Nat) : Nat → Nat
  | 0 => 1
  | h + 1 => 1 + (kmin + 1) * minSize t h

theorem one_le_minSize (t h : Nat) : 1 ≤ minSize t h := by
  cases h <;> simp only [minSize] <;> omega

theorem minSize_le_maxSize (ht : 1 ≤ t) (h : Nat) : minSize t h ≤ maxSize t h := by
  induction h with
  | zero => simp [minSize, maxSize]
  | succ h ih =>
    have h1 : t * minSize t h ≤ t * maxSize t h := Nat.mul_le_mul_left t ih
    have h2 : t * maxSize t h ≤ 2 * t * maxSize t h :=
      Nat.mul_le_mul_right (maxSize t h) (by omega)
    simp only [minSize, maxSize]
    omega

theorem rootMinSize_eq_minSize (ht : 1 ≤ t) (h : Nat) : rootMinSize t (t - 1) h = minSize t h := by
  cases h with
  | zero => rfl
  | succ h => simp only [rootMinSize, minSize]; congr 2; omega

/-- Height is bounded by node count: a height-`h` subtree has more than `h` nodes. -/
theorem lt_minSize (ht : 1 ≤ t) (h : Nat) : h < minSize t h := by
  induction h with
  | zero => simp [minSize]
  | succ h ih =>
    have : minSize t h ≤ t * minSize t h := Nat.le_mul_of_pos_left _ (by omega)
    simp only [minSize]
    omega

/-- Scaling a forest's node counts. -/
theorem sum_map_mul (n : Nat) (cs : List Tree) :
    (cs.map fun c => n * c.size).sum = n * (cs.map Tree.size).sum := by
  induction cs with
  | nil => simp
  | cons c cs ih => simp only [List.map_cons, List.sum_cons, ih]; ring

/-- The reserve of a subtree, `(t - 1) * (s - 1) + kmin`, run at `kmin = t - 1`. -/
theorem mul_pred_add (n s : Nat) (hs : 1 ≤ s) : n * (s - 1) + n = n * s := by
  have h : s - 1 + 1 = s := by omega
  calc n * (s - 1) + n = n * (s - 1 + 1) := by ring
    _ = n * s := by rw [h]

/-! ### Forest arithmetic -/

/-- Every child's demand on its own interval adds up to a demand on the parent's, with one extra
value for each separating key. -/
theorem Forest.sum_le {P : Int → Int → Tree → Prop} {f : Tree → Nat}
    (hP : ∀ a b c, P a b c → a + (f c : Int) ≤ b + 1) :
    ∀ (ks : List Int) (cs : List Tree) (lo hi : Int), Forest P lo hi ks cs →
      lo + ((ks.length + (cs.map f).sum : Nat) : Int) ≤ hi + 1 := by
  intro ks
  induction ks with
  | nil =>
    intro cs lo hi hf
    match cs with
    | [c] => have := hP lo hi c hf; simpa using this
    | [] => exact absurd hf not_false
    | _ :: _ :: _ => exact absurd hf not_false
  | cons k ks ih =>
    intro cs lo hi hf
    match cs with
    | [] => exact absurd hf not_false
    | c :: cs' =>
      obtain ⟨hc, hrest⟩ := hf
      have h1 := hP lo (k - 1) c hc
      have h2 := ih cs' (k + 1) hi hrest
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      push_cast at h2 ⊢
      omega

/-- A forest has one more tree than its parent has keys. -/
theorem Forest.length_eq {P : Int → Int → Tree → Prop} :
    ∀ (ks : List Int) (cs : List Tree) (lo hi : Int), Forest P lo hi ks cs →
      cs.length = ks.length + 1 := by
  intro ks
  induction ks with
  | nil =>
    intro cs lo hi hf
    match cs with
    | [c] => rfl
    | [] => exact absurd hf not_false
    | _ :: _ :: _ => exact absurd hf not_false
  | cons k ks ih =>
    intro cs lo hi hf
    match cs with
    | [] => exact absurd hf not_false
    | c :: cs' =>
      have := ih cs' (k + 1) hi hf.2
      simp only [List.length_cons] at *
      omega

/-- Every tree in a forest sits in some interval where it satisfies the forest's predicate. -/
theorem Forest.exists_of_mem {P : Int → Int → Tree → Prop} :
    ∀ (ks : List Int) (cs : List Tree) (lo hi : Int), Forest P lo hi ks cs →
      ∀ c ∈ cs, ∃ a b, P a b c := by
  intro ks
  induction ks with
  | nil =>
    intro cs lo hi hf
    match cs with
    | [c] =>
      intro c' hc'
      rw [List.mem_singleton.mp hc']
      exact ⟨lo, hi, hf⟩
    | [] => exact absurd hf not_false
    | _ :: _ :: _ => exact absurd hf not_false
  | cons k ks ih =>
    intro cs lo hi hf
    match cs with
    | [] => exact absurd hf not_false
    | c :: cs' =>
      obtain ⟨hc, hrest⟩ := hf
      intro c' hc'
      rcases List.mem_cons.mp hc' with rfl | hc'
      · exact ⟨lo, k - 1, hc⟩
      · exact ih cs' (k + 1) hi hrest c' hc'

/-- A per-child bound on any `Nat` measure adds up over a forest. -/
theorem Forest.sum_range {P : Int → Int → Tree → Prop} {f : Tree → Nat} {a b : Nat}
    (hP : ∀ x y c, P x y c → a ≤ f c ∧ f c ≤ b) :
    ∀ (ks : List Int) (cs : List Tree) (lo hi : Int), Forest P lo hi ks cs →
      (ks.length + 1) * a ≤ (cs.map f).sum ∧ (cs.map f).sum ≤ (ks.length + 1) * b := by
  intro ks
  induction ks with
  | nil =>
    intro cs lo hi hf
    match cs with
    | [c] => have := hP lo hi c hf; simpa using this
    | [] => exact absurd hf not_false
    | _ :: _ :: _ => exact absurd hf not_false
  | cons k ks ih =>
    intro cs lo hi hf
    match cs with
    | [] => exact absurd hf not_false
    | c :: cs' =>
      obtain ⟨hc, hrest⟩ := hf
      have h1 := hP lo (k - 1) c hc
      have h2 := ih cs' (k + 1) hi hrest
      simp only [List.map_cons, List.sum_cons, List.length_cons] at *
      refine ⟨?_, ?_⟩
      · have : (ks.length + 1 + 1) * a = a + (ks.length + 1) * a := by ring
        omega
      · have : (ks.length + 1 + 1) * b = b + (ks.length + 1) * b := by ring
        omega

/-- One `Nat` measure dominated by another, child by child, adds up over a forest. -/
theorem Forest.sum_le_sum {P : Int → Int → Tree → Prop} {f g : Tree → Nat} {d : Nat}
    (hP : ∀ x y c, P x y c → f c ≤ g c + d) :
    ∀ (ks : List Int) (cs : List Tree) (lo hi : Int), Forest P lo hi ks cs →
      (cs.map f).sum ≤ (cs.map g).sum + cs.length * d := by
  intro ks
  induction ks with
  | nil =>
    intro cs lo hi hf
    match cs with
    | [c] => have := hP lo hi c hf; simpa using this
    | [] => exact absurd hf not_false
    | _ :: _ :: _ => exact absurd hf not_false
  | cons k ks ih =>
    intro cs lo hi hf
    match cs with
    | [] => exact absurd hf not_false
    | c :: cs' =>
      obtain ⟨hc, hrest⟩ := hf
      have h1 := hP lo (k - 1) c hc
      have h2 := ih cs' (k + 1) hi hrest
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      have : (cs'.length + 1) * d = d + cs'.length * d := by ring
      omega

/-! ### The two facts -/

/-- A valid subtree's node count is bounded by its height. -/
theorem Tree.IsBTreeAt.size_range (ht : 1 ≤ t) : ∀ (h kmin : Nat) (lo hi : Int) (tr : Tree),
    Tree.IsBTreeAt t kmin h lo hi tr →
      rootMinSize t kmin h ≤ tr.size ∧ tr.size ≤ maxSize t h := by
  intro h
  induction h with
  | zero =>
    rintro kmin lo hi ⟨ks, cs⟩ ⟨rfl, -, -, -⟩
    simp [Tree.size_mk, rootMinSize, maxSize]
  | succ h ih =>
    rintro kmin lo hi ⟨ks, cs⟩ ⟨hmin, hmax, -, hforest⟩
    have hchild : ∀ x y c, Tree.IsBTreeAt t (t - 1) h x y c →
        minSize t h ≤ c.size ∧ c.size ≤ maxSize t h := by
      intro x y c hc
      have := ih (t - 1) x y c hc
      rwa [rootMinSize_eq_minSize ht] at this
    obtain ⟨hlo, hhi⟩ := Forest.sum_range hchild ks cs lo hi hforest
    rw [Tree.size_mk]
    refine ⟨?_, ?_⟩
    · have := Nat.mul_le_mul_right (minSize t h) (show kmin + 1 ≤ ks.length + 1 by omega)
      simp only [rootMinSize]
      omega
    · have := Nat.mul_le_mul_right (maxSize t h) (show ks.length + 1 ≤ 2 * t by omega)
      simp only [maxSize]
      omega

/-- A valid subtree of `s` nodes leaves no room to spare: every node but the root holds at least
`t - 1` keys, so its interval must hold `(t - 1) * (s - 1) + kmin` values. This is the reserve each
child claims from its parent's interval. -/
theorem Tree.IsBTreeAt.width : ∀ (h kmin : Nat) (lo hi : Int) (tr : Tree),
    Tree.IsBTreeAt t kmin h lo hi tr →
      lo + (((t - 1) * (tr.size - 1) + kmin : Nat) : Int) ≤ hi + 1 := by
  intro h
  induction h with
  | zero =>
    rintro kmin lo hi ⟨ks, cs⟩ ⟨rfl, hmin, -, hg⟩
    have hr := hg.room
    unfold Room at hr
    have hsz : Tree.size ⟨ks, ([] : List Tree)⟩ - 1 = 0 := by rw [Tree.size_mk]; simp
    rw [hsz]
    have hk : (kmin : Int) ≤ (ks.length : Int) := by exact_mod_cast hmin
    push_cast at hr ⊢
    omega
  | succ h ih =>
    rintro kmin lo hi ⟨ks, cs⟩ ⟨hmin, -, -, hforest⟩
    have hchild : ∀ a b c, Tree.IsBTreeAt t (t - 1) h a b c →
        a + (((t - 1) * c.size : Nat) : Int) ≤ b + 1 := by
      intro a b c hc
      have h1 := ih (t - 1) a b c hc
      rwa [mul_pred_add _ _ (Tree.one_le_size c)] at h1
    have hsum := Forest.sum_le hchild ks cs lo hi hforest
    rw [sum_map_mul] at hsum
    have hsz : Tree.size ⟨ks, cs⟩ - 1 = (cs.map Tree.size).sum := by rw [Tree.size_mk]; omega
    rw [hsz]
    have hk : (kmin : Int) ≤ (ks.length : Int) := by exact_mod_cast hmin
    push_cast at hsum ⊢
    omega

/-! ### The leaf-count reserve

`(t - 1) * s` misses that a B-tree's leaves all sit at depth `h`: a subtree of `s` nodes at a small
height has *many* leaves, and each leaf costs `t` values, not `t - 1`. `resv` takes the better of
the two bounds, and it is what each child claims from its parent's interval.
-/

mutual

/-- The number of leaves in a tree. -/
def Tree.leaves : Tree → Nat
  | ⟨_, []⟩ => 1
  | ⟨_, cs⟩ => Tree.leavesList cs

/-- The number of leaves in a forest. -/
def Tree.leavesList : List Tree → Nat
  | [] => 0
  | c :: cs => Tree.leaves c + Tree.leavesList cs

end

theorem Tree.leavesList_eq (cs : List Tree) : Tree.leavesList cs = (cs.map Tree.leaves).sum := by
  induction cs with
  | nil => simp [Tree.leavesList]
  | cons c cs ih => simp [Tree.leavesList, ih]

theorem Tree.leaves_cons (ks : List Int) (c : Tree) (cs : List Tree) :
    Tree.leaves ⟨ks, c :: cs⟩ = ((c :: cs).map Tree.leaves).sum := by
  rw [Tree.leaves, Tree.leavesList_eq]
  all_goals simp

theorem Tree.leaves_of_ne (ks : List Int) (cs : List Tree) (hne : cs ≠ []) :
    Tree.leaves ⟨ks, cs⟩ = (cs.map Tree.leaves).sum := by
  match cs, hne with
  | c :: cs', _ => rw [Tree.leaves_cons]

theorem Tree.one_le_leaves (tr : Tree) : 1 ≤ tr.leaves := by
  match tr with
  | ⟨ks, []⟩ => simp [Tree.leaves]
  | ⟨ks, c :: cs⟩ =>
    rw [Tree.leaves_cons]
    have := Tree.one_le_leaves c
    simp only [List.map_cons, List.sum_cons]
    omega

/-- Each child claims `t * L - 1` values; the keys between the children make up the difference. -/
theorem sum_map_leaves_pred (t : Nat) (ht : 1 ≤ t) (cs : List Tree) :
    (cs.map fun c => t * c.leaves - 1).sum + cs.length = t * (cs.map Tree.leaves).sum := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
    have hl := Tree.one_le_leaves c
    have h1 : 1 ≤ t * c.leaves := Nat.one_le_iff_ne_zero.mpr (by positivity)
    have hd : t * (c.leaves + (cs.map Tree.leaves).sum)
        = t * c.leaves + t * (cs.map Tree.leaves).sum := by ring
    simp only [List.map_cons, List.sum_cons, List.length_cons] at *
    omega

/-- The nodes of a height-`h` subtree that are not leaves: they form a height-`h - 1` subtree, so
there are at most `maxSize t (h - 1)` of them. -/
def innerSize (t : Nat) : Nat → Nat
  | 0 => 0
  | h + 1 => maxSize t h

theorem innerSize_step {t k : Nat} (hk : k ≤ 2 * t) (h : Nat) :
    1 + k * innerSize t h ≤ maxSize t h := by
  cases h with
  | zero => simp [innerSize, maxSize]
  | succ h =>
    have := Nat.mul_le_mul_right (maxSize t h) hk
    simp only [innerSize, maxSize]
    omega

/-- The values a height-`h` subtree of `s` nodes claims from its interval: at least `t - 1` per
node, and — since its leaves all sit at depth `h` — at least `t` per leaf, less one. Both halves are
lower bounds, not the exact minimum, because `innerSize` caps the inner nodes geometrically rather
than by what `s` and `h` jointly allow; the cost of the slack is a draw that fails, never a tree
that is missed. -/
def resv (t h s : Nat) : Nat := max ((t - 1) * s) (t * (s - innerSize t h) - 1)

/-- A valid subtree's interval holds `t` values per leaf, less one. -/
theorem Tree.IsBTreeAt.leaves_width (ht : 1 ≤ t) : ∀ (h kmin : Nat) (lo hi : Int) (tr : Tree),
    t - 1 ≤ kmin ∨ 1 ≤ h → Tree.IsBTreeAt t kmin h lo hi tr →
      lo + ((t * tr.leaves - 1 : Nat) : Int) ≤ hi + 1 := by
  intro h
  induction h with
  | zero =>
    rintro kmin lo hi ⟨ks, cs⟩ hk ⟨rfl, hmin, -, hg⟩
    have hroom := hg.room
    unfold Room at hroom
    have hkm : t - 1 ≤ kmin := hk.resolve_right (by omega)
    have hlv : Tree.leaves (⟨ks, []⟩ : Tree) = 1 := by simp [Tree.leaves]
    rw [hlv]
    have hk' : (kmin : Int) ≤ (ks.length : Int) := by exact_mod_cast hmin
    have hk'' : ((t - 1 : Nat) : Int) ≤ (kmin : Int) := by exact_mod_cast hkm
    push_cast at hroom hk'' ⊢
    omega
  | succ h ih =>
    rintro kmin lo hi ⟨ks, cs⟩ - ⟨hmin, hmax, hgap, hf⟩
    have hP : ∀ a b c, Tree.IsBTreeAt t (t - 1) h a b c →
        a + ((t * c.leaves - 1 : Nat) : Int) ≤ b + 1 :=
      fun a b c hc => ih (t - 1) a b c (Or.inl le_rfl) hc
    have hsum := Forest.sum_le hP ks cs lo hi hf
    have hlen := Forest.length_eq ks cs lo hi hf
    have hne : cs ≠ [] := by intro hnil; rw [hnil] at hlen; simp at hlen
    have hid := sum_map_leaves_pred t ht cs
    have hkey : t * (cs.map Tree.leaves).sum - 1
        = ks.length + (cs.map fun c => t * c.leaves - 1).sum := by omega
    rw [Tree.leaves_of_ne ks cs hne, hkey]
    exact hsum

/-- A valid subtree has few inner nodes: they form a subtree one level shorter. -/
theorem Tree.IsBTreeAt.size_le_leaves (ht : 1 ≤ t) : ∀ (h kmin : Nat) (lo hi : Int) (tr : Tree),
    Tree.IsBTreeAt t kmin h lo hi tr → tr.size ≤ tr.leaves + innerSize t h := by
  intro h
  induction h with
  | zero =>
    rintro kmin lo hi ⟨ks, cs⟩ ⟨rfl, -, -, -⟩
    simp [Tree.size_mk, Tree.leaves, innerSize]
  | succ h ih =>
    rintro kmin lo hi ⟨ks, cs⟩ ⟨hmin, hmax, hgap, hf⟩
    have hbound := Forest.sum_le_sum
      (fun x y c hc => ih (t - 1) x y c hc) ks cs lo hi hf
    have hlen := Forest.length_eq ks cs lo hi hf
    have hne : cs ≠ [] := by intro hnil; rw [hnil] at hlen; simp at hlen
    have hstep := innerSize_step (t := t) (k := cs.length) (by omega) h
    rw [Tree.size_mk, Tree.leaves_of_ne ks cs hne]
    simp only [innerSize]
    omega

/-- The leaf half of `resv`, stated for any root minimum: the interval holds `t` values for each of
the at least `s - innerSize t h` leaves, less one. -/
theorem Tree.IsBTreeAt.leaf_width (ht : 1 ≤ t) (h kmin : Nat) (lo hi : Int) (tr : Tree)
    (hk : t - 1 ≤ kmin ∨ 1 ≤ h) (hv : Tree.IsBTreeAt t kmin h lo hi tr) :
    lo + ((t * (tr.size - innerSize t h) - 1 : Nat) : Int) ≤ hi + 1 := by
  have h2 := Tree.IsBTreeAt.leaves_width ht h kmin lo hi tr hk hv
  have h3 := Tree.IsBTreeAt.size_le_leaves ht h kmin lo hi tr hv
  have h4 : t * (tr.size - innerSize t h) - 1 ≤ t * tr.leaves - 1 := by
    have hle : tr.size - innerSize t h ≤ tr.leaves := by omega
    have := Nat.mul_le_mul_left t hle
    omega
  have h5 : ((t * (tr.size - innerSize t h) - 1 : Nat) : Int) ≤ ((t * tr.leaves - 1 : Nat) : Int) :=
    by exact_mod_cast h4
  omega

/-- Both halves of `resv` are things a valid subtree's interval must hold. -/
theorem Tree.IsBTreeAt.resv_width (ht : 1 ≤ t) (h : Nat) : ∀ (lo hi : Int) (c : Tree),
    Tree.IsBTreeAt t (t - 1) h lo hi c → lo + ((resv t h c.size : Nat) : Int) ≤ hi + 1 := by
  intro lo hi c hc
  have h1 := Tree.IsBTreeAt.width (t := t) h (t - 1) lo hi c hc
  rw [mul_pred_add _ _ (Tree.one_le_size c)] at h1
  have h2 := Tree.IsBTreeAt.leaf_width ht h (t - 1) lo hi c (Or.inl le_rfl) hc
  simp only [resv]
  rcases Nat.le_total ((t - 1) * c.size) (t * (c.size - innerSize t h) - 1) with hle | hle
  · rw [max_eq_right hle]; exact h2
  · rw [max_eq_left hle]; exact h1

/-! ## Splitting a node budget

`genSizes a b k S` draws the `k` child node counts of one node. Each draw's range is exactly the
values that leave the remaining `k - 1` children a reachable total, so no draw strands the
recursion.
-/

theorem mem_support_default {α : Type u} {a : α} :
    a ∈ SPMF.support (default : SPMF α) ↔ False :=
  iff_false_intro (fun h => h rfl)

theorem sum_range_of_forall {a b : Nat} :
    ∀ (xs : List Nat), (∀ y ∈ xs, a ≤ y ∧ y ≤ b) →
      xs.length * a ≤ xs.sum ∧ xs.sum ≤ xs.length * b := by
  intro xs
  induction xs with
  | nil => simp
  | cons x xs ih =>
    intro h
    have hx := h x (by simp)
    have htl := ih fun y hy => h y (by simp [hy])
    simp only [List.length_cons, List.sum_cons]
    constructor
    · have : (xs.length + 1) * a = a + xs.length * a := by ring
      omega
    · have : (xs.length + 1) * b = b + xs.length * b := by ring
      omega

/-- Generates `k` values in `[a, b]` summing to `S`. -/
def genSizes [Gen G] (a b : Nat) : Nat → Nat → G (List Nat)
  | 0, S => if S = 0 then pure [] else default
  | k + 1, S =>
      if h : max a (S - k * b) ≤ min b (S - k * a) then do
        let x ← chooseNat (max a (S - k * b)) (min b (S - k * a)) h
        let xs ← genSizes a b k (S - x)
        return x :: xs
      else default

theorem genSizes_mem_support (a b : Nat) : ∀ (k S : Nat) (xs : List Nat),
    xs ∈ SPMF.support (genSizes a b k S : SPMF (List Nat))
      ↔ xs.length = k ∧ (∀ y ∈ xs, a ≤ y ∧ y ≤ b) ∧ xs.sum = S := by
  intro k
  induction k with
  | zero =>
    intro S xs
    rw [genSizes]
    split <;> rename_i hS
    · subst hS
      support_simp
      constructor
      · rintro rfl; simp
      · rintro ⟨hlen, -, -⟩; exact List.length_eq_zero_iff.mp hlen
    · rw [mem_support_default]
      refine ⟨False.elim, ?_⟩
      rintro ⟨hlen, -, hsum⟩
      rw [List.length_eq_zero_iff.mp hlen] at hsum
      exact hS hsum.symm
  | succ k ih =>
    intro S xs
    rw [genSizes]
    split <;> rename_i hd
    · support_simp [ih]
      constructor
      · rintro ⟨x, ⟨hx1, hx2⟩, ys, ⟨hlen, hmem, hsum⟩, rfl⟩
        simp only [max_le_iff] at hx1
        simp only [le_min_iff] at hx2
        refine ⟨by simp [hlen], ?_, ?_⟩
        · intro y hy
          rcases List.mem_cons.mp hy with rfl | hy
          · exact ⟨hx1.1, hx2.1⟩
          · exact hmem y hy
        · have := sum_range_of_forall ys hmem
          rw [hlen] at this
          simp only [List.sum_cons, hsum]
          omega
      · rintro ⟨hlen, hmem, hsum⟩
        match xs with
        | [] => simp at hlen
        | x :: ys =>
          have hlen' : ys.length = k := by simpa using hlen
          have hx := hmem x (by simp)
          have hmem' : ∀ y ∈ ys, a ≤ y ∧ y ≤ b := fun y hy => hmem y (by simp [hy])
          have hb := sum_range_of_forall ys hmem'
          rw [hlen'] at hb
          simp only [List.sum_cons] at hsum
          refine ⟨x, ⟨by simp only [max_le_iff]; omega, by simp only [le_min_iff]; omega⟩, ys, ?_,
            rfl⟩
          exact ⟨hlen', hmem', by omega⟩
    · rw [mem_support_default]
      refine ⟨False.elim, ?_⟩
      rintro ⟨hlen, hmem, hsum⟩
      match xs with
      | [] => simp at hlen
      | x :: ys =>
        have hlen' : ys.length = k := by simpa using hlen
        have hx := hmem x (by simp)
        have hb := sum_range_of_forall ys fun y hy => hmem y (by simp [hy])
        rw [hlen'] at hb
        simp only [List.sum_cons] at hsum
        exact hd (by simp only [max_le_iff, le_min_iff]; omega)

/-! ## Keys with a reserve per slot

A node's children no longer claim equal room, so the keys between them are spaced by a *list* of
reserves — one per slot, in order. `GappedL` is `Gapped` with that list in place of the single `g`.
-/

/-- The values a slot list needs: its reserves, plus one position for each key between them. -/
def needL : List Nat → Nat
  | [] => 0
  | [r] => r
  | r :: r' :: rs => r + 1 + needL (r' :: rs)

/-- `GappedL rs lo hi ks`: the keys `ks` are strictly increasing inside `[lo, hi]` and cut it into
`rs.length` intervals, the `i`-th holding at least `rs[i]` values. -/
def GappedL : List Nat → Int → Int → List Int → Prop
  | [r], lo, hi, [] => lo + r ≤ hi + 1
  | r :: r' :: rs, lo, hi, k :: ks => lo + r ≤ k ∧ GappedL (r' :: rs) (k + 1) hi ks
  | _, _, _, _ => False

theorem GappedL.length : ∀ (rs : List Nat) (lo hi : Int) (ks : List Int),
    GappedL rs lo hi ks → ks.length + 1 = rs.length := by
  intro rs
  induction rs with
  | nil => intro lo hi ks h; exact absurd h (by cases ks <;> exact not_false)
  | cons r rs ih =>
    match rs with
    | [] =>
      intro lo hi ks h
      match ks with
      | [] => rfl
      | _ :: _ => exact absurd h not_false
    | r' :: rs' =>
      intro lo hi ks h
      match ks with
      | [] => exact absurd h not_false
      | k :: ks' =>
        have := ih (k + 1) hi ks' h.2
        simp only [List.length_cons] at *
        omega

theorem GappedL.need : ∀ (rs : List Nat) (lo hi : Int) (ks : List Int),
    GappedL rs lo hi ks → lo + (needL rs : Int) ≤ hi + 1 := by
  intro rs
  induction rs with
  | nil => intro lo hi ks h; exact absurd h (by cases ks <;> exact not_false)
  | cons r rs ih =>
    match rs with
    | [] =>
      intro lo hi ks h
      match ks with
      | [] => simp only [GappedL] at h; simpa [needL] using h
      | _ :: _ => exact absurd h not_false
    | r' :: rs' =>
      intro lo hi ks h
      match ks with
      | [] => exact absurd h not_false
      | k :: ks' =>
        obtain ⟨hk, htl⟩ := h
        have := ih (k + 1) hi ks' htl
        simp only [needL]
        push_cast
        omega

theorem GappedL.gapped : ∀ (rs : List Nat) (lo hi : Int) (ks : List Int),
    GappedL rs lo hi ks → Gapped 0 lo hi ks := by
  intro rs
  induction rs with
  | nil => intro lo hi ks h; exact absurd h (by cases ks <;> exact not_false)
  | cons r rs ih =>
    match rs with
    | [] =>
      intro lo hi ks h
      match ks with
      | [] => simp only [Gapped]; simp only [GappedL] at h; omega
      | _ :: _ => exact absurd h not_false
    | r' :: rs' =>
      intro lo hi ks h
      match ks with
      | [] => exact absurd h not_false
      | k :: ks' =>
        obtain ⟨hk, htl⟩ := h
        exact ⟨by simp; omega, ih (k + 1) hi ks' htl⟩

/-- Children that each need their own room force the keys between them that far apart. -/
theorem GappedL.of_forest {P : Int → Int → Tree → Prop} {f : Tree → Nat}
    (hP : ∀ a b c, P a b c → a + (f c : Int) ≤ b + 1) :
    ∀ (ks : List Int) (cs : List Tree) (lo hi : Int), Forest P lo hi ks cs →
      GappedL (cs.map f) lo hi ks := by
  intro ks
  induction ks with
  | nil =>
    intro cs lo hi hf
    match cs with
    | [c] => simpa [GappedL] using hP lo hi c hf
    | [] => exact absurd hf not_false
    | _ :: _ :: _ => exact absurd hf not_false
  | cons k ks ih =>
    intro cs lo hi hf
    match cs with
    | [] => exact absurd hf not_false
    | c :: cs' =>
      obtain ⟨hc, hrest⟩ := hf
      have htl := ih cs' (k + 1) hi hrest
      match cs' with
      | [] => exact absurd hrest (by cases ks <;> exact not_false)
      | c' :: cs'' =>
        refine ⟨?_, htl⟩
        have := hP lo (k - 1) c hc
        omega

/-- Generates keys spaced by a reserve list: one key between each pair of consecutive slots, each
drawn from exactly the positions that leave the slots on both sides their room. -/
def genGappedL [Gen G] : List Nat → Int → Int → G (List Int)
  | [], _, _ => default
  | [r], lo, hi => if lo + (r : Int) ≤ hi + 1 then pure [] else default
  | r :: r' :: rs, lo, hi =>
      if hle : lo + (r : Int) ≤ hi - (needL (r' :: rs) : Nat) then do
        let k ← chooseInt (lo + (r : Int)) (hi - (needL (r' :: rs) : Nat)) hle
        let ks ← genGappedL (r' :: rs) (k + 1) hi
        return k :: ks
      else default

theorem genGappedL_mem_support : ∀ (rs : List Nat) (lo hi : Int) (ks : List Int),
    ks ∈ SPMF.support (genGappedL rs lo hi : SPMF (List Int)) ↔ GappedL rs lo hi ks := by
  intro rs
  induction rs with
  | nil =>
    intro lo hi ks
    rw [genGappedL, mem_support_default]
    exact ⟨False.elim, fun h => absurd h (by cases ks <;> exact not_false)⟩
  | cons r rs ih =>
    match rs with
    | [] =>
      intro lo hi ks
      rw [genGappedL]
      split <;> rename_i hd
      · support_simp
        constructor
        · rintro rfl; exact hd
        · intro h
          match ks with
          | [] => rfl
          | _ :: _ => exact absurd h not_false
      · rw [mem_support_default]
        refine ⟨False.elim, fun h => ?_⟩
        match ks with
        | [] => exact hd h
        | _ :: _ => exact absurd h not_false
    | r' :: rs' =>
      intro lo hi ks
      rw [genGappedL]
      split <;> rename_i hd
      · support_simp [ih]
        constructor
        · rintro ⟨k, ⟨hk1, hk2⟩, ks', hmem, rfl⟩
          exact ⟨hk1, hmem⟩
        · intro h
          match ks with
          | [] => exact absurd h not_false
          | k :: ks' =>
            obtain ⟨hk, htl⟩ := h
            have hneed := GappedL.need _ _ _ _ htl
            exact ⟨k, ⟨hk, by omega⟩, ks', htl, rfl⟩
      · rw [mem_support_default]
        refine ⟨False.elim, fun h => ?_⟩
        match ks with
        | [] => exact absurd h not_false
        | k :: ks' =>
          obtain ⟨hk, htl⟩ := h
          have hneed := GappedL.need _ _ _ _ htl
          exact hd (by omega)

/-! ## Nodes of a given size -/

/-- Generates the children of a node, the `i`-th at the node count `ss[i]` assigns it. -/
def genChildrenSized [Gen G] (gen : Nat → Int → Int → G Tree) :
    List Nat → Int → Int → List Int → G (List Tree)
  | [s], lo, hi, [] => do
      let c ← gen s lo hi
      return [c]
  | s :: s' :: ss, lo, hi, k :: ks => do
      let c ← gen s lo (k - 1)
      let cs ← genChildrenSized gen (s' :: ss) (k + 1) hi ks
      return c :: cs
  | _, _, _, _ => default

theorem genChildrenSized_mem_support {gen : Nat → Int → Int → SPMF Tree}
    {P : Int → Int → Tree → Prop}
    (hgen : ∀ s a b u, u ∈ SPMF.support (gen s a b) ↔ P a b u ∧ u.size = s) :
    ∀ (ss : List Nat) (ks : List Int) (lo hi : Int) (cs : List Tree),
      cs ∈ SPMF.support (genChildrenSized gen ss lo hi ks)
        ↔ Forest P lo hi ks cs ∧ cs.map Tree.size = ss := by
  intro ss
  induction ss with
  | nil =>
    intro ks lo hi cs
    rw [genChildrenSized, mem_support_default]
    · refine ⟨False.elim, ?_⟩
      rintro ⟨hf, hm⟩
      have : cs = [] := List.map_eq_nil_iff.mp hm
      subst this
      exact absurd hf (by cases ks <;> exact not_false)
    all_goals simp
  | cons s ss ih =>
    match ss with
    | [] =>
      intro ks lo hi cs
      match ks with
      | [] =>
        rw [genChildrenSized]
        support_simp [hgen]
        constructor
        · rintro ⟨c, ⟨hP, hsz⟩, rfl⟩
          exact ⟨hP, by simp [hsz]⟩
        · rintro ⟨hf, hm⟩
          match cs with
          | [c] => exact ⟨c, ⟨hf, by simpa using hm⟩, rfl⟩
          | [] => simp at hm
          | _ :: _ :: _ => simp at hm
      | k :: ks' =>
        rw [genChildrenSized, mem_support_default]
        · refine ⟨False.elim, ?_⟩
          rintro ⟨hf, hm⟩
          match cs with
          | [] => simp at hm
          | [c] => exact absurd hf.2 (by cases ks' <;> exact not_false)
          | _ :: _ :: _ => simp at hm
        all_goals simp
    | s' :: ss' =>
      intro ks lo hi cs
      match ks with
      | [] =>
        rw [genChildrenSized, mem_support_default]
        · refine ⟨False.elim, ?_⟩
          rintro ⟨hf, hm⟩
          match cs with
          | [c] => simp at hm
          | [] => exact absurd hf not_false
          | _ :: _ :: _ => exact absurd hf not_false
        all_goals simp
      | k :: ks' =>
        rw [genChildrenSized]
        support_simp [hgen, ih]
        constructor
        · rintro ⟨c, ⟨hP, hsz⟩, cs₀, ⟨hf, hm⟩, rfl⟩
          exact ⟨⟨hP, hf⟩, by simp [hsz, hm]⟩
        · rintro ⟨hf, hm⟩
          match cs with
          | [] => simp at hm
          | c :: cs₀ =>
            simp only [List.map_cons, List.cons.injEq] at hm
            exact ⟨c, ⟨hf.1, hm.1⟩, cs₀, ⟨hf.2, hm.2⟩, rfl⟩

/-- Generates a leaf: a key count the interval can hold, then that many keys. A leaf is one node,
so a node count says nothing about it beyond that. -/
def genLeafSized [Gen G] (t kmin : Nat) (lo hi : Int) : G Tree :=
  if hg : (kmin : Int) ≤ hi + 1 - lo ∧ kmin ≤ 2 * t - 1 then do
    let m ← chooseNat kmin (min (2 * t - 1) (hi + 1 - lo).toNat)
      (by simp only [le_min_iff]; exact ⟨hg.2, by omega⟩)
    let ks ← genGapped 0 m lo hi
    return ⟨ks, []⟩
  else default

theorem genLeafSized_mem_support (t kmin : Nat) (lo hi : Int) (ks : List Int) (cs : List Tree) :
    (⟨ks, cs⟩ : Tree) ∈ SPMF.support (genLeafSized t kmin lo hi : SPMF Tree)
      ↔ Tree.IsBTreeAt t kmin 0 lo hi ⟨ks, cs⟩ := by
  unfold genLeafSized
  split <;> rename_i hg
  · support_simp [Tree.mk.injEq]
    constructor
    · rintro ⟨m, ⟨hm1, hm2⟩, ks', hmem, rfl, rfl⟩
      simp only [le_min_iff] at hm2
      have hroom : Room 0 m lo hi := by unfold Room; push_cast; omega
      obtain ⟨hlen, hgap⟩ := (genGapped_mem_support 0 m lo hi ks hroom).mp hmem
      exact ⟨rfl, by omega, by omega, hgap⟩
    · rintro ⟨rfl, hmin, hmax, hgap⟩
      have hroom := hgap.room
      unfold Room at hroom
      refine ⟨ks.length, ⟨hmin, by simp only [le_min_iff]; push_cast at hroom; omega⟩, ks, ?_,
        rfl, rfl⟩
      exact (genGapped_mem_support 0 ks.length lo hi ks hroom).mpr ⟨rfl, hgap⟩
  · rw [mem_support_default]
    refine ⟨False.elim, ?_⟩
    rintro ⟨rfl, hmin, hmax, hgap⟩
    have hroom := hgap.room
    unfold Room at hroom
    exact hg ⟨by push_cast at hroom; omega, by omega⟩

/-- The arities a height-`h + 1` node of `s` nodes can have in `[lo, hi]`, given a root minimum of
`kmin` keys: enough children to share out `s - 1` nodes, few enough that they and the keys between
them fit. Every constraint is one a valid tree satisfies, so filtering by them loses nothing; each
is also what makes the corresponding draw below non-empty. -/
def arities (t kmin h s : Nat) (lo hi : Int) : List Nat :=
  (List.range (2 * t + 1)).filter fun k =>
    decide (kmin + 1 ≤ k ∧ k * minSize t h ≤ s - 1 ∧ s - 1 ≤ k * maxSize t h ∧
      lo + ((k - 1 + (t - 1) * (s - 1) : Nat) : Int) ≤ hi + 1)

theorem mem_arities {t kmin h s k : Nat} {lo hi : Int} :
    k ∈ arities t kmin h s lo hi ↔
      k ≤ 2 * t ∧ kmin + 1 ≤ k ∧ k * minSize t h ≤ s - 1 ∧ s - 1 ≤ k * maxSize t h ∧
        lo + ((k - 1 + (t - 1) * (s - 1) : Nat) : Int) ≤ hi + 1 := by
  simp only [arities, List.mem_filter, List.mem_range, decide_eq_true_eq]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by omega, h2.1, h2.2.1, h2.2.2.1, h2.2.2.2⟩
  · rintro ⟨h1, h2, h3, h4, h5⟩; exact ⟨by omega, h2, h3, h4, h5⟩

/-- Each child's node count lies in the range its height allows. -/
theorem child_size_range (ht : 1 ≤ t) {h : Nat} :
    ∀ x y c, Tree.IsBTreeAt t (t - 1) h x y c → minSize t h ≤ c.size ∧ c.size ≤ maxSize t h := by
  intro x y c hc
  have := Tree.IsBTreeAt.size_range ht h (t - 1) x y c hc
  rwa [rootMinSize_eq_minSize ht] at this

/-- A valid tree's own arity is one the guard admits: this is what makes `arities` a filter that
never excludes a tree. -/
theorem mem_arities_of_isBTreeAt (ht : 1 ≤ t) {h kmin s : Nat} {lo hi : Int} {ks : List Int}
    {cs : List Tree} (hv : Tree.IsBTreeAt t kmin (h + 1) lo hi ⟨ks, cs⟩)
    (hsize : Tree.size ⟨ks, cs⟩ = s) : ks.length + 1 ∈ arities t kmin h s lo hi := by
  obtain ⟨hmin, hmax, hgap, hf⟩ := hv
  obtain ⟨hslo, hshi⟩ := Forest.sum_range (child_size_range ht) ks cs lo hi hf
  have hsum : (cs.map Tree.size).sum = s - 1 := by rw [Tree.size_mk] at hsize; omega
  have hwidth := Tree.IsBTreeAt.width (t := t) (h + 1) ks.length lo hi ⟨ks, cs⟩
    ⟨le_rfl, hmax, hgap, hf⟩
  have hsz1 : Tree.size ⟨ks, cs⟩ - 1 = s - 1 := by rw [Tree.size_mk]; omega
  rw [hsz1] at hwidth
  rw [mem_arities]
  refine ⟨by omega, by omega, by rw [← hsum]; omega, by rw [← hsum]; omega, by push_cast at hwidth ⊢; omega⟩

/-- Generates the B-trees of order `t` and height `h` with exactly `s` nodes and keys in `[lo, hi]`,
whose root holds at least `kmin` keys: pick an arity the node count admits, share the budget out
among that many children, and space the keys so that each child gets the room its share forces. -/
def genNodeSized [Gen G] (t kmin : Nat) : (h s : Nat) → (lo hi : Int) → G Tree
  | 0, s, lo, hi => if s = 1 then genLeafSized t kmin lo hi else default
  | h + 1, s, lo, hi =>
      if hne : arities t kmin h s lo hi ≠ [] then do
        let k ← elements (arities t kmin h s lo hi) hne
        let ss ← genSizes (minSize t h) (maxSize t h) k (s - 1)
        let ks ← genGappedL (ss.map fun sc => resv t h sc) lo hi
        let cs ← genChildrenSized (fun s' a b => genNodeSized t (t - 1) h s' a b) ss lo hi ks
        return ⟨ks, cs⟩
      else default

theorem genNodeSized_mem_support (ht : 1 ≤ t) : ∀ (h kmin s : Nat) (lo hi : Int) (tr : Tree),
    tr ∈ SPMF.support (genNodeSized t kmin h s lo hi : SPMF Tree)
      ↔ Tree.IsBTreeAt t kmin h lo hi tr ∧ tr.size = s := by
  intro h
  induction h with
  | zero =>
    rintro kmin s lo hi ⟨ks, cs⟩
    rw [genNodeSized]
    have hsz : Tree.IsBTreeAt t kmin 0 lo hi ⟨ks, cs⟩ → Tree.size ⟨ks, cs⟩ = 1 := by
      rintro ⟨rfl, -, -, -⟩; simp [Tree.size_mk]
    split <;> rename_i hs
    · subst hs
      rw [genLeafSized_mem_support]
      exact ⟨fun hv => ⟨hv, hsz hv⟩, fun hv => hv.1⟩
    · rw [mem_support_default]
      exact ⟨False.elim, fun hv => hs (by rw [← hv.2, hsz hv.1])⟩
  | succ h ih =>
    rintro kmin s lo hi ⟨ks, cs⟩
    rw [genNodeSized]
    have hchild : ∀ s' a b u,
        u ∈ SPMF.support (genNodeSized t (t - 1) h s' a b : SPMF Tree)
          ↔ Tree.IsBTreeAt t (t - 1) h a b u ∧ u.size = s' := fun s' a b u => ih (t - 1) s' a b u
    split <;> rename_i hne
    · support_simp [genSizes_mem_support, genGappedL_mem_support,
        genChildrenSized_mem_support hchild, Tree.mk.injEq]
      constructor
      · rintro ⟨k, hk, ss, ⟨hlen, hmem, hsum⟩, ks', hgl, cs', ⟨hf, hm⟩, rfl, rfl⟩
        rw [mem_arities] at hk
        have hlenks : ks.length + 1 = ss.length := by
          have := GappedL.length _ _ _ _ hgl
          simpa using this
        have hmin1 := one_le_minSize t h
        have hkpos : 1 ≤ k := by omega
        have hs1 : 1 ≤ s - 1 := le_trans (le_trans hmin1 (Nat.le_mul_of_pos_left _ hkpos)) hk.2.2.1
        refine ⟨⟨by omega, by omega, GappedL.gapped _ _ _ _ hgl, hf⟩, ?_⟩
        rw [Tree.size_mk, hm, hsum]
        omega
      · rintro ⟨hv, hsize⟩
        obtain ⟨hmin, hmax, hgap, hf⟩ := hv
        obtain ⟨hslo, hshi⟩ := Forest.sum_range (child_size_range ht) ks cs lo hi hf
        have hlencs := Forest.length_eq ks cs lo hi hf
        have hsum : (cs.map Tree.size).sum = s - 1 := by rw [Tree.size_mk] at hsize; omega
        refine ⟨ks.length + 1,
          mem_arities_of_isBTreeAt ht ⟨hmin, hmax, hgap, hf⟩ hsize,
          cs.map Tree.size, ⟨by simp [hlencs], ?_, hsum⟩, ks, ?_, cs, ⟨hf, rfl⟩, rfl, rfl⟩
        · intro y hy
          obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hy
          obtain ⟨a, b, hP⟩ := Forest.exists_of_mem ks cs lo hi hf c hc
          exact child_size_range ht a b c hP
        · have := GappedL.of_forest (f := fun c => resv t h c.size)
            (Tree.IsBTreeAt.resv_width ht h) ks cs lo hi hf
          simpa [List.map_map, Function.comp_def] using this
    · rw [mem_support_default]
      refine ⟨False.elim, ?_⟩
      rintro ⟨hv, hsize⟩
      rw [not_not] at hne
      have := mem_arities_of_isBTreeAt ht hv hsize
      rw [hne] at this
      exact absurd this List.not_mem_nil

/-! ## The generators -/

/-- Generates the B-trees of order `t` with keys in `[lo, hi]`, every leaf at depth `h`, and
exactly `s` nodes. -/
def genBTreeSized [Gen G] (t h s : Nat) (lo hi : Int) : G Tree := genNodeSized t (min 1 h) h s lo hi

theorem genBTreeSized_mem_support (ht : 1 ≤ t) (h s : Nat) (lo hi : Int) (tr : Tree) :
    tr ∈ SPMF.support (genBTreeSized t h s lo hi : SPMF Tree)
      ↔ Tree.IsBTree t h lo hi tr ∧ tr.size = s :=
  genNodeSized_mem_support ht h (min 1 h) s lo hi tr

theorem genBTreeSized.sound_complete (ht : 1 ≤ t) :
    IsSoundAndComplete (genBTreeSized t h s lo hi : SPMF Tree)
      (fun tr => Tree.IsBTree t h lo hi tr ∧ tr.size = s) :=
  genBTreeSized_mem_support ht h s lo hi

/-! ## At most `N` nodes -/

/-- Height is bounded by node count, so a bound on nodes bounds both coordinates of the index. -/
theorem lt_rootMinSize (ht : 1 ≤ t) (h : Nat) : h < rootMinSize t (min 1 h) h := by
  cases h with
  | zero => simp [rootMinSize]
  | succ h =>
    have h1 := lt_minSize ht h
    have h2 : min 1 (h + 1) = 1 := by omega
    simp only [rootMinSize, h2]
    omega

/-- The `(height, node count)` pairs a B-tree of at most `N` nodes with keys in `[lo, hi]` can
have.

**The conjuncts are necessary, not sufficient: this list admits pairs whose generator produces
nothing.** `(3, 20) ∈ sizeIndices 2 20 0 20` but no order-2 tree of height `3` holds `20` nodes in
`[0, 20]` — the level counts force at least `12` leaves, while `Tree.IsBTreeAt.leaves_width` caps
them at `11` for that interval. The width conjunct here cannot see that, because it bounds the leaf
count below by `p.2 - innerSize t p.1`, which is `0` as soon as the height admits more internal
nodes than the whole tree has. The symptom is a *silently failing draw*, not a wrong support:
`genBTreeUpTo.sound_complete` still holds, since an empty branch contributes nothing to a union.
`BasaltTest/IO.lean` pins the failure. Closing it needs the true minimum leaf count for a
`(height, node count)` pair, which is what `Tree.genBTreeUpTo.terminates` is waiting on. -/
def sizeIndices (t N : Nat) (lo hi : Int) : List (Nat × Nat) :=
  ((List.range (N + 1)).flatMap fun h => (List.range (N + 1)).map fun s => (h, s)).filter
    fun p => decide (rootMinSize t (min 1 p.1) p.1 ≤ p.2 ∧ p.2 ≤ maxSize t p.1 ∧
      lo + (((t - 1) * (p.2 - 1) + min 1 p.1 : Nat) : Int) ≤ hi + 1 ∧
      (p.1 = 0 ∨ lo + ((t * (p.2 - innerSize t p.1) - 1 : Nat) : Int) ≤ hi + 1))

theorem mem_sizeIndices {t N h s : Nat} {lo hi : Int} :
    (h, s) ∈ sizeIndices t N lo hi ↔
      (h ≤ N ∧ s ≤ N) ∧ rootMinSize t (min 1 h) h ≤ s ∧ s ≤ maxSize t h ∧
        lo + (((t - 1) * (s - 1) + min 1 h : Nat) : Int) ≤ hi + 1 ∧
        (h = 0 ∨ lo + ((t * (s - innerSize t h) - 1 : Nat) : Int) ≤ hi + 1) := by
  simp only [sizeIndices, List.mem_filter, List.mem_flatMap, List.mem_map, List.mem_range,
    Prod.mk.injEq, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨h', hh', s', hs', rfl, rfl⟩, hp⟩
    exact ⟨⟨by omega, by omega⟩, hp.1, hp.2.1, hp.2.2.1, hp.2.2.2⟩
  · rintro ⟨⟨hh, hs⟩, hp⟩
    exact ⟨⟨h, by omega, s, by omega, rfl, rfl⟩, hp⟩

theorem mem_sizeIndices_of_isBTree (ht : 1 ≤ t) {N h : Nat} {lo hi : Int} {tr : Tree}
    (hv : Tree.IsBTree t h lo hi tr) (hsz : tr.size ≤ N) : (h, tr.size) ∈ sizeIndices t N lo hi := by
  have hrange := Tree.IsBTreeAt.size_range ht h (min 1 h) lo hi tr hv
  have hwidth := Tree.IsBTreeAt.width (t := t) h (min 1 h) lo hi tr hv
  have hlt := lt_rootMinSize (t := t) ht h
  rw [mem_sizeIndices]
  refine ⟨⟨by omega, hsz⟩, hrange.1, hrange.2, hwidth, ?_⟩
  match h with
  | 0 => exact Or.inl rfl
  | h + 1 => exact Or.inr (Tree.IsBTreeAt.leaf_width ht (h + 1) _ lo hi tr (Or.inr (by omega)) hv)

/-- Generates the B-trees of order `t` with keys in `[lo, hi]` that hold at most `N` nodes — the
paper's bound on B-trees — as the union of `genBTreeSized` over every `(height, node count)` pair
such a tree can have. Height and node count are pinned by the tree, so the union is disjoint. -/
def genBTreeUpTo [Gen G] (t N : Nat) (lo hi : Int) : G Tree :=
  if hne : sizeIndices t N lo hi ≠ [] then
    oneOf ((sizeIndices t N lo hi).map fun p => fun (_ : Unit) => genBTreeSized t p.1 p.2 lo hi)
      (by simpa using hne)
  else default

theorem genBTreeUpTo_mem_support (ht : 1 ≤ t) (N : Nat) (lo hi : Int) (tr : Tree) :
    tr ∈ SPMF.support (genBTreeUpTo t N lo hi : SPMF Tree)
      ↔ (∃ h, Tree.IsBTree t h lo hi tr) ∧ tr.size ≤ N := by
  unfold genBTreeUpTo
  split <;> rename_i hne
  · rw [SPMF.mem_support_oneOf_iff]
    simp only [List.mem_map]
    constructor
    · rintro ⟨g, ⟨⟨h, s⟩, hmem, rfl⟩, hsupp⟩
      rw [genBTreeSized_mem_support ht] at hsupp
      obtain ⟨hv, rfl⟩ := hsupp
      exact ⟨⟨h, hv⟩, (mem_sizeIndices.mp hmem).1.2⟩
    · rintro ⟨⟨h, hv⟩, hsz⟩
      exact ⟨_, ⟨(h, tr.size), mem_sizeIndices_of_isBTree ht hv hsz, rfl⟩,
        (genBTreeSized_mem_support ht h tr.size lo hi tr).mpr ⟨hv, rfl⟩⟩
  · rw [mem_support_default]
    refine ⟨False.elim, ?_⟩
    rintro ⟨⟨h, hv⟩, hsz⟩
    rw [not_not] at hne
    have := mem_sizeIndices_of_isBTree (N := N) ht hv hsz
    rw [hne] at this
    exact absurd this List.not_mem_nil

theorem genBTreeUpTo.sound_complete (ht : 1 ≤ t) :
    IsSoundAndComplete (genBTreeUpTo t N lo hi : SPMF Tree)
      (fun tr => (∃ h, Tree.IsBTree t h lo hi tr) ∧ tr.size ≤ N) :=
  genBTreeUpTo_mem_support ht N lo hi

end BTree
