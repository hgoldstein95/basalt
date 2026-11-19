/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Michael Hicks
-/
module

public import Std.Data.HashSet.Basic
import Std.Data.HashSet.Lemmas

/-!
# The seeds a random round hands to fuzzing

A hybrid campaign alternates *rounds*: in a random round every test is generated afresh, and in a
fuzzing round libFuzzer mutates the inputs in its corpus. A random test is a *find* if it reaches a
feature (an edge of the code, with how often it ran) that no test before it reached. When a random
round ends, its finds are reduced to a smaller set, the *seeds*, that still reaches every feature
the finds reached, and libFuzzer's corpus is seeded with them. `cover` computes the seeds; the
proofs at the end show they lose no feature and are all real finds.
-/

public section

namespace Basalt.Fuzz

/-! ## Finds -/

/-- One find of the random round that just ended (`runOneRandom` in `Runner.lean` collects them).

* `bytes` is the test itself, which libFuzzer is handed and which a generator decodes.
* `feats` is the features the test reached that no test of an *earlier round* reached, each a number
  from `basalt_feat_read` (`native.c`). A feature first reached earlier in this same round is kept,
  because the seeds are chosen among this round's finds: a later find may reach everything an
  earlier one did, and more, and then the earlier one is not needed. -/
structure Find where
  bytes : ByteArray
  feats : Array UInt32

/-- `g`'s features that are not in `covered`. `cover` calls it with `covered` the features the seeds
chosen so far reach, so it is what `g` would add as the next seed. It keeps `g`'s bytes: the same
test. -/
def Find.residual (covered : Std.HashSet UInt32) (g : Find) : Find :=
  { g with feats := g.feats.filter (!covered.contains ·) }

/-! ## The cover

`cover` is greedy: it picks, again and again, the find that adds the most features the seeds chosen
so far do not reach, and stops when no find adds any.

Rescoring every find at every pick would be slow, so the finds wait in *buckets*: an array whose
entry `k` is the list of finds last scored as adding `k` features. A find's score can only fall as
seeds are chosen, so its bucket's number bounds what it adds now. The loop therefore takes the first
find in the highest nonempty bucket and rescores only that one: if it still adds as many as its
bucket says, no other find can add more, and it is the next seed. -/

/-- A measure of the buckets, which every step of `coverLoop` lowers (with `top`): the sum, over the
waiting finds, of their bucket's number plus one. `weight k bs` counts the buckets `bs` as numbered
from `k`; `coverLoop` uses `weight 0`. -/
private def weight (k : Nat) : List (List Find) → Nat
  | [] => 0
  | l :: ls => (k + 1) * l.length + weight (k + 1) ls

/-! The three lemmas below are about `weight`, and come before `coverLoop` because Lean checks its
termination when it is defined; every other proof is at the end of the file. -/

private theorem weight_set : ∀ (ls : List (List Find)) (k i : Nat) (hi : i < ls.length)
    (v : List Find), weight k (ls.set i v) + (k + i + 1) * ls[i].length =
      weight k ls + (k + i + 1) * v.length
  | [], _, _, hi, _ => by simp at hi
  | l :: ls, k, 0, _, v => by simp [weight]; omega
  | l :: ls, k, i + 1, hi, v => by
    have := weight_set ls (k + 1) i (by simp at hi; omega) v
    simp only [List.set_cons_succ, weight, List.getElem_cons_succ]
    rw [show k + (i + 1) + 1 = k + 1 + i + 1 by omega]
    omega

private theorem toList_set (b : Array (List Find)) (i : Nat) (hi : i < b.size) (v : List Find) :
    (b.set i v).toList = b.toList.set i v := by
  apply List.ext_getElem
  · simp
  · intro j h₁ h₂
    simp only [Array.getElem_toList, Array.getElem_set, List.getElem_set]
    first | done | (split <;> simp_all)

/-- Popping a find from bucket `i` takes `i + 1` off the weight. -/
private theorem weight_pop {b : Array (List Find)} {i : Nat} (hi : i < b.size) {g : Find}
    {more : List Find} (hb : b[i] = g :: more) :
    weight 0 (b.set i more).toList + (i + 1) = weight 0 b.toList := by
  have := weight_set b.toList 0 i (by simpa using hi) more
  rw [toList_set b i hi, Array.getElem_toList, hb] at *
  simp only [List.length_cons, Nat.zero_add, Nat.mul_succ] at this
  omega

/-- Pushing a find onto bucket `k` adds `k + 1`. -/
private theorem weight_push {b : Array (List Find)} {k : Nat} (hk : k < b.size) {r : Find} :
    weight 0 (b.modify k (r :: ·)).toList = weight 0 b.toList + (k + 1) := by
  have heq : (b.modify k (r :: ·)).toList = b.toList.set k (r :: b[k]) := by
    apply List.ext_getElem
    · simp
    · intro j h₁ h₂
      simp only [Array.getElem_toList, Array.getElem_modify, List.getElem_set]
      first | done | (split <;> simp_all)
  have := weight_set b.toList 0 k (by simpa using hk) (r :: b[k])
  rw [heq]
  simp only [Array.getElem_toList, List.length_cons, Nat.zero_add, Nat.mul_succ] at this
  omega

/-- `cover`'s loop. `buckets` holds the finds still waiting, `top` is the bucket to take from (none
above it holds a find), `picked` is the seeds chosen so far, and `covered` the features they reach.
Returns the seeds, and any find still waiting, which once the bottom bucket is empty is none. -/
private def coverLoop (top : Nat) (covered : Std.HashSet UInt32) (buckets : Array (List Find))
    (picked : List Find) : List Find :=
  if h : top < buckets.size then
    match hb : buckets[top] with
    | [] =>
      -- Bucket `top` is empty: go down to the next, or stop at the bottom.
      if top = 0 then picked ++ buckets.toList.flatten
      else coverLoop (top - 1) covered buckets picked
    | g :: more =>
      -- Rescore the first find waiting in bucket `top` against what the seeds reach now.
      if (g.residual covered).feats.size = 0 then
        -- It adds nothing: drop it.
        coverLoop top covered (buckets.set top more) picked
      else if hlt : (g.residual covered).feats.size < top then
        -- It adds fewer than `top`: it waits again, in the bucket of what it adds now.
        coverLoop top covered
          ((buckets.set top more).modify (g.residual covered).feats.size (g.residual covered :: ·))
          picked
      else
        -- It still adds `top`, and no waiting find can add more: it is the next seed.
        coverLoop top (covered.insertMany (g.residual covered).feats.toList) (buckets.set top more)
          (g.residual covered :: picked)
  else picked ++ buckets.toList.flatten
termination_by weight 0 buckets.toList + top
decreasing_by
  · omega
  · have := weight_pop h hb; omega
  · have := weight_pop h hb
    have := weight_push (b := buckets.set top more) (k := (g.residual covered).feats.size)
      (r := g.residual covered) (by simp; omega)
    omega
  · have := weight_pop h hb; omega

/-- The seeds for libFuzzer, from the finds `l` of a random round. Called when a hybrid campaign
switches to fuzzing (the closure `goHybrid` in `Runner.lean` hands the C bridge). Greedy, ties going
to the shorter input. -/
def cover (l : List Find) : List Find :=
  -- The most features any find has: the top bucket.
  let n := l.foldl (fun m g => max m g.feats.size) 0
  -- Pushed longest first, so that among finds in the same bucket the shortest is taken first.
  let sorted := l.mergeSort (fun a b => decide (a.bytes.size ≥ b.bytes.size))
  let buckets :=
    sorted.foldl (fun b g => b.modify g.feats.size (g :: ·)) (Array.replicate (n + 1) [])
  coverLoop n ∅ buckets []

/-! ## Correctness

Two properties are proved of `cover l`, for any list of finds `l`:

* **Coverage** (`cover_covers`): every feature of every find in `l` is in the features of some seed
  `cover l` keeps. Handing libFuzzer the seeds instead of all the finds loses no coverage.
* **Soundness** (`cover_sub`): every seed is one of the finds (the same bytes, so the same test),
  and carries only features that find reached. A seed is never credited with coverage it does not
  have.

Both follow from an invariant of `coverLoop` (`Inv`): whatever is covered is reached by a seed chosen so far;
every feature of `l` is covered or held by a waiting find; and every seed or waiting find is one of
`l` with a subset of its features. Each step keeps it, by strong induction on the loop's measure;
when the loop ends, what it returns (the seeds, and any find still waiting) therefore reaches every
feature of `l`.

Not proved: that the cover is *small*. That is greedy set cover's own guarantee (at most `1 + ln d`
times the smallest cover, `d` the most features a find adds), which holds because every pick is a
greedy choice; the lemma that says so is not stated here. -/


private theorem mem_flat {b : Array (List Find)} {q : Find} :
    q ∈ b.toList.flatten ↔ ∃ j, ∃ h : j < b.size, q ∈ b[j] := by
  simp only [List.mem_flatten, Array.mem_toList_iff, Array.mem_iff_getElem]
  constructor
  · rintro ⟨_, ⟨j, h, rfl⟩, hq⟩; exact ⟨j, h, hq⟩
  · rintro ⟨j, h, hq⟩; exact ⟨_, ⟨j, h, rfl⟩, hq⟩

private theorem mem_flat_set {b : Array (List Find)} {i : Nat} (hi : i < b.size) {v : List Find}
    {q : Find} :
    q ∈ (b.set i v).toList.flatten ↔ q ∈ v ∨ ∃ j, ∃ h : j < b.size, j ≠ i ∧ q ∈ b[j] := by
  rw [mem_flat]
  constructor
  · rintro ⟨j, h, hq⟩
    rw [Array.getElem_set] at hq
    split at hq
    · exact .inl hq
    · exact .inr ⟨j, by simpa using h, by omega, hq⟩
  · rintro (hq | ⟨j, h, hne, hq⟩)
    · exact ⟨i, by simpa using hi, by rw [Array.getElem_set]; simpa using hq⟩
    · exact ⟨j, by simpa using h, by rw [Array.getElem_set]; simpa [Ne.symm hne] using hq⟩

private theorem mem_flat_split {b : Array (List Find)} {i : Nat} (hi : i < b.size) {q : Find} :
    q ∈ b.toList.flatten ↔ q ∈ b[i] ∨ ∃ j, ∃ h : j < b.size, j ≠ i ∧ q ∈ b[j] := by
  rw [mem_flat]
  constructor
  · rintro ⟨j, h, hq⟩
    by_cases hj : j = i
    · subst hj; exact .inl hq
    · exact .inr ⟨j, h, hj, hq⟩
  · rintro (hq | ⟨j, h, _, hq⟩)
    · exact ⟨i, hi, hq⟩
    · exact ⟨j, h, hq⟩

/-- Popping `g` from a bucket loses nothing else. -/
private theorem mem_flat_pop {b : Array (List Find)} {i : Nat} (hi : i < b.size) {g : Find}
    {more : List Find} (hb : b[i] = g :: more) {q : Find} :
    q ∈ b.toList.flatten ↔ q = g ∨ q ∈ (b.set i more).toList.flatten := by
  rw [mem_flat_split hi, mem_flat_set hi, hb, List.mem_cons, or_assoc]

/-- Pushing `r` onto a bucket in range adds exactly `r`. -/
private theorem mem_flat_push {b : Array (List Find)} {k : Nat} (hk : k < b.size) {r q : Find} :
    q ∈ (b.modify k (r :: ·)).toList.flatten ↔ q = r ∨ q ∈ b.toList.flatten := by
  rw [mem_flat, mem_flat]
  constructor
  · rintro ⟨j, h, hq⟩
    rw [Array.getElem_modify] at hq
    split at hq
    · rcases List.mem_cons.mp hq with rfl | hq
      · exact .inl rfl
      · exact .inr ⟨j, by simpa using h, hq⟩
    · exact .inr ⟨j, by simpa using h, hq⟩
  · rintro (rfl | ⟨j, h, hq⟩)
    · exact ⟨k, by simpa using hk, by rw [Array.getElem_modify]; simp⟩
    · refine ⟨j, by simpa using h, ?_⟩
      rw [Array.getElem_modify]; split <;> simp_all

/-- `coverLoop`'s arguments, for its invariant. `buckets[k]` holds finds remembered with `k`
features, which bounds what each would still add, since `covered` only grows. -/
private structure CoverState where
  covered : Std.HashSet UInt32
  buckets : Array (List Find)
  picked : List Find

/-- The seeds chosen and every find still waiting. -/
private def CoverState.all (s : CoverState) : List Find := s.picked ++ s.buckets.toList.flatten

/-- The loop's invariant, against the finds `l` it started from: what is covered is reached by a
seed (`picked`); every feature of `l` is covered or still held by a waiting find; and every seed or
waiting find is one of `l`, with only features that find reached. -/
private structure Inv (l : List Find) (s : CoverState) : Prop where
  picked : ∀ x, s.covered.contains x → ∃ c ∈ s.picked, x ∈ c.feats
  held : ∀ g ∈ l, ∀ x ∈ g.feats,
    s.covered.contains x ∨ ∃ q ∈ s.buckets.toList.flatten, x ∈ q.feats
  sub : ∀ c ∈ s.all, ∃ g ∈ l, c.bytes = g.bytes ∧ ∀ x ∈ c.feats, x ∈ g.feats

/-- What `cover` promises, of a result `r` for finds `l`. -/
private def Good (l r : List Find) : Prop :=
  (∀ g ∈ l, ∀ x ∈ g.feats, ∃ c ∈ r, x ∈ c.feats) ∧
  (∀ c ∈ r, ∃ g ∈ l, c.bytes = g.bytes ∧ ∀ x ∈ c.feats, x ∈ g.feats)

private theorem good_all {l : List Find} {s : CoverState} (h : Inv l s) : Good l s.all := by
  refine ⟨fun g hg x hx => ?_, h.sub⟩
  rcases h.held g hg x hx with hc | ⟨q, hq, hxq⟩
  · obtain ⟨c, hc, hxc⟩ := h.picked x hc
    exact ⟨c, List.mem_append_left _ hc, hxc⟩
  · exact ⟨q, List.mem_append_right _ hq, hxq⟩

private theorem mem_residual {covered : Std.HashSet UInt32} {g : Find} {x : UInt32} :
    x ∈ (g.residual covered).feats ↔ x ∈ g.feats ∧ covered.contains x = false := by
  simp [Find.residual, Array.mem_filter]

/-- The residual of a waiting find is one of `l` as much as the find was. -/
private theorem sub_residual {l : List Find} {s : CoverState} (h : Inv l s) {g : Find}
    (hg : g ∈ s.buckets.toList.flatten) :
    ∃ g' ∈ l, (g.residual s.covered).bytes = g'.bytes ∧
      ∀ x ∈ (g.residual s.covered).feats, x ∈ g'.feats := by
  obtain ⟨g', hg', hb, hs⟩ := h.sub g (List.mem_append_right _ hg)
  exact ⟨g', hg', hb, fun x hx => hs x (mem_residual.mp hx).1⟩

private theorem good_coverLoop (l : List Find) (n : Nat) :
    ∀ (top : Nat) (covered : Std.HashSet UInt32) (buckets : Array (List Find)) (picked : List Find),
    weight 0 buckets.toList + top = n →
    Inv l ⟨covered, buckets, picked⟩ → Good l (coverLoop top covered buckets picked) := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro top covered buckets picked hn h
  rw [coverLoop]
  split
  · rename_i htop
    split
    · split
      · exact good_all h
      · rename_i hz
        exact ih _ (by omega) _ covered buckets picked rfl h
    · rename_i g more hb
      have pop := fun q => mem_flat_pop htop hb (q := q)
      have hgq : g ∈ buckets.toList.flatten := (pop g).mpr (.inl rfl)
      have hsub := sub_residual h hgq
      -- A feature held by `g` is covered or kept by `g`'s residual.
      have hres : ∀ x ∈ g.feats, covered.contains x ∨ x ∈ (g.residual covered).feats :=
        fun x hx => by
          cases hc : covered.contains x
          · exact .inr (mem_residual.mpr ⟨hx, hc⟩)
          · exact .inl rfl
      split
      · -- Dropped: nothing of it is uncovered.
        rename_i hz
        refine ih _ (by have := weight_pop htop hb; omega) _ _ _ _ rfl ?_
        refine ⟨h.picked, fun g' hg' x hx => ?_, fun c hc => ?_⟩
        · rcases h.held g' hg' x hx with hc | ⟨q, hq, hxq⟩
          · exact .inl hc
          · rcases (pop q).mp hq with rfl | hq
            · rcases hres x hxq with hc | hr
              · exact .inl hc
              · exact absurd (Array.size_pos_of_mem hr) (by omega)
            · exact .inr ⟨q, hq, hxq⟩
        · rcases List.mem_append.mp hc with hc | hc
          · exact h.sub c (List.mem_append_left _ hc)
          · exact h.sub c (List.mem_append_right _ ((pop c).mpr (.inr hc)))
      · split
        · -- Requeued at its new size.
          rename_i _ hlt
          have hk : (g.residual covered).feats.size < (buckets.set top more).size := by
            simp; omega
          have push := fun q => mem_flat_push hk (r := g.residual covered) (q := q)
          refine ih _ (by
              have := weight_pop htop hb
              have := weight_push hk (r := g.residual covered)
              omega) _ _ _ _ rfl ?_
          refine ⟨h.picked, fun g' hg' x hx => ?_, fun c hc => ?_⟩
          · rcases h.held g' hg' x hx with hc | ⟨q, hq, hxq⟩
            · exact .inl hc
            · rcases (pop q).mp hq with rfl | hq
              · rcases hres x hxq with hc | hr
                · exact .inl hc
                · exact .inr ⟨_, (push _).mpr (.inl rfl), hr⟩
              · exact .inr ⟨q, (push q).mpr (.inr hq), hxq⟩
          · rcases List.mem_append.mp hc with hc | hc
            · exact h.sub c (List.mem_append_left _ hc)
            · rcases (push c).mp hc with rfl | hc
              · exact hsub
              · exact h.sub c (List.mem_append_right _ ((pop c).mpr (.inr hc)))
        · -- Taken: its residual joins the picks and the covered set.
          refine ih _ (by have := weight_pop htop hb; omega) _ _ _ _ rfl ?_
          have hcov : ∀ x, (covered.insertMany (g.residual covered).feats.toList).contains x =
              (covered.contains x || (g.residual covered).feats.toList.contains x) :=
            fun _ => Std.HashSet.contains_insertMany_list
          refine ⟨fun x hx => ?_, fun g' hg' x hx => ?_, fun c hc => ?_⟩
          · simp only at hx
            rw [hcov] at hx
            rcases Bool.or_eq_true _ _ ▸ hx with hx | hx
            · obtain ⟨c, hc, hxc⟩ := h.picked x hx
              exact ⟨c, List.mem_cons_of_mem _ hc, hxc⟩
            · exact ⟨_, List.mem_cons_self, by simpa using hx⟩
          · rcases h.held g' hg' x hx with hc | ⟨q, hq, hxq⟩
            · exact .inl (by simp only; rw [hcov, hc]; rfl)
            · rcases (pop q).mp hq with rfl | hq
              · rcases hres x hxq with hc | hr
                · exact .inl (by simp only; rw [hcov, hc]; rfl)
                · exact .inl (by simp only; rw [hcov]; simp [hr])
              · exact .inr ⟨q, hq, hxq⟩
          · simp only [CoverState.all, List.cons_append, List.mem_cons] at hc
            rcases hc with rfl | hc
            · exact hsub
            · rcases List.mem_append.mp hc with hc | hc
              · exact h.sub c (List.mem_append_left _ hc)
              · exact h.sub c (List.mem_append_right _ ((pop c).mpr (.inr hc)))
  · exact good_all h

/-- The initial buckets hold exactly the finds. -/
private theorem mem_flat_init (n : Nat) :
    ∀ (xs : List Find) (b : Array (List Find)), b.size = n + 1 → (∀ g ∈ xs, g.feats.size ≤ n) →
      ∀ q, q ∈ (xs.foldl (fun b g => b.modify g.feats.size (g :: ·)) b).toList.flatten ↔
        q ∈ xs ∨ q ∈ b.toList.flatten
  | [], _, _, _, q => by simp
  | g :: xs, b, hb, hn, q => by
    rw [List.foldl_cons, mem_flat_init n xs _ (by simp [hb]) (fun g' h => hn g' (by simp [h])),
      mem_flat_push (by have := hn g (by simp); omega)]
    simp only [List.mem_cons]
    constructor
    · rintro (h | h | h)
      · exact .inl (.inr h)
      · exact .inl (.inl h)
      · exact .inr h
    · rintro ((h | h) | h)
      · exact .inr (.inl h)
      · exact .inl h
      · exact .inr (.inr h)

private theorem le_foldl_max (l : List Find) :
    ∀ m, ∀ g ∈ l, g.feats.size ≤ l.foldl (fun m g => max m g.feats.size) m := by
  induction l with
  | nil => simp
  | cons g' gs ih =>
    intro m g hg
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hg with rfl | hg
    · have : ∀ m', m' ≤ gs.foldl (fun m g => max m g.feats.size) m' := by
        clear ih hg
        induction gs with
        | nil => simp
        | cons _ _ ih' => intro m'; exact Nat.le_trans (Nat.le_max_left _ _) (ih' _)
      exact Nat.le_trans (Nat.le_max_right _ _) (this _)
    · exact ih _ g hg

private theorem good_cover (l : List Find) : Good l (cover l) := by
  unfold cover
  refine good_coverLoop l _ _ _ _ _ rfl ?_
  have hn := le_foldl_max l 0
  have init := mem_flat_init (l.foldl (fun m g => max m g.feats.size) 0)
    (l.mergeSort (fun a b => decide (a.bytes.size ≥ b.bytes.size)))
    (Array.replicate (l.foldl (fun m g => max m g.feats.size) 0 + 1) []) Array.size_replicate
    (fun g hg => hn g (List.mem_mergeSort.mp hg))
  refine ⟨fun x hx => by simp [Std.HashSet.contains_empty] at hx,
    fun g hg x hx => .inr ⟨g, ?_, hx⟩, fun c hc => ?_⟩
  · exact (init g).mpr (.inl (List.mem_mergeSort.mpr hg))
  · simp only [CoverState.all, List.nil_append] at hc
    rcases (init c).mp hc with hc | hc
    · exact ⟨c, List.mem_mergeSort.mp hc, rfl, fun _ h => h⟩
    · simp at hc

/-- **Coverage.** Every feature of every find is reached by some seed `cover` keeps. -/
theorem cover_covers (l : List Find) : ∀ g ∈ l, ∀ x ∈ g.feats, ∃ c ∈ cover l, x ∈ c.feats :=
  (good_cover l).1

/-- **Soundness.** Every seed `cover` keeps is one of the finds, reaching only features that find
reached. -/
theorem cover_sub (l : List Find) :
    ∀ c ∈ cover l, ∃ g ∈ l, c.bytes = g.bytes ∧ ∀ x ∈ c.feats, x ∈ g.feats :=
  (good_cover l).2

end Basalt.Fuzz
