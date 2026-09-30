/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Segev Elazar Mittelman
-/
import Basalt.GradedLazy

/-!
# Chunked Levels

`LvC α` stores each level as a lazy list of strict chunks of at least `C` elements, merged by `coalesce C`:
a level smaller than a chunk is one strict list, and a huge one is built a chunk ahead of the reader. A
level means its flattening, and `AgreeC` transports results about `Lv` as `Agree` and `AgreeL` do.
-/

namespace Basalt

variable {α β : Type}

/-- A chunk size for callers to pass. It is an argument of every operation that merges, not a global. -/
def defaultChunk : Nat := 256

/-! ## Chunk-level list operations -/

namespace LList

/-- Merge consecutive chunks until each holds at least `c` elements; drop an empty remainder. -/
def coalesce (c : Nat) : LList (List α) → LList (List α) := go [] 0
where
  /-- `accRev` holds the chunks gathered so far, newest first, so each merge step is a cons; `len` is a
      running count of their elements, so deciding when to emit is `O(1)`. Correctness does not depend
      on `len` being accurate — only when chunks are emitted does. -/
  go (accRev : List (List α)) (len : Nat) : LList (List α) → LList (List α)
    | nil =>
      let out := accRev.reverse.flatten
      if out.isEmpty then nil else cons out (Thunk.pure nil)
    | cons xs t =>
      if c ≤ len + xs.length then
        cons (xs :: accRev).reverse.flatten ⟨fun _ => go [] 0 t.get⟩
      else go (xs :: accRev) (len + xs.length) t.get

theorem toList_flatten_coalesce_go (c : Nat) :
    ∀ (l : LList (List α)) (accRev : List (List α)) (len : Nat),
      (coalesce.go c accRev len l).toList.flatten = accRev.reverse.flatten ++ l.toList.flatten
  | nil, accRev, _ => by
    simp only [coalesce.go, toList_nil, List.flatten_nil, List.append_nil]
    split
    · next h => simp only [toList_nil, List.flatten_nil]; exact (List.isEmpty_iff.mp h).symm
    · simp [Thunk.pure, Thunk.get]
  | cons xs t, accRev, len => by
    simp only [coalesce.go, toList_cons, List.flatten_cons]
    split
    · rw [toList_cons, Thunk.get, List.flatten_cons, toList_flatten_coalesce_go c t.get [] 0]
      simp [List.reverse_cons, List.flatten_append, List.append_assoc]
    · rw [toList_flatten_coalesce_go c t.get (xs :: accRev) (len + xs.length)]
      simp [List.reverse_cons, List.flatten_append, List.append_assoc]

/-- **Merging chunks does not change what a level means.** -/
@[simp] theorem toList_flatten_coalesce (c : Nat) (l : LList (List α)) :
    (coalesce c l).toList.flatten = l.toList.flatten := by
  show (coalesce.go c [] 0 l).toList.flatten = _
  simpa using toList_flatten_coalesce_go c l [] 0

/-- `flatMap` from a plain list into a lazy list, skipping an empty result by a direct call (the
    `GradedLazy` rule: going through a thunk nests one `Thunk.get` per empty result). -/
def flatMapList (f : α → LList β) : List α → LList β
  | [] => nil
  | a :: as =>
    match f a with
    | nil => flatMapList f as
    | cons b bs => cons b ⟨fun _ => appendT bs.get ⟨fun _ => flatMapList f as⟩⟩

@[simp] theorem toList_flatMapList (f : α → LList β) :
    ∀ l : List α, (flatMapList f l).toList = l.flatMap fun a => (f a).toList
  | [] => by simp [flatMapList]
  | a :: as => by
    simp only [flatMapList, List.flatMap_cons]
    split
    · next h => rw [h, toList_nil, List.nil_append]; exact toList_flatMapList f as
    · next b bs h =>
      rw [h, toList_cons, toList_cons, Thunk.get, toList_appendT, Thunk.get, List.cons_append]
      exact congrArg (fun r => b :: (bs.get.toList ++ r)) (toList_flatMapList f as)

/-- Every element of every chunk fed to `f`, results concatenated lazily. -/
def chunkFlatMap (f : α → LList (List β)) (l : LList (List α)) : LList (List β) :=
  l.flatMap (flatMapList f)

theorem flatten_flatMap' (l : List α) (f : α → List (List β)) :
    (l.flatMap f).flatten = l.flatMap fun a => (f a).flatten := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.flatMap_cons, List.flatten_append, ih]

@[simp] theorem toList_flatten_chunkFlatMap (f : α → LList (List β)) (l : LList (List α)) :
    (chunkFlatMap f l).toList.flatten = l.toList.flatten.flatMap fun a => (f a).toList.flatten := by
  rw [chunkFlatMap, toList_flatMap, flatten_flatMap']
  simp only [toList_flatMapList, flatten_flatMap']
  induction l.toList with
  | nil => rfl
  | cons xs L ih => simp [List.flatMap_cons, List.flatten_cons, List.flatMap_append, ih]

/-- The first `k` elements of the flattening, reading whole chunks and stopping as soon as `k` are in
    hand. -/
def takeC : Nat → LList (List α) → List α
  | 0, _ => []
  | _ + 1, nil => []
  | k + 1, cons xs t =>
    if k + 1 ≤ xs.length then xs.take (k + 1) else xs ++ takeC (k + 1 - xs.length) t.get

/-- `takeC` is exactly a prefix of the flattening. -/
theorem takeC_eq : ∀ (k : Nat) (l : LList (List α)), takeC k l = l.toList.flatten.take k
  | 0, _ => by simp [takeC]
  | _ + 1, nil => by simp [takeC]
  | k + 1, cons xs t => by
    simp only [takeC, toList_cons, List.flatten_cons]
    split
    · next h => rw [List.take_append_of_le_length h]
    · next h =>
      rw [List.take_append, List.take_of_length_le (by omega), takeC_eq]

end LList

/-! ## The carrier -/

/-- Levels `0..N`, each a thunk of a lazy list of strict chunks. -/
abbrev LvC (α : Type) := Array (Thunk (LList (List α)))

/-- Read one level's chunks, lazily. Past the end this is `nil`. -/
def LvC.get (x : LvC α) (n : Nat) : LList (List α) :=
  if h : n < x.size then (x[n]'h).get else .nil

/-- What a level means: its chunks, flattened. For proofs; running code reads with `takeC`. -/
def LvC.flat (x : LvC α) (n : Nat) : List α := (x.get n).toList.flatten

/-- Every stored level flattens to `m`'s. The chunked analogue of `Agree`/`AgreeL`. -/
def AgreeC (x : LvC α) (m : Lv α) : Prop := ∀ n, n < x.size → x.flat n = m n

/-- Built through a `List`, for the same axiom reason as `LvT.build`. -/
def LvC.build (N : Nat) (f : Nat → Thunk (LList (List α))) : LvC α := ((List.range N).map f).toArray

def LvC.nothing (N : Nat) : LvC α := LvC.build (N + 1) fun _ => Thunk.mk fun _ => .nil

def LvC.single (N : Nat) (a : α) : LvC α :=
  LvC.build (N + 1) fun n => Thunk.mk fun _ => if n = 0 then LList.single [a] else .nil

def LvC.union (C : Nat) (x y : LvC α) : LvC α :=
  LvC.build x.size fun n => Thunk.mk fun _ =>
    LList.coalesce C ((x.get n).appendT ⟨fun _ => y.get n⟩)

def LvC.pay (x : LvC α) : LvC α :=
  LvC.build x.size fun n => Thunk.mk fun _ => if n = 0 then .nil else x.get (n - 1)

def LvC.gmap (g : α → β) (x : LvC α) : LvC β :=
  LvC.build x.size fun n => Thunk.mk fun _ => (x.get n).map (List.map g)

/-- For each `a` in `x`'s level `i`, one chunk per chunk of `y`'s level `n - i`, each built with a strict
    `List.map`; then coalesced. -/
def LvC.pair (C : Nat) (x : LvC α) (y : LvC β) : LvC (α × β) :=
  LvC.build x.size fun n => Thunk.mk fun _ =>
    LList.coalesce C <| (LList.range (n + 1)).flatMap fun i =>
      LList.chunkFlatMap (fun a => (y.get (n - i)).map (List.map (a, ·))) (x.get i)

def LvC.bindC (C : Nat) (x : LvC α) (k : α → LvC β) : LvC β :=
  LvC.build x.size fun n => Thunk.mk fun _ =>
    LList.coalesce C <| (LList.range (n + 1)).flatMap fun i =>
      LList.chunkFlatMap (fun a => (k a).get (n - i)) (x.get i)

/-- Filtering can shrink chunks, so the result is coalesced again. -/
def LvC.guard (C : Nat) (p : α → V) (x : LvC α) : LvC (α × Bool) :=
  LvC.build x.size fun n => Thunk.mk fun _ =>
    LList.coalesce C <| (x.get n).map fun xs => xs.filterMap fun a =>
      match p a with
      | .yes => some (a, true)
      | .inconclusive => some (a, false)
      | .no => none

/-! ## Sizes -/

@[simp] theorem LvC.size_build (N : Nat) (f : Nat → Thunk (LList (List α))) :
    (LvC.build N f).size = N := by simp [LvC.build]

@[simp] theorem LvC.size_nothing (N : Nat) : (LvC.nothing N : LvC α).size = N + 1 := by
  simp [LvC.nothing]

@[simp] theorem LvC.size_single (N : Nat) (a : α) : (LvC.single N a).size = N + 1 := by
  simp [LvC.single]

@[simp] theorem LvC.size_union (C : Nat) (x y : LvC α) : (LvC.union C x y).size = x.size := by
  simp [LvC.union]

@[simp] theorem LvC.size_pay (x : LvC α) : (LvC.pay x).size = x.size := by simp [LvC.pay]

@[simp] theorem LvC.size_gmap (g : α → β) (x : LvC α) : (LvC.gmap g x).size = x.size := by
  simp [LvC.gmap]

@[simp] theorem LvC.size_pair (C : Nat) (x : LvC α) (y : LvC β) : (LvC.pair C x y).size = x.size := by
  simp [LvC.pair]

@[simp] theorem LvC.size_bindC (C : Nat) (x : LvC α) (k : α → LvC β) :
    (LvC.bindC C x k).size = x.size := by
  simp [LvC.bindC]

@[simp] theorem LvC.size_guard (C : Nat) (p : α → V) (x : LvC α) :
    (LvC.guard C p x).size = x.size := by
  simp [LvC.guard]

theorem LvC.get_build {f : Nat → Thunk (LList (List α))} {N n : Nat} (h : n < N) :
    LvC.get (LvC.build N f) n = (f n).get := by
  simp only [LvC.get, LvC.build, List.size_toArray, List.length_map, List.length_range, dite_eq_left h,
    List.getElem_toArray, List.getElem_map, List.getElem_range]

theorem LvC.flat_build {f : Nat → Thunk (LList (List α))} {N n : Nat} (h : n < N) :
    LvC.flat (LvC.build N f) n = (f n).get.toList.flatten := by
  rw [LvC.flat, LvC.get_build h]

/-! ## Agreement, preserved by every operation -/

theorem agreeC_nothing (N : Nat) : AgreeC (LvC.nothing N : LvC α) Choice.nothing := by
  intro n hn
  simp only [LvC.size_nothing] at hn
  rw [LvC.nothing, LvC.flat_build hn]
  simp only [Thunk.get, LList.toList_nil, List.flatten_nil]
  rfl

theorem agreeC_single (N : Nat) (a : α) : AgreeC (LvC.single N a) (Graded.single a) := by
  intro n hn
  simp only [LvC.size_single] at hn
  rw [LvC.single, LvC.flat_build hn]
  by_cases h : n = 0 <;> simp [h, Thunk.get, Graded.single]

theorem AgreeC.union {C : Nat} {x y : LvC α} {m p : Lv α} (hx : AgreeC x m) (hy : AgreeC y p)
    (hsz : y.size = x.size) : AgreeC (LvC.union C x y) (Choice.union m p) := by
  intro n hn
  rw [LvC.size_union] at hn
  rw [LvC.union, LvC.flat_build hn]
  simp only [Thunk.get, LList.toList_flatten_coalesce, LList.toList_appendT, List.flatten_append]
  rw [← LvC.flat, ← LvC.flat, hx n hn, hy n (by rw [hsz]; exact hn)]
  rfl

theorem AgreeC.pay {x : LvC α} {m : Lv α} (hx : AgreeC x m) :
    AgreeC (LvC.pay x) (Graded.pay m) := by
  intro n hn
  rw [LvC.size_pay] at hn
  rw [LvC.pay, LvC.flat_build hn]
  simp only [Thunk.get]
  cases n with
  | zero => rw [ite_eq_left rfl, LList.toList_nil, List.flatten_nil]; rfl
  | succ n => simpa [Graded.pay, LvC.flat] using hx n (by omega)

theorem AgreeC.gmap {x : LvC α} {m : Lv α} (g : α → β) (hx : AgreeC x m) :
    AgreeC (LvC.gmap g x) (Graded.gmap g m) := by
  intro n hn
  rw [LvC.size_gmap] at hn
  rw [LvC.gmap, LvC.flat_build hn]
  simp only [Thunk.get, LList.toList_map, ← List.map_flatten]
  rw [← LvC.flat, hx n hn]
  rfl

theorem AgreeC.pair {C : Nat} {x : LvC α} {m : Lv α} {y : LvC β} {p : Lv β}
    (hx : AgreeC x m) (hy : AgreeC y p) (hsz : y.size = x.size) :
    AgreeC (LvC.pair C x y) (Graded.pair m p) := by
  intro n hn
  rw [LvC.size_pair] at hn
  rw [LvC.pair, LvC.flat_build hn]
  simp only [Thunk.get, LList.toList_flatten_coalesce, LList.toList_flatMap, LList.toList_range,
    LList.flatten_flatMap', LList.toList_flatten_chunkFlatMap, LList.toList_map, ← List.map_flatten]
  refine flatMap_congr' fun i hi => ?_
  rw [List.mem_range] at hi
  have ex : (x.get i).toList.flatten = m i := hx i (by omega)
  have ey : y.flat (n - i) = p (n - i) := hy (n - i) (by rw [hsz]; omega)
  rw [ex, show (y.get (n - i)).toList.flatten = p (n - i) from ey]

theorem AgreeC.bindC {C : Nat} {x : LvC α} {m : Lv α} {k : α → LvC β} {h : α → Lv β}
    (hx : AgreeC x m) (hk : ∀ a, AgreeC (k a) (h a)) (hsz : ∀ a, (k a).size = x.size) :
    AgreeC (LvC.bindC C x k) (GradedBind.bindC m h) := by
  intro n hn
  rw [LvC.size_bindC] at hn
  rw [LvC.bindC, LvC.flat_build hn]
  simp only [Thunk.get, LList.toList_flatten_coalesce, LList.toList_flatMap, LList.toList_range,
    LList.flatten_flatMap', LList.toList_flatten_chunkFlatMap]
  refine flatMap_congr' fun i hi => ?_
  rw [List.mem_range] at hi
  have ex : (x.get i).toList.flatten = m i := hx i (by omega)
  rw [ex]
  exact flatMap_congr' fun a _ => hk a (n - i) (by rw [hsz a]; omega)

theorem filterMap_flatten' (f : α → Option β) (L : List (List α)) :
    (L.map (List.filterMap f)).flatten = L.flatten.filterMap f := by
  induction L with
  | nil => rfl
  | cons xs L ih => simp only [List.map_cons, List.flatten_cons, List.filterMap_append, ih]

theorem AgreeC.guard {C : Nat} {x : LvC α} {m : Lv α} (p : α → V) (hx : AgreeC x m) :
    AgreeC (LvC.guard C p x) (GradedBind.guard p m) := by
  intro n hn
  rw [LvC.size_guard] at hn
  rw [LvC.guard, LvC.flat_build hn]
  show (LList.coalesce C _).toList.flatten = _
  rw [LList.toList_flatten_coalesce, LList.toList_map, filterMap_flatten']
  have ex : (x.get n).toList.flatten = m n := hx n hn
  rw [ex]
  rfl

/-- The `if` a rule's input-decidable side condition compiles to. -/
theorem AgreeC.ite {c : Prop} [Decidable c] {x y : LvC α} {m p : Lv α}
    (hx : AgreeC x m) (hy : AgreeC y p) : AgreeC (if c then x else y) (if c then m else p) := by
  by_cases h : c <;> simp [h, hx, hy]

/-! ## Transport -/

/-- Membership in a flattened chunked level matches the specification, level by level, within budget. -/
theorem mem_flat_iff_of_agrees {x : LvC α} {m : Lv α} {s : SetE α}
    (hx : AgreeC x m) (hm : Agrees m s) (n : Nat) (hn : n < x.size) (a : α) :
    a ∈ x.flat n ↔ s n a := by
  rw [hx n hn]; exact hm n a

/-- **What a chunked read returns is sound**: every term among the first `k` read from a level is in the
specification at that level, and only whole chunks up to the `k`-th element were forced. -/
theorem mem_takeC_sound {x : LvC α} {m : Lv α} {s : SetE α}
    (hx : AgreeC x m) (hm : Agrees m s) (n k : Nat) (hn : n < x.size) {a : α}
    (ha : a ∈ LList.takeC k (x.get n)) : s n a := by
  rw [LList.takeC_eq] at ha
  exact (mem_flat_iff_of_agrees hx hm n hn a).1 (List.mem_of_mem_take ha)

theorem length_flat_eq_of_counts {x : LvC α} {m : Lv α} {c : Cnt α}
    (hx : AgreeC x m) (hm : Counts m c) (n : Nat) (hn : n < x.size) :
    (x.flat n).length = c n := by
  rw [hx n hn]; exact hm n

end Basalt
