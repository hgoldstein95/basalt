/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Segev Elazar Mittelman
-/
import Basalt.GradedSound

/-!
# Lazy Levels

`LvL α` is `LvT` with each level a lazy list, forced only as far as it is read, so the first values of a
huge level cost nothing for the rest. Every operation is total and `toList` turns it into the `List`
operation `Lv` uses, so `AgreeL` transports results about `Lv` as `Agree` does.
-/

namespace Basalt

variable {α β : Type}

/-! ## A total lazy list -/

/-- A lazy list: the tail is a thunk, so it is built only when read. -/
inductive LList (α : Type) where
  | nil
  | cons (a : α) (t : Thunk (LList α))

namespace LList

/-- Force the whole list. For proofs; not tail recursive. -/
def toList : LList α → List α
  | nil => []
  | cons a t => a :: toList t.get

/-- The first `n` elements, forcing only those. -/
def take : Nat → LList α → List α
  | 0, _ => []
  | _, nil => []
  | n + 1, cons a t => a :: take n t.get

def single (a : α) : LList α := cons a (Thunk.pure nil)

/-- Append onto a *thunk* of the second list, so it is not built until the first is exhausted. -/
def appendT : LList α → Thunk (LList α) → LList α
  | nil, ys => ys.get
  | cons x xs, ys => cons x ⟨fun _ => appendT xs.get ys⟩

def map (f : α → β) : LList α → LList β
  | nil => nil
  | cons a t => cons (f a) ⟨fun _ => map f t.get⟩

/-- `flatMap`. An empty inner list is skipped by a direct call, not through the tail's thunk: the thunked
form nests one force per empty list and overflowed the stack on a sparse level. -/
def flatMap (f : α → LList β) : LList α → LList β
  | nil => nil
  | cons a t =>
    match f a with
    | nil => flatMap f t.get
    | cons b bs => cons b ⟨fun _ => appendT bs.get ⟨fun _ => flatMap f t.get⟩⟩

/-- `filterMap`, skipping dropped elements by a direct call, as `flatMap` skips empty lists. -/
def filterMap (f : α → Option β) : LList α → LList β
  | nil => nil
  | cons a t =>
    match f a with
    | none => filterMap f t.get
    | some b => cons b ⟨fun _ => filterMap f t.get⟩

/-- `i, i+1, …, i+len-1`. -/
def rangeFrom (i : Nat) : Nat → LList Nat
  | 0 => nil
  | len + 1 => cons i ⟨fun _ => rangeFrom (i + 1) len⟩

/-- `0, …, n-1`. -/
def range (n : Nat) : LList Nat := rangeFrom 0 n

/-! ### `toList` turns each operation into the `List` one -/

@[simp] theorem toList_nil : (nil : LList α).toList = [] := by simp [toList]

@[simp] theorem toList_cons (a : α) (t : Thunk (LList α)) :
    (cons a t).toList = a :: t.get.toList := by simp [toList]

@[simp] theorem toList_single (a : α) : (single a).toList = [a] := by
  simp [single, Thunk.pure, Thunk.get]

@[simp] theorem toList_appendT : ∀ (xs : LList α) (ys : Thunk (LList α)),
    (appendT xs ys).toList = xs.toList ++ ys.get.toList
  | nil, _ => by simp [appendT]
  | cons x xs, ys => by
    simp only [appendT, toList_cons, List.cons_append, Thunk.get]
    exact congrArg (x :: ·) (toList_appendT xs.get ys)

@[simp] theorem toList_map (f : α → β) : ∀ l : LList α, (map f l).toList = l.toList.map f
  | nil => by simp [map]
  | cons a t => by
    simp only [map, toList_cons, List.map_cons, Thunk.get]
    exact congrArg (f a :: ·) (toList_map f t.get)

@[simp] theorem toList_flatMap (f : α → LList β) :
    ∀ l : LList α, (flatMap f l).toList = l.toList.flatMap fun a => (f a).toList
  | nil => by simp [flatMap]
  | cons a t => by
    simp only [flatMap, toList_cons, List.flatMap_cons]
    split
    · next h => rw [h, toList_nil, List.nil_append]; exact toList_flatMap f t.get
    · next b bs h =>
      rw [h, toList_cons, toList_cons, Thunk.get, toList_appendT, Thunk.get, List.cons_append]
      exact congrArg (fun r => b :: (bs.get.toList ++ r)) (toList_flatMap f t.get)

@[simp] theorem toList_filterMap (f : α → Option β) :
    ∀ l : LList α, (filterMap f l).toList = l.toList.filterMap f
  | nil => by simp [filterMap]
  | cons a t => by
    simp only [filterMap, toList_cons, List.filterMap_cons]
    split
    · next h => rw [h]; exact toList_filterMap f t.get
    · next b h => rw [h, toList_cons, Thunk.get]; exact congrArg (b :: ·) (toList_filterMap f t.get)

theorem toList_rangeFrom : ∀ (i len : Nat), (rangeFrom i len).toList = List.range' i len
  | _, 0 => by simp [rangeFrom]
  | i, len + 1 => by
    simp only [rangeFrom, toList_cons, List.range'_succ, Thunk.get]
    exact congrArg (i :: ·) (toList_rangeFrom (i + 1) len)

@[simp] theorem toList_range (n : Nat) : (range n).toList = List.range n := by
  rw [range, toList_rangeFrom, List.range_eq_range']

/-- `take` reads a prefix of what `toList` would force: the lazy read is faithful. -/
theorem take_eq : ∀ (n : Nat) (l : LList α), l.take n = l.toList.take n
  | 0, _ => by simp [take]
  | _ + 1, nil => by simp [take]
  | n + 1, cons a t => by
    simp only [take, toList_cons, List.take_succ_cons]
    exact congrArg (a :: ·) (take_eq n t.get)

end LList

/-! ## The carrier -/

/-- Levels `0..N`, each a thunk of a lazy list. -/
abbrev LvL (α : Type) := Array (Thunk (LList α))

/-- Read one level, lazily. Past the end this is `nil`. -/
def LvL.get (x : LvL α) (n : Nat) : LList α :=
  if h : n < x.size then (x[n]'h).get else .nil

/-- The forced level matches `m` on every level the array covers. The lazy analogue of `Agree`. -/
def AgreeL (x : LvL α) (m : Lv α) : Prop := ∀ n, n < x.size → (x.get n).toList = m n

/-- Built through a `List`, for the same axiom reason as `LvT.build`. -/
def LvL.build (N : Nat) (f : Nat → Thunk (LList α)) : LvL α := ((List.range N).map f).toArray

def LvL.nothing (N : Nat) : LvL α := LvL.build (N + 1) fun _ => Thunk.mk fun _ => .nil

def LvL.single (N : Nat) (a : α) : LvL α :=
  LvL.build (N + 1) fun n => Thunk.mk fun _ => if n = 0 then LList.single a else .nil

def LvL.union (x y : LvL α) : LvL α :=
  LvL.build x.size fun n => Thunk.mk fun _ => (x.get n).appendT ⟨fun _ => y.get n⟩

def LvL.pay (x : LvL α) : LvL α :=
  LvL.build x.size fun n => Thunk.mk fun _ => if n = 0 then .nil else x.get (n - 1)

def LvL.gmap (g : α → β) (x : LvL α) : LvL β :=
  LvL.build x.size fun n => Thunk.mk fun _ => (x.get n).map g

def LvL.pair (x : LvL α) (y : LvL β) : LvL (α × β) :=
  LvL.build x.size fun n => Thunk.mk fun _ =>
    (LList.range (n + 1)).flatMap fun i => (x.get i).flatMap fun a => (y.get (n - i)).map (a, ·)

def LvL.bindC (x : LvL α) (k : α → LvL β) : LvL β :=
  LvL.build x.size fun n => Thunk.mk fun _ =>
    (LList.range (n + 1)).flatMap fun i => (x.get i).flatMap fun a => (k a).get (n - i)

def LvL.guard (p : α → V) (x : LvL α) : LvL (α × Bool) :=
  LvL.build x.size fun n => Thunk.mk fun _ =>
    (x.get n).filterMap fun a =>
      match p a with
      | .yes => some (a, true)
      | .inconclusive => some (a, false)
      | .no => none

/-! ## Sizes -/

@[simp] theorem LvL.size_build (N : Nat) (f : Nat → Thunk (LList α)) :
    (LvL.build N f).size = N := by simp [LvL.build]

@[simp] theorem LvL.size_nothing (N : Nat) : (LvL.nothing N : LvL α).size = N + 1 := by
  simp [LvL.nothing]

@[simp] theorem LvL.size_single (N : Nat) (a : α) : (LvL.single N a).size = N + 1 := by
  simp [LvL.single]

@[simp] theorem LvL.size_union (x y : LvL α) : (LvL.union x y).size = x.size := by
  simp [LvL.union]

@[simp] theorem LvL.size_pay (x : LvL α) : (LvL.pay x).size = x.size := by simp [LvL.pay]

@[simp] theorem LvL.size_gmap (g : α → β) (x : LvL α) : (LvL.gmap g x).size = x.size := by
  simp [LvL.gmap]

@[simp] theorem LvL.size_pair (x : LvL α) (y : LvL β) : (LvL.pair x y).size = x.size := by
  simp [LvL.pair]

@[simp] theorem LvL.size_bindC (x : LvL α) (k : α → LvL β) : (LvL.bindC x k).size = x.size := by
  simp [LvL.bindC]

@[simp] theorem LvL.size_guard (p : α → V) (x : LvL α) : (LvL.guard p x).size = x.size := by
  simp [LvL.guard]

theorem LvL.get_build {f : Nat → Thunk (LList α)} {N n : Nat} (h : n < N) :
    LvL.get (LvL.build N f) n = (f n).get := by
  simp only [LvL.get, LvL.build, List.size_toArray, List.length_map, List.length_range, dite_eq_left h,
    List.getElem_toArray, List.getElem_map, List.getElem_range]

/-- `flatMap` depends only on the function's values on the list. -/
theorem flatMap_congr' {l : List α} {f g : α → List β} (h : ∀ a ∈ l, f a = g a) :
    l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.flatMap_cons]
    rw [h a (List.mem_cons_self ..), ih fun b hb => h b (List.mem_cons_of_mem _ hb)]

/-! ## Agreement, preserved by every operation -/

theorem agreeL_nothing (N : Nat) : AgreeL (LvL.nothing N : LvL α) Choice.nothing := by
  intro n hn
  simp only [LvL.size_nothing] at hn
  rw [LvL.nothing, LvL.get_build hn]
  simp only [Thunk.get, LList.toList_nil]
  rfl

theorem agreeL_single (N : Nat) (a : α) : AgreeL (LvL.single N a) (Graded.single a) := by
  intro n hn
  simp only [LvL.size_single] at hn
  rw [LvL.single, LvL.get_build hn]
  by_cases h : n = 0 <;> simp [h, Thunk.get, Graded.single]

theorem AgreeL.union {x y : LvL α} {m p : Lv α} (hx : AgreeL x m) (hy : AgreeL y p)
    (hsz : y.size = x.size) : AgreeL (LvL.union x y) (Choice.union m p) := by
  intro n hn
  rw [LvL.size_union] at hn
  rw [LvL.union, LvL.get_build hn]
  simp only [Thunk.get, LList.toList_appendT]
  rw [hx n hn, hy n (by rw [hsz]; exact hn)]
  rfl

theorem AgreeL.pay {x : LvL α} {m : Lv α} (hx : AgreeL x m) :
    AgreeL (LvL.pay x) (Graded.pay m) := by
  intro n hn
  rw [LvL.size_pay] at hn
  rw [LvL.pay, LvL.get_build hn]
  simp only [Thunk.get]
  cases n with
  | zero => rw [ite_eq_left rfl, LList.toList_nil]; rfl
  | succ n => simpa [Graded.pay] using hx n (by omega)

theorem AgreeL.gmap {x : LvL α} {m : Lv α} (g : α → β) (hx : AgreeL x m) :
    AgreeL (LvL.gmap g x) (Graded.gmap g m) := by
  intro n hn
  rw [LvL.size_gmap] at hn
  rw [LvL.gmap, LvL.get_build hn]
  simp only [Thunk.get, LList.toList_map]
  rw [hx n hn]
  rfl

theorem AgreeL.pair {x : LvL α} {m : Lv α} {y : LvL β} {p : Lv β}
    (hx : AgreeL x m) (hy : AgreeL y p) (hsz : y.size = x.size) :
    AgreeL (LvL.pair x y) (Graded.pair m p) := by
  intro n hn
  rw [LvL.size_pair] at hn
  rw [LvL.pair, LvL.get_build hn]
  simp only [Thunk.get, LList.toList_flatMap, LList.toList_range, LList.toList_map]
  refine flatMap_congr' fun i hi => ?_
  rw [List.mem_range] at hi
  rw [hx i (by omega), hy (n - i) (by rw [hsz]; omega)]

theorem AgreeL.bindC {x : LvL α} {m : Lv α} {k : α → LvL β} {h : α → Lv β}
    (hx : AgreeL x m) (hk : ∀ a, AgreeL (k a) (h a)) (hsz : ∀ a, (k a).size = x.size) :
    AgreeL (LvL.bindC x k) (GradedBind.bindC m h) := by
  intro n hn
  rw [LvL.size_bindC] at hn
  rw [LvL.bindC, LvL.get_build hn]
  simp only [Thunk.get, LList.toList_flatMap, LList.toList_range]
  refine flatMap_congr' fun i hi => ?_
  rw [List.mem_range] at hi
  rw [hx i (by omega)]
  exact flatMap_congr' fun a _ => hk a (n - i) (by rw [hsz a]; omega)

theorem AgreeL.guard {x : LvL α} {m : Lv α} (p : α → V) (hx : AgreeL x m) :
    AgreeL (LvL.guard p x) (GradedBind.guard p m) := by
  intro n hn
  rw [LvL.size_guard] at hn
  rw [LvL.guard, LvL.get_build hn]
  simp only [Thunk.get, LList.toList_filterMap]
  rw [hx n hn]
  rfl

/-- The `if` a rule's input-decidable side condition compiles to. -/
theorem AgreeL.ite {c : Prop} [Decidable c] {x y : LvL α} {m p : Lv α}
    (hx : AgreeL x m) (hy : AgreeL y p) : AgreeL (if c then x else y) (if c then m else p) := by
  by_cases h : c <;> simp [h, hx, hy]

/-! ## Transport -/

/-- Membership in a forced lazy level matches the specification, level by level, within budget. -/
theorem mem_toList_iff_of_agrees {x : LvL α} {m : Lv α} {s : SetE α}
    (hx : AgreeL x m) (hm : Agrees m s) (n : Nat) (hn : n < x.size) (a : α) :
    a ∈ (x.get n).toList ↔ s n a := by
  rw [hx n hn]; exact hm n a

/-- **What a lazy read returns is sound**: every term in the first `k` of a level is in the
specification at that level. Reading lazily loses nothing but the terms not yet read. -/
theorem mem_take_sound {x : LvL α} {m : Lv α} {s : SetE α}
    (hx : AgreeL x m) (hm : Agrees m s) (n k : Nat) (hn : n < x.size) {a : α}
    (ha : a ∈ (x.get n).take k) : s n a := by
  rw [LList.take_eq] at ha
  exact (mem_toList_iff_of_agrees hx hm n hn a).1 (List.mem_of_mem_take ha)

theorem length_toList_eq_of_counts {x : LvL α} {m : Lv α} {c : Cnt α}
    (hx : AgreeL x m) (hm : Counts m c) (n : Nat) (hn : n < x.size) :
    (x.get n).toList.length = c n := by
  rw [hx n hn]; exact hm n

end Basalt
