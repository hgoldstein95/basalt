/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Segev Elazar Mittelman
-/
import Basalt.GradedSound

/-!
# Graded Enumeration to Run

`LvT α` stores levels `0..N` as an array of thunks, so each level is computed once and only when read;
`Lv`, a function, recomputes every level it is asked for. `Agree x m` says `x` matches `m` on the levels
it stores, and every operation preserves it, so a result about `Lv` transports to what runs.
-/

universe u

namespace Basalt

variable {α β : Type}

/-! ## The carrier -/

/-- Levels `0..N` as an array of memoised thunks. -/
abbrev LvT (α : Type) := Array (Thunk (List α))

/-- Read one level. Past the end this is `[]`: the carrier claims only the levels it stores. -/
def LvT.get (x : LvT α) (n : Nat) : List α :=
  if h : n < x.size then (x[n]'h).get else []

/-- View the executable carrier as the carrier the theorems are about. -/
def LvT.toLv (x : LvT α) : Lv α := fun n => x.get n

/-- The view matches `m` on every level stored. Bounded because past the end the two differ: `LvT.get`
is `[]` there, while `Lv` keeps going. -/
def Agree (x : LvT α) (m : Lv α) : Prop := ∀ n, n < x.size → x.get n = m n

/-! ## Operations

Each mirrors the corresponding `Lv` instance, level by level, and preserves the number of levels. -/

/-- Build levels `0..N-1` from a per-level thunk.

Do not build the array with `Array.range`/`Array.ofFn`: their indexing lemmas are classical, and every
agreement proof then silently depends on `Classical.choice` (pinned by `BasaltTest/Graded.lean`). -/
def LvT.build (N : Nat) (f : Nat → Thunk (List α)) : LvT α := ((List.range N).map f).toArray

def LvT.nothing (N : Nat) : LvT α := LvT.build (N + 1) fun _ => Thunk.mk fun _ => []

def LvT.single (N : Nat) (a : α) : LvT α :=
  LvT.build (N + 1) fun n => Thunk.mk fun _ => if n = 0 then [a] else []

def LvT.union (x y : LvT α) : LvT α :=
  LvT.build x.size fun n => Thunk.mk fun _ => x.get n ++ y.get n

def LvT.pay (x : LvT α) : LvT α :=
  LvT.build x.size fun n => Thunk.mk fun _ => if n = 0 then [] else x.get (n - 1)

def LvT.gmap (g : α → β) (x : LvT α) : LvT β :=
  LvT.build x.size fun n => Thunk.mk fun _ => (x.get n).map g

def LvT.pair (x : LvT α) (y : LvT β) : LvT (α × β) :=
  LvT.build x.size fun n => Thunk.mk fun _ =>
    (List.range (n + 1)).flatMap fun i => (x.get i).flatMap fun a => (y.get (n - i)).map (a, ·)

/-- Convolving dependent sequencing — the variant an auxiliary output needs. -/
def LvT.bindC (x : LvT α) (k : α → LvT β) : LvT β :=
  LvT.build x.size fun n => Thunk.mk fun _ =>
    (List.range (n + 1)).flatMap fun i => (x.get i).flatMap fun a => (k a).get (n - i)

/-- Level-preserving dependent sequencing. -/
def LvT.bind (x : LvT α) (k : α → LvT β) : LvT β :=
  LvT.build x.size fun n => Thunk.mk fun _ => (x.get n).flatMap fun a => (k a).get n

/-- A checked premise. `.no` drops; `.inconclusive` is kept flagged `false`. -/
def LvT.guard (p : α → V) (x : LvT α) : LvT (α × Bool) :=
  LvT.build x.size fun n => Thunk.mk fun _ =>
    (x.get n).filterMap fun a =>
      match p a with
      | .yes => some (a, true)
      | .inconclusive => some (a, false)
      | .no => none

/-! ## Sizes -/

@[simp] theorem LvT.size_build (N : Nat) (f : Nat → Thunk (List α)) :
    (LvT.build N f).size = N := by simp [LvT.build]

@[simp] theorem LvT.size_nothing (N : Nat) : (LvT.nothing N : LvT α).size = N + 1 := by
  simp [LvT.nothing]

@[simp] theorem LvT.size_single (N : Nat) (a : α) : (LvT.single N a).size = N + 1 := by
  simp [LvT.single]

@[simp] theorem LvT.size_union (x y : LvT α) : (LvT.union x y).size = x.size := by
  simp [LvT.union]

@[simp] theorem LvT.size_pay (x : LvT α) : (LvT.pay x).size = x.size := by
  simp [LvT.pay]

@[simp] theorem LvT.size_gmap (g : α → β) (x : LvT α) : (LvT.gmap g x).size = x.size := by
  simp [LvT.gmap]

@[simp] theorem LvT.size_pair (x : LvT α) (y : LvT β) : (LvT.pair x y).size = x.size := by
  simp [LvT.pair]

@[simp] theorem LvT.size_bindC (x : LvT α) (k : α → LvT β) : (LvT.bindC x k).size = x.size := by
  simp [LvT.bindC]

@[simp] theorem LvT.size_bind (x : LvT α) (k : α → LvT β) : (LvT.bind x k).size = x.size := by
  simp [LvT.bind]

@[simp] theorem LvT.size_guard (p : α → V) (x : LvT α) : (LvT.guard p x).size = x.size := by
  simp [LvT.guard]

/-! ## Reading a level -/

theorem LvT.get_build {f : Nat → Thunk (List α)} {N n : Nat} (h : n < N) :
    LvT.get (LvT.build N f) n = (f n).get := by
  simp only [LvT.get, LvT.build, List.size_toArray, List.length_map, List.length_range, dite_eq_left h,
    List.getElem_toArray, List.getElem_map, List.getElem_range]

/-! ## Agreement, preserved by every operation -/

theorem agree_nothing (N : Nat) : Agree (LvT.nothing N : LvT α) Choice.nothing := by
  intro n hn
  simp only [LvT.size_nothing] at hn
  rw [LvT.nothing, LvT.get_build hn]
  rfl

theorem agree_single (N : Nat) (a : α) : Agree (LvT.single N a) (Graded.single a) := by
  intro n hn
  simp only [LvT.size_single] at hn
  rw [LvT.single, LvT.get_build hn]
  by_cases h : n = 0 <;> simp [h, Thunk.get]

theorem Agree.union {x y : LvT α} {m p : Lv α} (hx : Agree x m) (hy : Agree y p)
    (hsz : y.size = x.size) : Agree (LvT.union x y) (Choice.union m p) := by
  intro n hn
  rw [LvT.size_union] at hn
  rw [LvT.union, LvT.get_build hn]
  simp only [Thunk.get]
  rw [hx n hn, hy n (by rw [hsz]; exact hn)]
  rfl

theorem Agree.pay {x : LvT α} {m : Lv α} (hx : Agree x m) :
    Agree (LvT.pay x) (Graded.pay m) := by
  intro n hn
  rw [LvT.size_pay] at hn
  rw [LvT.pay, LvT.get_build hn]
  simp only [Thunk.get]
  cases n with
  | zero => simp
  | succ n => simpa using hx n (by omega)

theorem Agree.gmap {x : LvT α} {m : Lv α} (g : α → β) (hx : Agree x m) :
    Agree (LvT.gmap g x) (Graded.gmap g m) := by
  intro n hn
  rw [LvT.size_gmap] at hn
  rw [LvT.gmap, LvT.get_build hn]
  simp only [Thunk.get]
  rw [hx n hn]
  rfl

theorem Agree.pair {x : LvT α} {m : Lv α} {y : LvT β} {p : Lv β}
    (hx : Agree x m) (hy : Agree y p) (hsz : y.size = x.size) :
    Agree (LvT.pair x y) (Graded.pair m p) := by
  intro n hn
  rw [LvT.size_pair] at hn
  rw [LvT.pair, LvT.get_build hn]
  simp only [Thunk.get]
  refine congrArg List.flatten (List.map_congr_left ?_)
  intro i hi
  rw [List.mem_range] at hi
  rw [hx i (by omega), hy (n - i) (by rw [hsz]; omega)]

theorem Agree.bindC {x : LvT α} {m : Lv α} {k : α → LvT β} {h : α → Lv β}
    (hx : Agree x m) (hk : ∀ a, Agree (k a) (h a)) (hsz : ∀ a, (k a).size = x.size) :
    Agree (LvT.bindC x k) (GradedBind.bindC m h) := by
  intro n hn
  rw [LvT.size_bindC] at hn
  rw [LvT.bindC, LvT.get_build hn]
  simp only [Thunk.get]
  refine congrArg List.flatten (List.map_congr_left ?_)
  intro i hi
  rw [List.mem_range] at hi
  rw [hx i (by omega)]
  refine congrArg List.flatten (List.map_congr_left ?_)
  intro a _
  exact hk a (n - i) (by rw [hsz a]; omega)

theorem Agree.guard {x : LvT α} {m : Lv α} (p : α → V) (hx : Agree x m) :
    Agree (LvT.guard p x) (GradedBind.guard p m) := by
  intro n hn
  rw [LvT.size_guard] at hn
  rw [LvT.guard, LvT.get_build hn]
  simp only [Thunk.get]
  rw [hx n hn]
  rfl

/-- The `if` a rule's input-decidable side condition compiles to. -/
theorem Agree.ite {c : Prop} [Decidable c] {x y : LvT α} {m p : Lv α}
    (hx : Agree x m) (hy : Agree y p) : Agree (if c then x else y) (if c then m else p) := by
  by_cases h : c <;> simp [h, hx, hy]

/-! ## Transporting a result about `Lv` to what runs -/

/-- Membership in the executable carrier matches the specification, level by level, within budget. -/
theorem mem_toLv_iff_of_agrees {x : LvT α} {m : Lv α} {s : SetE α}
    (hx : Agree x m) (hm : Agrees m s) (n : Nat) (hn : n < x.size) (a : α) :
    a ∈ x.get n ↔ s n a := by
  rw [hx n hn]; exact hm n a

/-- Cardinality of the executable carrier matches the counting interpretation, within budget. -/
theorem length_get_eq_of_counts {x : LvT α} {m : Lv α} {c : Cnt α}
    (hx : Agree x m) (hm : Counts m c) (n : Nat) (hn : n < x.size) :
    (x.get n).length = c n := by
  rw [hx n hn]; exact hm n

end Basalt
