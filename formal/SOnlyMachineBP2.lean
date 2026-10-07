import SOnlyMachine

/-!
# Literal BP2 operational semantics and restart-safe program blocks

All code is a finite list of ordinary unit increments and decrements. A
failed decrement sets its counter to one and restarts the entire program.
The generic counter type can be specialized to a dense `Fin C` alphabet.
-/
namespace SOnlyMachineBP2

open SOnlyMachine (put)
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

variable {α : Type} [DecidableEq α]

inductive Command (α : Type) where
  | inc : α → Command α
  | dec : α → Command α
  deriving DecidableEq, Repr

abbrev Program (α : Type) := List (Command α)

structure State (α : Type) where
  pc : Nat
  value : α → Nat

/-- One literal instruction; failed decrement always restarts at zero. -/
def execute (command : Command α) (s : State α) : State α :=
  match command with
  | .inc i => ⟨s.pc + 1, put s.value i (s.value i + 1)⟩
  | .dec i => if s.value i = 0 then ⟨0, put s.value i 1⟩
    else ⟨s.pc + 1, put s.value i (s.value i - 1)⟩

/-- The optional interface reports actual falling off the finite source. -/
def step? (P : Program α) (s : State α) : Option (State α) :=
  (P[s.pc]?).map (fun command => execute command s)

/-- Total extension, preserving the final counter vector after falling off. -/
def advance (P : Program α) (s : State α) : State α :=
  (step? P s).getD s

def run (P : Program α) : Nat → State α → State α
  | 0, s => s
  | k + 1, s => run P k (advance P s)

def Halted (P : Program α) (s : State α) : Prop := P.length ≤ s.pc

@[simp] theorem run_zero (P : Program α) (s : State α) : run P 0 s = s := rfl
@[simp] theorem run_succ (P : Program α) (k : Nat) (s : State α) :
    run P (k + 1) s = run P k (advance P s) := rfl

theorem run_add (P : Program α) (m n : Nat) (s : State α) :
    run P (m + n) s = run P n (run P m s) := by
  induction m generalizing s with
  | zero => simp [run]
  | succ m ih => simpa [Nat.succ_add, run] using ih (advance P s)

theorem step_none_iff (P : Program α) (s : State α) : step? P s = none ↔ Halted P s := by
  simp [step?, Halted]

theorem advance_halted (P : Program α) (s : State α) (h : Halted P s) : advance P s = s := by
  simp [advance, (step_none_iff P s).mpr h]

theorem run_halted (P : Program α) (k : Nat) (s : State α) (h : Halted P s) : run P k s = s := by
  induction k with
  | zero => rfl
  | succ k ih => simp [run, advance_halted P s h, ih]

/-- A program segment is independent of preceding and following code, provided
all of its decrements succeed. This relation records literal execution. -/
inductive Straight : Program α → (α → Nat) → (α → Nat) → Prop
  | nil (v) : Straight [] v v
  | inc (i : α) (tail : Program α) (v w : α → Nat)
      (rest : Straight tail (put v i (v i + 1)) w) : Straight (.inc i :: tail) v w
  | dec (i : α) (tail : Program α) (v w : α → Nat) (positive : 0 < v i)
      (rest : Straight tail (put v i (v i - 1)) w) : Straight (.dec i :: tail) v w

/-- Exact concatenation of non-restarting straight-line executions. -/
theorem straight_append {left right : Program α} {u v w : α → Nat}
    (hl : Straight left u v) (hr : Straight right v w) : Straight (left ++ right) u w := by
  induction hl with
  | nil => exact hr
  | inc i tail u v h ih => exact .inc i _ _ _ (ih hr)
  | dec i tail u v hp h ih => exact .dec i _ _ _ hp (ih hr)

/-- Fetching at the boundary of a pre reads the next literal instruction. -/
theorem fetch_boundary (pre suffix : Program α) (command : Command α) :
    (pre ++ command :: suffix)[pre.length]? = some command := by
  simp

theorem advance_boundary (pre suffix : Program α) (command : Command α) (v : α → Nat) :
    advance (pre ++ command :: suffix) ⟨pre.length, v⟩ =
      execute command ⟨pre.length, v⟩ := by
  simp [advance, step?, fetch_boundary]

/-- Every successful block has an exact execution in any surrounding program. -/
theorem straight_run {block : Program α} {v w : α → Nat} (h : Straight block v w)
    (pre suffix : Program α) :
    run (pre ++ block ++ suffix) block.length ⟨pre.length, v⟩ =
      ⟨pre.length + block.length, w⟩ := by
  induction h generalizing pre with
  | nil => simp
  | inc i tail v w h ih =>
    rw [List.length_cons, run_succ]
    have hf : advance (pre ++ (Command.inc i :: tail) ++ suffix) ⟨pre.length, v⟩ =
        ⟨pre.length + 1, put v i (v i + 1)⟩ := by
      simpa [execute] using advance_boundary pre (tail ++ suffix) (.inc i) v
    rw [hf]
    have ht := ih (pre ++ [.inc i])
    simpa [List.append_assoc, Nat.add_assoc, Nat.add_comm 1] using ht
  | dec i tail v w hp h ih =>
    rw [List.length_cons, run_succ]
    have hn : v i ≠ 0 := by omega
    have hf : advance (pre ++ (Command.dec i :: tail) ++ suffix) ⟨pre.length, v⟩ =
        ⟨pre.length + 1, put v i (v i - 1)⟩ := by
      simpa [execute, hn] using advance_boundary pre (tail ++ suffix) (.dec i) v
    rw [hf]
    have ht := ih (pre ++ [.dec i])
    simpa [List.append_assoc, Nat.add_assoc, Nat.add_comm 1] using ht

/-- A zero guard has exactly its documented effect in the whole program. -/
theorem zero_guard (pre suffix : Program α) (i : α) (v : α → Nat) (hz : v i = 0) :
    advance (pre ++ .dec i :: suffix) ⟨pre.length, v⟩ = ⟨0, put v i 1⟩ := by
  simp [advance_boundary, execute, hz]

/-- Unary constant compilation is explicit finite repetition. -/
def add (i : α) (n : Nat) : Program α := List.replicate n (.inc i)
def sub (i : α) (n : Nat) : Program α := List.replicate n (.dec i)

theorem add_straight (i : α) (n : Nat) (v : α → Nat) :
    Straight (add i n) v (put v i (v i + n)) := by
  induction n generalizing v with
  | zero => simpa [add] using Straight.nil v
  | succ n ih =>
    simp only [add, List.replicate_succ]
    have h := Straight.inc i (add i n) v _ (ih (put v i (v i + 1)))
    simpa [add, Nat.add_assoc, Nat.add_comm 1 n] using h

theorem sub_straight (i : α) (n : Nat) (v : α → Nat) (hn : n ≤ v i) :
    Straight (sub i n) v (put v i (v i - n)) := by
  induction n generalizing v with
  | zero => simpa [sub] using Straight.nil v
  | succ n ih =>
    have hp : 0 < v i := by omega
    have hn' : n ≤ (put v i (v i - 1)) i := by simp; omega
    have h := Straight.dec i (sub i n) v _ hp (ih (put v i (v i - 1)) hn')
    have he : v i - 1 - n = v i - (n + 1) := by omega
    simpa [sub, List.replicate_succ, he] using h

/-- A literal increment word; repeats implement arbitrary natural constants. -/
def addMany (word : List α) : Program α := word.map Command.inc
/-- Cancellation uses the same order as the increment word. -/
def subMany (word : List α) : Program α := word.map Command.dec

def plus (v : α → Nat) (word : List α) : α → Nat := fun i => v i + word.count i

def minus (v : α → Nat) (word : List α) : α → Nat := fun i => v i - word.count i

@[simp] theorem plus_nil (v : α → Nat) : plus v [] = v := by funext i; simp [plus]
@[simp] theorem minus_nil (v : α → Nat) : minus v [] = v := by funext i; simp [minus]
@[simp] theorem plus_at (v : α → Nat) (word : List α) (i : α) :
    plus v word i = v i + word.count i := rfl
@[simp] theorem plus_absent (v : α → Nat) (word : List α) (i : α) (h : i ∉ word) :
    plus v word i = v i := by simp [plus, List.count_eq_zero.mpr h]

theorem plus_cons (v : α → Nat) (i : α) (tail : List α) :
    plus v (i :: tail) = plus (put v i (v i + 1)) tail := by
  funext j
  by_cases h : j = i <;> simp_all [plus, put, List.count_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Ne.symm]

@[simp] theorem minus_plus (v : α → Nat) (word : List α) : minus (plus v word) word = v := by
  funext i
  simp [minus, plus]

theorem addMany_straight (word : List α) (v : α → Nat) : Straight (addMany word) v (plus v word) := by
  induction word generalizing v with
  | nil => simpa [addMany] using Straight.nil v
  | cons i tail ih =>
    rw [plus_cons]
    exact .inc i (addMany tail) v _ (ih _)

theorem subMany_straight (word : List α) (v : α → Nat)
    (h : ∀ i, word.count i ≤ v i) : Straight (subMany word) v (minus v word) := by
  induction word generalizing v with
  | nil => simpa [subMany] using Straight.nil v
  | cons i tail ih =>
    have hp : 0 < v i := by have := h i; simp only [List.count_cons_self] at this; omega
    have ht : ∀ j, tail.count j ≤ put v i (v i - 1) j := by
      intro j
      have hj := h j
      by_cases he : j = i
      · subst j; simp only [List.count_cons_self] at hj; simp; omega
      · simpa [put, he, List.count_cons, he, Ne.symm he] using hj
    have he : minus (put v i (v i - 1)) tail = minus v (i :: tail) := by
      funext j
      by_cases he : j = i
      · subst j; simp [minus]; omega
      · simp [minus, put, he, Ne.symm he, List.count_cons]
    have hh := Straight.dec i (subMany tail) v _ hp (ih _ ht)
    simpa only [subMany, List.map_cons, he] using hh

/-- The compiler's guarded addition. All additions occur before the guard. -/
def guarded (word : List α) (guard : α) : Program α :=
  addMany word ++ [.dec guard, .inc guard] ++ subMany word

theorem guard_pair_straight (guard : α) (v : α → Nat) (hp : 0 < v guard) :
    Straight [.dec guard, .inc guard] v v := by
  have he : v guard - 1 + 1 = v guard := by omega
  apply Straight.dec guard [.inc guard] v v hp
  have hh := Straight.inc guard [] (put v guard (v guard - 1)) _ (Straight.nil _)
  simpa [he] using hh

/-- Inactive guarded blocks are exact no-ops for arbitrary nonnegative
working data; in particular, temporary zeros elsewhere cause no underflow. -/
theorem guarded_inactive (word : List α) (guard : α) (v : α → Nat)
    (hp : 0 < v guard) : Straight (guarded word guard) v v := by
  have hg : 0 < plus v word guard := by simp; omega
  have hsub := subMany_straight word (plus v word) (by intro i; simp)
  rw [minus_plus] at hsub
  exact straight_append (straight_append (addMany_straight word v)
    (guard_pair_straight guard (plus v word) hg)) hsub

/-- The active guard is after every addition and before every cancellation.
It restarts the actual whole program, keeping exactly the intended additions. -/
theorem guarded_active (pre suffix : Program α) (word : List α) (guard : α) (v : α → Nat)
    (habsent : guard ∉ word) (hz : v guard = 0) :
    run (pre ++ guarded word guard ++ suffix) ((addMany word).length + 1) ⟨pre.length, v⟩ =
      ⟨0, put (plus v word) guard 1⟩ := by
  rw [run_add]
  have ha := straight_run (addMany_straight word v) pre
    ([.dec guard, .inc guard] ++ subMany word ++ suffix)
  have he : pre ++ guarded word guard ++ suffix =
      pre ++ addMany word ++ ([.dec guard, .inc guard] ++ subMany word ++ suffix) := by
    simp [guarded, List.append_assoc]
  rw [he, ha]
  simp only [run_succ, run_zero]
  have hg := zero_guard (pre ++ addMany word) ([.inc guard] ++ subMany word ++ suffix)
    guard (plus v word) (by rw [plus_absent v word guard habsent]; exact hz)
  simpa [List.append_assoc] using hg

/-- A restart-safe initializer begins at pc zero, creates the requested finite
input on its first visit, then is a no-op on every later visit with marker≥1. -/
def initializer (word : List α) (marker : α) : Program α := guarded word marker

theorem initializer_first (word : List α) (marker : α) (tail : Program α)
    (habsent : marker ∉ word) :
    run (initializer word marker ++ tail) (word.length + 1) ⟨0, fun _ => 0⟩ =
      ⟨0, put (fun i => word.count i) marker 1⟩ := by
  have he : plus (fun _ : α => 0) word = (fun i => word.count i) := by funext i; simp [plus]
  simpa only [initializer, addMany, List.length_map, List.nil_append, List.length_nil, he] using
    guarded_active [] tail word marker (fun _ => 0) habsent rfl

theorem initializer_restart (word : List α) (marker : α) (tail : Program α)
    (v : α → Nat) (hm : 0 < v marker) :
    run (initializer word marker ++ tail) (initializer word marker).length ⟨0, v⟩ =
      ⟨(initializer word marker).length, v⟩ := by
  simpa [initializer] using straight_run (guarded_inactive word marker v hm) [] tail

/-- An effective finite alphabet, with its fixed traversal order. -/
structure Enumeration (α : Type) where
  order : List α
  nodup : order.Nodup
  complete : ∀ i, i ∈ order

/-- Expand a finite natural vector into an explicit unary word. -/
def unary (order : List α) (weight : α → Nat) : List α :=
  order.flatMap (fun i => List.replicate (weight i) i)

theorem count_unary_of_nodup (order : List α) (weight : α → Nat) (h : order.Nodup) (i : α) :
    (unary order weight).count i = if i ∈ order then weight i else 0 := by
  induction order with
  | nil => simp [unary]
  | cons j tail ih =>
    have hj : j ∉ tail := (List.nodup_cons.mp h).1
    have ht := ih (List.nodup_cons.mp h).2
    change (List.replicate (weight j) j ++ unary tail weight).count i = _
    by_cases he : i = j
    · subst i
      simp [List.count_append, hj, ht]
    · simp [List.count_append, he, Ne.symm he, ht, List.count_replicate]

@[simp] theorem count_unary (e : Enumeration α) (weight : α → Nat) (i : α) :
    (unary e.order weight).count i = weight i := by
  rw [count_unary_of_nodup _ _ e.nodup, if_pos (e.complete i)]

theorem absent_unary (e : Enumeration α) (weight : α → Nat) (i : α) (h : weight i = 0) :
    i ∉ unary e.order weight := by
  apply List.count_eq_zero.mp
  simp [h]

@[simp] theorem plus_unary (e : Enumeration α) (weight v : α → Nat) :
    plus v (unary e.order weight) = fun i => v i + weight i := by
  funext i
  simp

/-- Arbitrarily many no-op blocks retain the same complete working vector. -/
theorem straight_flatMap {β : Type} (order : List β) (block : β → Program α) (v : α → Nat)
    (h : ∀ i ∈ order, Straight (block i) v v) : Straight (order.flatMap block) v v := by
  induction order with
  | nil => exact .nil v
  | cons i tail ih =>
    exact straight_append (h i (by simp)) (ih (by intro j hj; exact h j (by simp [hj])))

/-- Exact finite-run concatenation. -/
theorem run_join (P : Program α) {m n : Nat} {a b c : State α}
    (h₁ : run P m a = b) (h₂ : run P n b = c) : run P (m + n) a = c := by
  rw [run_add, h₁, h₂]

/-- A finite actual execution with a strictly positive number of instructions. -/
def Reaches (P : Program α) (a b : State α) : Prop := ∃ t, 0 < t ∧ run P t a = b

theorem reaches_trans (P : Program α) {a b c : State α}
    (hab : Reaches P a b) (hbc : Reaches P b c) : Reaches P a c := by
  obtain ⟨m, hm, he⟩ := hab
  obtain ⟨n, hn, hf⟩ := hbc
  exact ⟨m + n, by omega, run_join P he hf⟩

end SOnlyMachineBP2
