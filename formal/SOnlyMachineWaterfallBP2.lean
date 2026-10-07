import SOnlyMachineBP2

/-!
# Literal Waterfall-to-BP2 compiler

The generated source is exactly the restart-safe initialization, guarded
trigger blocks, sweep, zero tests, and final marker pair from the written
front-end proof. Natural constants are expanded into literal unit commands.
-/
namespace SOnlyMachineWaterfallBP2

open SOnlyMachine (put)
open SOnlyMachineBP2

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

variable {α : Type} [DecidableEq α]

inductive Cell (α : Type) where
  | value : α → Cell α
  | zero : α → Cell α
  | marker : Cell α
  deriving DecidableEq, Repr

/-- Effective counter order: value cells, pending-event cells, then marker. -/
def cells (e : Enumeration α) : Enumeration (Cell α) where
  order := e.order.map Cell.value ++ e.order.map Cell.zero ++ [.marker]
  nodup := by
    simp only [List.nodup_append, List.mem_map, List.mem_singleton, List.nodup_cons, List.not_mem_nil,
      List.nodup_nil, and_true, forall_exists_index, and_imp]
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · simpa only [List.Nodup, List.pairwise_map, ne_eq, Cell.value.injEq] using e.nodup
    · simpa only [List.Nodup, List.pairwise_map, ne_eq, Cell.zero.injEq] using e.nodup
    · intro a i hi he b j hj hf; subst a; subst b; simp
    · refine ⟨by simp, ?_⟩
      intro a ha b hb
      subst b
      rcases List.mem_append.mp ha with ha | ha
      · rcases List.mem_map.mp ha with ⟨i, hi, he⟩; subst a; simp
      · rcases List.mem_map.mp ha with ⟨i, hi, he⟩; subst a; simp
  complete := by
    intro c
    cases c with
    | value i => simp [e.complete i]
    | zero i => simp [e.complete i]
    | marker => simp

def store (x z : α → Nat) (m : Nat) : Cell α → Nat
  | .value i => x i
  | .zero i => z i
  | .marker => m

def ready (x : α → Nat) (m : Nat) : Cell α → Nat := store x (fun _ => 1) m

def initWeight (w : α → Nat) : Cell α → Nat
  | .value i => w i
  | .zero _ => 1
  | .marker => 0

def triggerWeight (A : α → α → Nat) (halt i : α) : Cell α → Nat
  | .value j => (if i = halt then 2 else A i j) - (if i = j then 1 else 0)
  | .zero _ => 0
  | .marker => if i = halt then 1 else 0

def initCode (e : Enumeration α) (w : α → Nat) : Program (Cell α) :=
  initializer (unary (cells e).order (initWeight w)) .marker

def triggerCode (e : Enumeration α) (A : α → α → Nat) (halt i : α) : Program (Cell α) :=
  guarded (unary (cells e).order (triggerWeight A halt i)) (.zero i)

def sweepWeight : Cell α → Nat
  | .value _ => 1
  | _ => 0

def sweep (e : Enumeration α) : Program (Cell α) := subMany (unary (cells e).order sweepWeight)

def test (i : α) : Program (Cell α) := [.dec (.zero i), .dec (.value i), .inc (.value i), .inc (.zero i)]

def prologue (e : Enumeration α) (w : α → Nat) (A : α → α → Nat) (halt : α) : Program (Cell α) :=
  initCode e w ++ e.order.flatMap (triggerCode e A halt)

def compile (e : Enumeration α) (w : α → Nat) (A : α → α → Nat) (halt : α) : Program (Cell α) :=
  prologue e w A halt ++ sweep e ++ e.order.flatMap test ++ [.dec .marker, .dec .marker]

/-- The first restart creates precisely the finite initial clock vector,
all pending indicators one, and the ordinary execution marker one. -/
theorem initialization (e : Enumeration α) (w : α → Nat) (A : α → α → Nat) (halt : α) :
    Reaches (compile e w A halt) ⟨0, fun _ => 0⟩ ⟨0, ready w 1⟩ := by
  have hi := initializer_first (unary (cells e).order (initWeight w)) (.marker : Cell α)
    (e.order.flatMap (triggerCode e A halt) ++ sweep e ++ e.order.flatMap test ++ [.dec .marker, .dec .marker])
    (absent_unary (cells e) (initWeight w) .marker rfl)
  have he : put (fun i => (unary (cells e).order (initWeight w)).count i) (.marker : Cell α) 1 = ready w 1 := by
    funext c
    cases c <;> simp [put, ready, store, initWeight]
  refine ⟨(unary (cells e).order (initWeight w)).length + 1, by omega, ?_⟩
  simpa only [compile, prologue, initCode, List.append_assoc, he] using hi

/-- Every complete pass through the initializer and inactive trigger table is
an exact no-op, for any working clock vector, including zeros and exit marker 2. -/
theorem prologue_straight (e : Enumeration α) (w : α → Nat) (A : α → α → Nat) (halt : α)
    (x : α → Nat) (m : Nat) (hm : 0 < m) :
    Straight (prologue e w A halt) (ready x m) (ready x m) := by
  apply straight_append
  · exact guarded_inactive _ _ _ hm
  · apply straight_flatMap
    intro i hi
    exact guarded_inactive _ _ _ (by simp [ready, store])

/-- A full sweep is a literal successful decrement of every clock once. -/
theorem sweep_straight (e : Enumeration α) (x z : α → Nat) (m : Nat) (hx : ∀ i, 0 < x i) :
    Straight (sweep e) (store x z m) (store (fun i => x i - 1) z m) := by
  have h := subMany_straight (unary (cells e).order sweepWeight) (store x z m) (by
    intro c
    cases c <;> simp [sweepWeight, store]
    exact hx _)
  have he : minus (store x z m) (unary (cells e).order sweepWeight) = store (fun i => x i - 1) z m := by
    funext c
    cases c <;> simp [minus, sweepWeight, store]
  simpa only [sweep, he] using h

/-- Testing a positive clock has no net effect on any counter. -/
theorem test_straight (i : α) (v : Cell α → Nat) (hz : 0 < v (.zero i)) (hx : 0 < v (.value i)) :
    Straight (test i) v v := by
  have hnz : v (.zero i) - 1 + 1 = v (.zero i) := by omega
  have hinc : Straight [.inc (.zero i)] (put v (.zero i) (v (.zero i) - 1)) v := by
    have h := Straight.inc (.zero i) [] (put v (.zero i) (v (.zero i) - 1)) _ (Straight.nil _)
    simpa [hnz] using h
  have hmid := guard_pair_straight (.value i) (put v (.zero i) (v (.zero i) - 1)) (by simpa [put] using hx)
  exact .dec (.zero i) _ v v hz (straight_append hmid hinc)

/-- Every successful zero test leaves its complete input vector unchanged. -/
theorem tests_straight (order : List α) (x : α → Nat) (m : Nat)
    (hx : ∀ i ∈ order, 0 < x i) : Straight (order.flatMap test) (ready x m) (ready x m) := by
  apply straight_flatMap
  intro i hi
  exact test_straight i _ (by simp [ready, store]) (hx i hi)

theorem marker_dec (x : α → Nat) (m : Nat) (hm : 0 < m) :
    Straight [.dec (.marker : Cell α)] (ready x m) (ready x (m - 1)) := by
  have he : put (ready x m) (.marker : Cell α) (m - 1) = ready x (m - 1) := by
    funext c
    cases c <;> simp [put, ready, store]
  have h := Straight.dec (.marker : Cell α) [] (ready x m) _ hm (Straight.nil _)
  change Straight [.dec (.marker : Cell α)] (ready x m) (put (ready x m) .marker (m - 1)) at h
  rw [he] at h
  exact h

/-- Until a zero clock is found the ending pair restarts, preserving marker 1. -/
theorem ordinary_marker_pair (pre : Program (Cell α)) (x : α → Nat) :
    run (pre ++ [.dec .marker, .dec .marker]) 2 ⟨pre.length, ready x 1⟩ =
      ⟨0, ready x 1⟩ := by
  have hfirst := straight_run (marker_dec x 1 (by decide)) pre [.dec .marker]
  have hlast := zero_guard (pre ++ [.dec .marker]) [] (.marker : Cell α) (ready x 0) rfl
  have he : put (ready x 0) (.marker : Cell α) 1 = ready x 1 := by
    funext c
    cases c <;> simp [put, ready, store]
  have h := run_join (pre ++ [.dec .marker, .dec .marker]) (m := 1) (n := 1)
    (a := ⟨pre.length, ready x 1⟩) (by simpa using hfirst)
    (show run (pre ++ [.dec .marker, .dec .marker]) 1 ⟨pre.length + 1, ready x 0⟩ = ⟨0, ready x 1⟩ by
      simpa [List.append_assoc, he] using hlast)
  exact h

/-- A sweep strictly before the next event takes one finite whole-program pass. -/
theorem tick (e : Enumeration α) (w : α → Nat) (A : α → α → Nat) (halt : α)
    (x : α → Nat) (hx : ∀ i, 1 < x i) :
    Reaches (compile e w A halt) ⟨0, ready x 1⟩ ⟨0, ready (fun i => x i - 1) 1⟩ := by
  let pre := prologue e w A halt ++ sweep e ++ e.order.flatMap test
  have hpre : Straight pre (ready x 1) (ready (fun i => x i - 1) 1) := by
    apply straight_append
    · exact straight_append (prologue_straight e w A halt x 1 (by decide))
        (sweep_straight e x (fun _ => 1) 1 (by intro i; have := hx i; omega))
    · exact tests_straight _ _ _ (by intro i hi; have := hx i; omega)
  have hr := straight_run hpre [] [.dec .marker, .dec .marker]
  have hm := ordinary_marker_pair pre (fun i => x i - 1)
  refine ⟨pre.length + 2, by omega, ?_⟩
  have hj := run_join (pre ++ [.dec .marker, .dec .marker]) (by simpa using hr) hm
  exact hj

/-- Once the halt trigger raises the marker to two, a final sweep and the last
pair fall off the actual finite source with marker zero and no extra tick. -/
theorem exit_pass (e : Enumeration α) (w : α → Nat) (A : α → α → Nat) (halt : α)
    (x : α → Nat) (hx : ∀ i, 1 < x i) :
    Reaches (compile e w A halt) ⟨0, ready x 2⟩
      ⟨(compile e w A halt).length, ready (fun i => x i - 1) 0⟩ := by
  have h : Straight (compile e w A halt) (ready x 2) (ready (fun i => x i - 1) 0) := by
    apply straight_append
    · apply straight_append
      · exact straight_append (prologue_straight e w A halt x 2 (by decide))
          (sweep_straight e x (fun _ => 1) 2 (by intro i; have := hx i; omega))
      · exact tests_straight _ _ _ (by intro i hi; have := hx i; omega)
    · exact straight_append (marker_dec _ 2 (by decide)) (marker_dec _ 1 (by decide))
  refine ⟨(compile e w A halt).length, ?_, ?_⟩
  · simp only [compile, List.length_append, List.length_cons, List.length_nil]; omega
  · simpa using straight_run h [] []

/-- State after the zero test sets its clock to one and leaves its pending flag zero. -/
def pending (y : α → Nat) (i : α) : Cell α → Nat :=
  store (put y i 1) (put (fun _ => 1) i 0) 1

theorem test_active (pre suffix : Program (Cell α)) (i : α) (y : α → Nat) (hy : y i = 0) :
    run (pre ++ test i ++ suffix) 2 ⟨pre.length, ready y 1⟩ = ⟨0, pending y i⟩ := by
  let v := put (ready y 1) (.zero i) 0
  have hfirst : Straight [.dec (.zero i)] (ready y 1) v := by
    have h := Straight.dec (.zero i) [] (ready y 1) _ (by simp [ready, store]) (Straight.nil _)
    simpa [v, ready, store] using h
  have hrun := straight_run hfirst pre ([.dec (.value i), .inc (.value i), .inc (.zero i)] ++ suffix)
  have hlast := zero_guard (pre ++ [.dec (.zero i)]) ([.inc (.value i), .inc (.zero i)] ++ suffix)
    (.value i) v (by simp [v, put, ready, store, hy])
  have he : put v (.value i) 1 = pending y i := by
    funext c
    cases c <;> simp [v, put, ready, pending, store]
  have h := run_join (pre ++ test i ++ suffix) (m := 1) (n := 1)
    (a := ⟨pre.length, ready y 1⟩) (by simpa [test, List.append_assoc] using hrun)
    (show run (pre ++ test i ++ suffix) 1 ⟨pre.length + 1, v⟩ = ⟨0, pending y i⟩ by
      simpa [test, List.append_assoc, he] using hlast)
  exact h

/-- A nodup enumeration can be split at any selected clock, with no earlier copy. -/
theorem split_at (e : Enumeration α) (i : α) :
    ∃ before after, e.order = before ++ i :: after ∧ i ∉ before := by
  obtain ⟨before, after, he⟩ := List.mem_iff_append.mp (e.complete i)
  refine ⟨before, after, he, ?_⟩
  have hn := e.nodup
  rw [he, List.nodup_append] at hn
  intro hi
  exact hn.2.2 i hi i (by simp) rfl

/-- At the next unique zero, only its pending flag is cleared; the literal
zero test causes the first of the two event-related restarts. -/
theorem detect_event (e : Enumeration α) (w : α → Nat) (A : α → α → Nat) (halt i : α)
    (x : α → Nat) (hi : x i = 1) (hx : ∀ j, j ≠ i → 1 < x j) :
    Reaches (compile e w A halt) ⟨0, ready x 1⟩ ⟨0, pending (fun j => x j - 1) i⟩ := by
  obtain ⟨before, after, he, hbefore⟩ := split_at e i
  let pre := prologue e w A halt ++ sweep e ++ before.flatMap test
  let suffix := after.flatMap test ++ [.dec .marker, .dec .marker]
  have hp : ∀ j, 0 < x j := by
    intro j
    by_cases hj : j = i
    · simpa [hj, hi]
    · have := hx j hj; omega
  have hb : ∀ j ∈ before, 0 < x j - 1 := by
    intro j hj
    have hne : j ≠ i := by intro h; subst j; exact hbefore hj
    have := hx j hne
    omega
  have hpre : Straight pre (ready x 1) (ready (fun j => x j - 1) 1) :=
    straight_append (straight_append (prologue_straight e w A halt x 1 (by decide))
      (sweep_straight e x (fun _ => 1) 1 hp)) (tests_straight before _ 1 hb)
  have hcode : compile e w A halt = pre ++ test i ++ suffix := by
    simp [compile, pre, suffix, he, List.flatMap_append, List.append_assoc]
  have hr := straight_run hpre [] (test i ++ suffix)
  have ht := test_active pre suffix i (fun j => x j - 1) (by simp [hi])
  refine ⟨pre.length + 2, by omega, ?_⟩
  rw [hcode]
  exact run_join _ (by simpa [List.append_assoc] using hr) ht

/-- The active trigger performs exactly one restart after the entire increment
vector; all preceding inactive blocks cancel, including the initializer. -/
theorem dispatch_raw (e : Enumeration α) (w : α → Nat) (A : α → α → Nat) (halt i : α)
    (y : α → Nat) :
    Reaches (compile e w A halt) ⟨0, pending y i⟩
      ⟨0, put (plus (pending y i) (unary (cells e).order (triggerWeight A halt i))) (.zero i) 1⟩ := by
  obtain ⟨before, after, he, hbefore⟩ := split_at e i
  let pre := initCode e w ++ before.flatMap (triggerCode e A halt)
  let suffix := after.flatMap (triggerCode e A halt) ++ sweep e ++ e.order.flatMap test ++ [.dec .marker, .dec .marker]
  have hpre : Straight pre (pending y i) (pending y i) := by
    apply straight_append
    · exact guarded_inactive _ _ _ (by simp [pending, store])
    · apply straight_flatMap
      intro j hj
      have hne : j ≠ i := by intro h; subst j; exact hbefore hj
      exact guarded_inactive _ _ _ (by simp [pending, store, put, hne])
  have hcode : compile e w A halt = pre ++ triggerCode e A halt i ++ suffix := by
    simp [compile, prologue, pre, suffix, he, List.flatMap_append, List.append_assoc]
  have hr := straight_run hpre [] (triggerCode e A halt i ++ suffix)
  have ha := guarded_active pre suffix (unary (cells e).order (triggerWeight A halt i)) (.zero i)
    (pending y i) (absent_unary (cells e) (triggerWeight A halt i) (.zero i) rfl)
    (by simp [pending, store, put])
  refine ⟨pre.length + ((addMany (unary (cells e).order (triggerWeight A halt i))).length + 1), by omega, ?_⟩
  rw [hcode]
  have ht := run_join (pre ++ triggerCode e A halt i ++ suffix)
    (by simpa only [List.nil_append, List.length_nil, Nat.zero_add, List.append_assoc] using hr)
    (by simpa only [triggerCode] using ha)
  simpa only [Nat.add_assoc] using ht

/-- Diagonal compensation removes exactly the spurious one introduced by BP2's
zero test, including arbitrary zeros in all other working coordinates. -/
theorem dispatch_nonhalt (e : Enumeration α) (w : α → Nat) (A : α → α → Nat) (halt i : α)
    (y : α → Nat) (hih : i ≠ halt) (hy : y i = 0) (hdiag : 0 < A i i) :
    Reaches (compile e w A halt) ⟨0, pending y i⟩ ⟨0, ready (fun j => y j + A i j) 1⟩ := by
  have he : put (plus (pending y i) (unary (cells e).order (triggerWeight A halt i))) (.zero i) 1 =
      ready (fun j => y j + A i j) 1 := by
    rw [plus_unary]
    funext c
    cases c with
    | value j =>
      by_cases hj : j = i
      · subst j; simp [put, pending, ready, store, triggerWeight, hih, hy]; omega
      · simp [put, pending, ready, store, triggerWeight, hih, hj, Ne.symm hj]
    | zero j =>
      by_cases hj : j = i <;> simp [put, pending, ready, store, triggerWeight, hih, hj]
    | marker => simp [put, pending, ready, store, triggerWeight, hih]
  simpa only [he] using dispatch_raw e w A halt i y

/-- The halt trigger uniformly adds two and raises the exit marker. -/
theorem dispatch_halt (e : Enumeration α) (w : α → Nat) (A : α → α → Nat) (halt : α)
    (y : α → Nat) (hy : y halt = 0) :
    Reaches (compile e w A halt) ⟨0, pending y halt⟩ ⟨0, ready (fun j => y j + 2) 2⟩ := by
  have he : put (plus (pending y halt) (unary (cells e).order (triggerWeight A halt halt))) (.zero halt) 1 =
      ready (fun j => y j + 2) 2 := by
    rw [plus_unary]
    funext c
    cases c with
    | value j =>
      by_cases hj : j = halt
      · subst j; simp [put, pending, ready, store, triggerWeight, hy]
      · simp [put, pending, ready, store, triggerWeight, hj, Ne.symm hj]
    | zero j =>
      by_cases hj : j = halt <;> simp [put, pending, ready, store, triggerWeight, hj]
    | marker => simp [put, pending, ready, store, triggerWeight]
  simpa only [he] using dispatch_raw e w A halt halt y

/-- Complete nonhalt event from the final positive tick through both restarts. -/
theorem nonhalt_event (e : Enumeration α) (w : α → Nat) (A : α → α → Nat) (halt i : α)
    (y : α → Nat) (hy : y i = 0) (hother : ∀ j, j ≠ i → 0 < y j)
    (hih : i ≠ halt) (hdiag : 0 < A i i) :
    Reaches (compile e w A halt) ⟨0, ready (fun j => y j + 1) 1⟩
      ⟨0, ready (fun j => y j + A i j) 1⟩ := by
  have hd := detect_event e w A halt i (fun j => y j + 1) (by simp [hy])
    (by intro j hj; have := hother j hj; omega)
  have he : (fun j => y j + 1 - 1) = y := by funext j; omega
  rw [he] at hd
  exact reaches_trans _ hd (dispatch_nonhalt e w A halt i y hih hy hdiag)

/-- Complete halt event falls off with exactly y+1, every pending flag one,
and the marker zero. No source output coordinate is cleared or rerun. -/
theorem halt_event (e : Enumeration α) (w : α → Nat) (A : α → α → Nat) (halt : α)
    (y : α → Nat) (hy : y halt = 0) (hother : ∀ j, j ≠ halt → 0 < y j) :
    Reaches (compile e w A halt) ⟨0, ready (fun j => y j + 1) 1⟩
      ⟨(compile e w A halt).length, ready (fun j => y j + 1) 0⟩ := by
  have hd := detect_event e w A halt halt (fun j => y j + 1) (by simp [hy])
    (by intro j hj; have := hother j hj; omega)
  have he : (fun j => y j + 1 - 1) = y := by funext j; omega
  rw [he] at hd
  have hh := reaches_trans _ hd (dispatch_halt e w A halt y hy)
  have hx := exit_pass e w A halt (fun j => y j + 2) (by intro j; omega)
  have he' : (fun j => y j + 2 - 1) = (fun j => y j + 1) := by funext j; omega
  rw [he'] at hx
  exact reaches_trans _ hh hx

/-- Any finite positive integer interval is realized by finitely many actual
whole-program ticks. The zero-tick case is an ordinary reflexive run. -/
theorem wait_ticks (e : Enumeration α) (w : α → Nat) (A : α → α → Nat) (halt : α)
    (y : α → Nat) (ticks : Nat) :
    ∃ t, run (compile e w A halt) t ⟨0, ready (fun j => y j + ticks + 1) 1⟩ =
      ⟨0, ready (fun j => y j + 1) 1⟩ := by
  induction ticks with
  | zero => exact ⟨0, rfl⟩
  | succ ticks ih =>
    obtain ⟨t, ht⟩ := ih
    obtain ⟨u, hu, hh⟩ := tick e w A halt (fun j => y j + (ticks + 1) + 1) (by intro j; omega)
    have he : (fun j => y j + (ticks + 1) + 1 - 1) = (fun j => y j + ticks + 1) := by
      funext j; omega
    rw [he] at hh
    exact ⟨u + t, run_join _ hh ht⟩

/-- A nonhalt event may be separated from the preceding trigger by any
positive integer delay; there is no hidden unit-time assumption. -/
theorem delayed_nonhalt_event (e : Enumeration α) (w : α → Nat) (A : α → α → Nat) (halt i : α)
    (y : α → Nat) (delay : Nat) (hd : 0 < delay)
    (hy : y i = 0) (hother : ∀ j, j ≠ i → 0 < y j)
    (hih : i ≠ halt) (hdiag : 0 < A i i) :
    Reaches (compile e w A halt) ⟨0, ready (fun j => y j + delay) 1⟩
      ⟨0, ready (fun j => y j + A i j) 1⟩ := by
  obtain ⟨t, ht⟩ := wait_ticks e w A halt y (delay - 1)
  have he : (fun j => y j + (delay - 1) + 1) = (fun j => y j + delay) := by funext j; omega
  rw [he] at ht
  obtain ⟨u, hu, hh⟩ := nonhalt_event e w A halt i y hy hother hih hdiag
  exact ⟨t + u, by omega, run_join _ ht hh⟩

/-- The distinguished zero-row event becomes literal BP2 falling-off, with
its complete output vector y+1, after any finite positive initial delay. -/
theorem delayed_halt_event (e : Enumeration α) (w : α → Nat) (A : α → α → Nat) (halt : α)
    (y : α → Nat) (delay : Nat) (hd : 0 < delay)
    (hy : y halt = 0) (hother : ∀ j, j ≠ halt → 0 < y j) :
    Reaches (compile e w A halt) ⟨0, ready (fun j => y j + delay) 1⟩
      ⟨(compile e w A halt).length, ready (fun j => y j + 1) 0⟩ := by
  obtain ⟨t, ht⟩ := wait_ticks e w A halt y (delay - 1)
  have he : (fun j => y j + (delay - 1) + 1) = (fun j => y j + delay) := by funext j; omega
  rw [he] at ht
  obtain ⟨u, hu, hh⟩ := halt_event e w A halt y hy hother
  exact ⟨t + u, by omega, run_join _ ht hh⟩

/-- Every compiler output is nonempty, independently of the machine/input. -/
theorem compile_nonempty (e : Enumeration α) (w : α → Nat) (A : α → α → Nat) (halt : α) :
    0 < (compile e w A halt).length := by
  simp only [compile, List.length_append, List.length_cons, List.length_nil]
  omega

/-- The final data coordinate has the fixed arithmetic form used by the
register-machine reduction. This reader is independent of source syntax. -/
theorem final_output (output : α) (v : Nat) (y : α → Nat) (hy : y output = 2 * (v + 1)) :
    ready (fun j => y j + 1) 0 (.value output) = 2 * v + 3 := by
  simp only [ready, store, hy]
  omega

def readOutput (counter : Nat) : Nat := (counter - 3) / 2

@[simp] theorem readOutput_correct (v : Nat) : readOutput (2 * v + 3) = v := by
  unfold readOutput
  omega

end SOnlyMachineWaterfallBP2
