import SOnlyTemporalMemory

/-!
# Global UT19 assembly and source-level instruction simulation

This module joins the literal memory and counter words. Alignment is always
`true = take`, and all transitions below are transitions of the actual FIFO
machine, including safety at every intervening microstep.
-/

namespace SOnlySimulation

open SOnlySource SOnlyCounter SOnlyMemory SOnlyTemporalMemory

set_option maxRecDepth 20000
set_option maxHeartbeats 5000000

theorem phaseAfter_add (m n : Nat) (q : Bool) :
    phaseAfter (m + n) q = phaseAfter n (phaseAfter m q) := by
  induction m generalizing q with
  | zero => simp [phaseAfter]
  | succ m ih => simpa only [Nat.succ_add, phaseAfter] using ih (!q)

@[simp] theorem phaseAfter_even (n : Nat) (q : Bool) : phaseAfter (2 * n) q = q := by
  induction n generalizing q with
  | zero => rfl
  | succ n ih =>
    rw [Nat.mul_succ, Nat.add_comm, phaseAfter_add]
    simpa only [phaseAfter, Bool.not_not] using ih q

@[simp] theorem phaseAfter_odd (n : Nat) (q : Bool) :
    phaseAfter (2 * n + 1) q = !q := by rw [phaseAfter_add, phaseAfter_even]; rfl

theorem phaseAfter_of_even (n : Nat) (h : n % 2 = 0) (q : Bool) :
    phaseAfter n q = q := by
  have hn : n = 2 * (n / 2) := by omega
  rw [hn, phaseAfter_even]

theorem phaseAfter_mod (n : Nat) (q : Bool) :
    phaseAfter n q = if n % 2 = 0 then q else !q := by
  have hm : n % 2 < 2 := Nat.mod_lt _ (by decide)
  by_cases h : n % 2 = 0
  · simp [h, phaseAfter_of_even n h q]
  · have hn : n = 2 * (n / 2) + 1 := by omega
    rw [hn, phaseAfter_odd]
    simp

@[simp] theorem memory_next_phase (cells : List Cell) (q : Bool) :
    phaseAfter (memory cells).length q = Bool.xor q (widthParity cells) := by
  rw [phaseAfter_mod, memory_width]
  cases q <;> cases widthParity cells <;> rfl

@[simp] theorem memory_command_phase (cells : List Cell) (q p : Bool) :
    phaseAfter (pass q (memory cells)).length p = p := by
  rw [memory_command_length, phaseAfter_even]

@[simp] theorem memory_parity_phase (cells : List Cell) (q p r : Bool) :
    phaseAfter (pass p (pass q (memory cells))).length r = r := by
  rw [memory_parity_length, phaseAfter_even]

@[simp] theorem ordinary_phase (n : Nat) (q : Bool) : phaseAfter (C n).length q = q :=
  phaseAfter_of_even _ (command_words_even n).1 q

@[simp] theorem protected_phase (n : Nat) (q : Bool) : phaseAfter (T n).length q = q :=
  phaseAfter_of_even _ (command_words_even n).2 q

/-- The machine consumes every original head before any appended production. -/
theorem prefix_nonempty (front suffix : List Symbol) (q : Bool) (time : Nat)
    (htime : time < front.length) : (iterate time ⟨front ++ suffix, q⟩).word ≠ [] := by
  induction front generalizing suffix q time with
  | nil => simp at htime
  | cons a as ih =>
    cases time with
    | zero => simp [iterate]
    | succ time =>
      have htime' : time < as.length := by simpa using htime
      have h := ih (suffix ++ if q then production a else []) (!q) time htime'
      rw [SOnlyCounter.iterate_add]
      change (iterate time ⟨(as ++ suffix) ++ (if q then production a else []), !q⟩).word ≠ []
      rw [List.append_assoc]
      exact h

/-- A finite, nonempty, event-free segment of the actual microstep trajectory. -/
def SafeRun (start finish : Config) : Prop :=
  ∃ steps : Nat, 0 < steps ∧ iterate steps start = finish ∧
    ∀ time, time < steps →
      ¬Selected (iterate time start) ∧ (iterate time start).word ≠ []

theorem SafeRun.trans {a b c : Config} (hab : SafeRun a b) (hbc : SafeRun b c) :
    SafeRun a c := by
  obtain ⟨m, hm, hab, hma⟩ := hab
  obtain ⟨n, hn, hbc, hnb⟩ := hbc
  refine ⟨m + n, by omega, ?_, ?_⟩
  · rw [Nat.add_comm, SOnlyCounter.iterate_add, hab, hbc]
  · intro time htime
    by_cases h : time < m
    · exact hma time h
    · have ht : time = (time - m) + m := by omega
      rw [ht, SOnlyCounter.iterate_add, hab]
      exact hnb (time - m) (by omega)

/-- Whole-queue passes now inherit safety and no-exhaustion for every microstep. -/
theorem safe_pass_run (word : List Symbol) (q : Bool) (hne : word ≠ [])
    (hsafe : safePass q word = true) :
    SafeRun ⟨word, q⟩ ⟨pass q word, phaseAfter word.length q⟩ := by
  refine ⟨word.length, List.length_pos_iff.mpr hne, ?_, ?_⟩
  · simpa using consume_source_prefix word [] q
  · intro time htime
    constructor
    · simpa using safe_prefix_no_event word [] q time hsafe htime
    · simpa using prefix_nonempty word [] q time htime

theorem counter_safe (word : List Symbol) (q : Bool) (hw : CounterWord word) :
    safePass q word = true := by
  induction word generalizing q with
  | nil => rfl
  | cons a as ih =>
    apply (safePass_cons a as q).mpr
    constructor
    · intro _ heq
      have ha := hw a (by simp)
      subst a
      simp at ha
    · exact ih (!q) (fun s hs => hw s (by simp [hs]))

/-- An assembled component may be a program memory or an ordinary/protected counter. -/
inductive Piece where
  | mem (cells : List Cell)
  | count (n : Nat)
  | protect (n : Nat)

def Piece.word : Piece → List Symbol
  | .mem cells => memory cells
  | .count n => C n
  | .protect n => T n

def assemble (pieces : List Piece) : List Symbol := pieces.flatMap Piece.word

/-- Stage-one local alignment, obtained from consumed component widths. -/
def alignments (q : Bool) : List Piece → List Bool
  | [] => []
  | piece :: rest => q :: alignments (phaseAfter piece.word.length q) rest

/-- A complete pass, preserving component boundaries exactly. -/
def passPieces (q : Bool) : List Piece → List (List Symbol)
  | [] => []
  | piece :: rest => pass q piece.word :: passPieces (phaseAfter piece.word.length q) rest

theorem pass_assemble (pieces : List Piece) (q : Bool) :
    pass q (assemble pieces) = (passPieces q pieces).flatten := by
  induction pieces generalizing q with
  | nil => rfl
  | cons a as ih =>
    change pass q (a.word ++ assemble as) = _
    rw [pass_append, ih]
    rfl

/-- Every Command pass of an assembled memory/counter word is event-free. -/
theorem assembled_command_safe (pieces : List Piece) (q : Bool) :
    safePass q (assemble pieces) = true := by
  induction pieces generalizing q with
  | nil => rfl
  | cons a as ih =>
    change safePass q (a.word ++ assemble as) = true
    rw [safePass_append, ih, Bool.and_true]
    cases a with
    | mem cells => exact memory_command_safe cells q
    | count n => exact counter_safe _ q (ordinary_counter_word n)
    | protect n => exact counter_safe _ q (protected_counter_word n)

/-- Every Parity pass of the actual assembled Command output is also event-free. -/
theorem assembled_parity_safe (pieces : List Piece) (q p : Bool) :
    safePass p (pass q (assemble pieces)) = true := by
  induction pieces generalizing q p with
  | nil => rfl
  | cons a as ih =>
    change safePass p (pass q (a.word ++ assemble as)) = true
    rw [pass_append, safePass_append, ih, Bool.and_true]
    cases a with
    | mem cells => exact memory_parity_safe cells q p
    | count n => exact counter_safe _ p (pass_counter_word _ q (ordinary_counter_word n))
    | protect n => exact counter_safe _ p (pass_counter_word _ q (protected_counter_word n))

/-- Every second-pass component has even length, including exceptional counters. -/
theorem assembled_reset_even (pieces : List Piece) (q p : Bool) :
    (pass p (pass q (assemble pieces))).length % 2 = 0 := by
  induction pieces generalizing q p with
  | nil => rfl
  | cons a as ih =>
    change (pass p (pass q (a.word ++ assemble as))).length % 2 = 0
    rw [pass_append, pass_append, List.length_append, Nat.add_mod, ih, Nat.add_zero, Nat.mod_mod]
    cases a with
    | mem cells => simp [Piece.word, memory_parity_length]
    | count n => exact reset_word_even n q p
    | protect n => exact protected_reset_even n q p

/-- Odd Reset skips every marker across the entire assembled queue, even after
an exceptional singleton changed the local Parity alignment. -/
theorem assembled_odd_reset_safe (pieces : List Piece) (q p : Bool) :
    safePass false (pass p (pass q (assemble pieces))) = true := by
  induction pieces generalizing q p with
  | nil => rfl
  | cons a as ih =>
    change safePass false (pass p (pass q (a.word ++ assemble as))) = true
    rw [pass_append, pass_append, safePass_append]
    have heven : (pass p (pass q a.word)).length % 2 = 0 := by
      cases a with
      | mem cells => simp [Piece.word, memory_parity_length]
      | count n => exact reset_word_even n q p
      | protect n => exact protected_reset_even n q p
    rw [phaseAfter_of_even _ heven, ih, Bool.and_true]
    cases a with
    | mem cells => exact memory_reset_safe cells q p false (Or.inr rfl)
    | count n => exact counter_safe _ false (pass_counter_word _ p (pass_counter_word _ q (ordinary_counter_word n)))
    | protect n => exact counter_safe _ false (pass_counter_word _ p (pass_counter_word _ q (protected_counter_word n)))

end SOnlySimulation

#print axioms SOnlySimulation.safe_pass_run
#print axioms SOnlySimulation.assembled_command_safe
#print axioms SOnlySimulation.assembled_parity_safe
#print axioms SOnlySimulation.assembled_reset_even
#print axioms SOnlySimulation.assembled_odd_reset_safe
