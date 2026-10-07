import SOnlySimulationNormal

namespace SOnlySimulation

open SOnlySource SOnlyCounter SOnlyMemory SOnlyTemporalMemory

set_option maxRecDepth 20000
set_option maxHeartbeats 5000000

abbrev IncrementRow := List Cell × Nat

def incrementPrefix : List IncrementRow → List Symbol → List Symbol
  | [], tail => tail
  | (cells, n) :: rows, tail => memory cells ++ (C n ++ incrementPrefix rows tail)

def incrementPieces : List IncrementRow → List Piece → List Piece
  | [], tail => tail
  | (cells, n) :: rows, tail => .mem cells :: .count n :: incrementPieces rows tail

theorem incrementPrefix_assemble (rows : List IncrementRow) (pieces : List Piece) :
    incrementPrefix rows (assemble pieces) = assemble (incrementPieces rows pieces) := by
  induction rows with
  | nil => rfl
  | cons row rows ih => obtain ⟨cells, n⟩ := row; simpa [incrementPrefix, incrementPieces, assemble, Piece.word] using congrArg (fun w => memory cells ++ (C n ++ w)) ih

def incrementEnd : Bool → List IncrementRow → Bool
  | q, [] => q
  | _, _ :: rows => incrementEnd true rows

def IncrementFits : Bool → List IncrementRow → Prop
  | _, [] => True
  | q, (cells, _) :: rows =>
      widthParity cells = Bool.xor q true ∧ IncrementFits true rows

/-- Every action in this prefix increments; in particular no positive decrement
can be corrupted by the exceptional odd Reset. -/
theorem incrementPrefix_phase (rows : List IncrementRow) (tail : List Symbol) (q : Bool)
    (fits : IncrementFits q rows) :
    phaseAfter (incrementPrefix rows tail).length q =
      phaseAfter tail.length (incrementEnd q rows) := by
  induction rows generalizing q with
  | nil => rfl
  | cons row rows ih =>
    obtain ⟨cells, n⟩ := row
    obtain ⟨hcell, hrest⟩ := fits
    simp only [incrementPrefix, List.length_append, phaseAfter_add]
    rw [fits_counter_phase cells q true hcell, ordinary_phase, ih true hrest]
    rfl

theorem incrementPrefix_command_phase (rows : List IncrementRow) (tail : List Symbol) (q p : Bool)
    (fits : IncrementFits q rows) :
    phaseAfter (pass q (incrementPrefix rows tail)).length p =
      phaseAfter (pass (incrementEnd q rows) tail).length p := by
  induction rows generalizing q with
  | nil => rfl
  | cons row rows ih =>
    obtain ⟨cells, n⟩ := row
    obtain ⟨hcell, hrest⟩ := fits
    simp only [incrementPrefix, pass_append, fits_counter_phase cells q true hcell,
      ordinary_phase, List.length_append, phaseAfter_add, memory_command_phase]
    rw [increment_command]
    simp only [copies_length, List.length_cons, List.length_nil, Nat.reduceAdd, phaseAfter_even]
    exact ih true hrest

/-- Odd Reset restores all prefix memories and preserves ordinary incremented
counters, irrespective of the prefix's Parity alignment. -/
theorem incrementPrefix_reset (rows : List IncrementRow) (tail : List Symbol) (q p : Bool)
    (fits : IncrementFits q rows) :
    halfcommand q p false (incrementPrefix rows tail) =
      incrementPrefix (rows.map (fun row => (reset row.1, row.2 + 1)))
        (halfcommand (incrementEnd q rows) p false tail) := by
  induction rows generalizing q with
  | nil => rfl
  | cons row rows ih =>
    obtain ⟨cells, n⟩ := row
    obtain ⟨hcell, hrest⟩ := fits
    simp only [incrementPrefix, halfcommand, pass_append,
      fits_counter_phase cells q true hcell, ordinary_phase,
      memory_command_phase, memory_parity_phase]
    have hc := NormalAction.command_even (.inc n) p
    have hr := NormalAction.parity_even (.inc n) p false
    change phaseAfter (pass true (C n)).length p = p at hc
    change phaseAfter (pass p (pass true (C n))).length false = false at hr
    rw [hc, hr]
    change halfcommand q p false (memory cells) ++
      (halfcommand true p false (C n) ++ halfcommand true p false (incrementPrefix rows tail)) = _
    rw [memory_reset, increment, ih true hrest]
    rfl

def incrementResultPrefix : List IncrementRow → List Symbol → List Symbol
  | [], tail => tail
  | (cells, n) :: rows, tail => markerWord cells ++
      (copies [15, 15] (2 ^ (n + 1)) ++ incrementResultPrefix rows tail)

/-- In a halt Parity pass, prefix memories become exact marker words while
source counters retain their exact constant-16 result words. -/
theorem incrementPrefix_marker (rows : List IncrementRow) (tail : List Symbol) (q : Bool)
    (fits : IncrementFits q rows) :
    pass false (pass q (incrementPrefix rows tail)) =
      incrementResultPrefix rows (pass false (pass (incrementEnd q rows) tail)) := by
  induction rows generalizing q with
  | nil => rfl
  | cons row rows ih =>
    obtain ⟨cells, n⟩ := row
    obtain ⟨hcell, hrest⟩ := fits
    simp only [incrementPrefix, pass_append,
      fits_counter_phase cells q true hcell, ordinary_phase, memory_command_phase]
    have hc := NormalAction.command_even (.inc n) false
    change phaseAfter (pass true (C n)).length false = false at hc
    rw [hc, memory_marker, increment_command, pass_constant_pairs, production_14, ih true hrest]
    rfl

/-- Exactly one zero-exponent counter, between ordinary increment prefixes. -/
def exceptionalWord (before after : List IncrementRow) (target last : List Cell) : List Symbol :=
  incrementPrefix before (memory target ++ (C 0 ++ incrementPrefix after (memory last)))

def exceptionalPieces (before after : List IncrementRow) (target last : List Cell) : List Piece :=
  incrementPieces before (.mem target :: .count 0 :: incrementPieces after [.mem last])

theorem exceptional_assemble (before after : List IncrementRow) (target last : List Cell) :
    exceptionalWord before after target last = assemble (exceptionalPieces before after target last) := by
  unfold exceptionalWord exceptionalPieces
  have h := incrementPrefix_assemble after [.mem last]
  simp only [assemble, List.flatMap_cons, List.flatMap_nil, Piece.word, List.append_nil] at h
  rw [h]
  exact incrementPrefix_assemble before (.mem target :: .count 0 :: incrementPieces after [.mem last])

/-- The singleton is required to be the only requested decrement. Desired
Command and global Parity alignments are checked from the memory widths. -/
def ExceptionalFits (q p : Bool) (before after : List IncrementRow) (target last : List Cell) : Prop :=
  IncrementFits q before ∧
  widthParity target = Bool.xor (incrementEnd q before) false ∧
  IncrementFits false after ∧
  widthParity last = Bool.xor (incrementEnd false after) p

theorem exceptional_command_phase (before after : List IncrementRow) (target last : List Cell)
    (q p : Bool) (fits : ExceptionalFits q p before after target last) :
    phaseAfter (exceptionalWord before after target last).length q = p := by
  obtain ⟨hbefore, ht, hafter, hl⟩ := fits
  unfold exceptionalWord
  rw [incrementPrefix_phase before _ q hbefore]
  simp only [List.length_append, phaseAfter_add]
  rw [fits_counter_phase target _ false ht, ordinary_phase,
    incrementPrefix_phase after _ false hafter, fits_counter_phase last _ p hl]

/-- The one singleton flips the global phase exactly once. -/
theorem exceptional_parity_phase (before after : List IncrementRow) (target last : List Cell)
    (q p r : Bool) (fits : ExceptionalFits q p before after target last) :
    phaseAfter (pass q (exceptionalWord before after target last)).length r = !r := by
  obtain ⟨hbefore, ht, hafter, hl⟩ := fits
  unfold exceptionalWord
  rw [incrementPrefix_command_phase before _ q r hbefore]
  simp only [pass_append, fits_counter_phase target _ false ht, ordinary_phase,
    List.length_append, phaseAfter_add, memory_command_phase]
  rw [zero_decrement_command]
  change phaseAfter (pass false (incrementPrefix after (memory last))).length (!r) = !r
  rw [incrementPrefix_command_phase after _ false (!r) hafter, memory_command_phase]

/-- Global zero-decrement output: every memory is reset, precisely the target
is protected, and every other counter follows its ordinary increment path. -/
theorem exceptional_reset (before after : List IncrementRow) (target last : List Cell)
    (q : Bool) (fits : ExceptionalFits q true before after target last) :
    halfcommand q true false (exceptionalWord before after target last) =
      incrementPrefix (before.map (fun row => (reset row.1, row.2 + 1)))
        (memory (reset target) ++ (D ++
          incrementPrefix (after.map (fun row => (reset row.1, row.2 + 1))) (memory (reset last)))) := by
  obtain ⟨hbefore, ht, hafter, hl⟩ := fits
  unfold exceptionalWord
  rw [incrementPrefix_reset before _ q true hbefore]
  congr 1
  simp only [halfcommand, pass_append, fits_counter_phase target _ false ht,
    ordinary_phase, memory_command_phase, memory_parity_phase]
  rw [zero_decrement_command]
  change halfcommand (incrementEnd q before) true false (memory target) ++
    (pass false (pass true [14]) ++ halfcommand false false false (incrementPrefix after (memory last))) = _
  rw [memory_reset]
  have hzero : pass false (pass true ([14] : List Symbol)) = D := by
    simpa only [halfcommand, zero_decrement_command] using zero_decrement_protects
  rw [hzero, incrementPrefix_reset after _ false false hafter, memory_reset]

/-- A nonempty memory before the exceptional target supplies every pass entrance. -/
theorem exceptional_nonempty (before after : List IncrementRow) (target last : List Cell)
    (q p : Bool) (htarget : target ≠ [])
    (hbefore : ∀ row ∈ before, row.1 ≠ []) :
    exceptionalWord before after target last ≠ [] ∧
      pass q (exceptionalWord before after target last) ≠ [] ∧
      pass p (pass q (exceptionalWord before after target last)) ≠ [] := by
  cases before with
  | nil => exact memory_prefix_nonempty target _ q p htarget
  | cons row rows =>
    obtain ⟨cells, n⟩ := row
    exact memory_prefix_nonempty cells _ q p (hbefore (cells,n) (by simp))

/-- A failed source decrement is a finite event-free actual run. No isolated
component-phase assumption is hidden in this assembled-queue theorem. -/
theorem exceptional_reset_run (before after : List IncrementRow) (target last : List Cell)
    (q : Bool) (fits : ExceptionalFits q true before after target last)
    (htarget : target ≠ []) (hbefore : ∀ row ∈ before, row.1 ≠ []) :
    SafeRun ⟨exceptionalWord before after target last, q⟩
      ⟨halfcommand q true false (exceptionalWord before after target last), false⟩ := by
  let word := exceptionalWord before after target last
  have hne := exceptional_nonempty before after target last q true htarget hbefore
  have hs : word = assemble (exceptionalPieces before after target last) := exceptional_assemble _ _ _ _
  have h1 := safe_pass_run word q hne.1 (by rw [hs]; exact assembled_command_safe _ q)
  rw [exceptional_command_phase _ _ _ _ q true fits] at h1
  have h2 := safe_pass_run (pass q word) true hne.2.1 (by rw [hs]; exact assembled_parity_safe _ q true)
  rw [exceptional_parity_phase _ _ _ _ q true true fits] at h2
  have h3 := safe_pass_run (pass true (pass q word)) false hne.2.2
    (by rw [hs]; exact assembled_odd_reset_safe _ q true)
  have heven : (pass true (pass q word)).length % 2 = 0 := by rw [hs]; exact assembled_reset_even _ q true
  rw [phaseAfter_of_even _ heven false] at h3
  exact h1.trans (h2.trans h3)

end SOnlySimulation

#print axioms SOnlySimulation.exceptional_reset
#print axioms SOnlySimulation.exceptional_reset_run
