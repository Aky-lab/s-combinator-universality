import SOnlySimulationExceptional

namespace SOnlySimulation

open SOnlySource SOnlyCounter SOnlyMemory SOnlyTemporalMemory

set_option maxRecDepth 20000
set_option maxHeartbeats 5000000

/-- Full Reset-entrance queue at the designated event. The halt counter is
absent, and the final memory has switched to even local Parity. -/
def haltOutput (before : List IncrementRow) (haltMemory last : List Cell) : List Symbol :=
  incrementResultPrefix before
    (markerWord haltMemory ++ pass true (pass false (memory last)))

/-- Exact output of the two passes in the second half of the halt instruction. -/
theorem halt_output_exact (before : List IncrementRow) (haltMemory last : List Cell)
    (q : Bool) (fits : ExceptionalFits q false before [] haltMemory last) :
    pass false (pass q (exceptionalWord before [] haltMemory last)) =
      haltOutput before haltMemory last := by
  obtain ⟨hbefore, ht, _, _⟩ := fits
  unfold exceptionalWord haltOutput
  rw [incrementPrefix_marker before _ q hbefore]
  congr 1
  simp only [incrementPrefix, pass_append, fits_counter_phase haltMemory _ false ht,
    ordinary_phase, memory_command_phase]
  rw [memory_marker, zero_decrement_command]
  rfl

theorem markerWord_head (cells : List Cell) (hne : cells ≠ []) (tail : List Symbol) :
    (markerWord cells ++ tail).head? = some (17 : Symbol) := by
  cases cells with
  | nil => contradiction
  | cons cell cells => rfl

/-- The very first Reset symbol is selected 18, including with zero ordinary
counters. Counter words are still intact at this pre-transition event. -/
theorem halt_output_selected (before : List IncrementRow) (haltMemory last : List Cell)
    (hh : haltMemory ≠ []) (hb : ∀ row ∈ before, row.1 ≠ []) :
    Selected ⟨haltOutput before haltMemory last, true⟩ := by
  constructor
  · rfl
  · cases before with
    | nil => exact markerWord_head haltMemory hh _
    | cons row rows =>
      obtain ⟨cells, n⟩ := row
      exact markerWord_head cells (hb (cells,n) (by simp)) _

/-- The assembled halt halfcommand reaches that event after two complete
passes, with no earlier selected 18 and no earlier empty queue. -/
theorem halt_run (before : List IncrementRow) (haltMemory last : List Cell)
    (q : Bool) (fits : ExceptionalFits q false before [] haltMemory last)
    (hh : haltMemory ≠ []) (hb : ∀ row ∈ before, row.1 ≠ []) :
    SafeRun ⟨exceptionalWord before [] haltMemory last, q⟩
      ⟨haltOutput before haltMemory last, true⟩ ∧
      Selected ⟨haltOutput before haltMemory last, true⟩ := by
  constructor
  · let word := exceptionalWord before [] haltMemory last
    have hne := exceptional_nonempty before [] haltMemory last q false hh hb
    have hs : word = assemble (exceptionalPieces before [] haltMemory last) := exceptional_assemble _ _ _ _
    have h1 := safe_pass_run word q hne.1 (by rw [hs]; exact assembled_command_safe _ q)
    rw [exceptional_command_phase _ _ _ _ q false fits] at h1
    have h2 := safe_pass_run (pass q word) false hne.2.1
      (by rw [hs]; exact assembled_parity_safe _ q false)
    rw [exceptional_parity_phase _ _ _ _ q false false fits] at h2
    have h := h1.trans h2
    simpa only [word, halt_output_exact _ _ _ q fits, Bool.not_false] using h
  · exact halt_output_selected before haltMemory last hh hb

/-- The count in paired notation is exactly the source-level power of four. -/
theorem result_counter_word (value : Nat) :
    copies [15, 15] (2 ^ (2 * value + 1)) = copies [15] (4 ^ (value + 1)) := by
  rw [two_copies, twice_pow]
  congr 1
  have he : 2 * value + 1 + 1 = 2 * (value + 1) := by omega
  rw [he, Nat.pow_mul]

/-- Canonical result grammar, parameterized by the source counter values. -/
def finalResult : List (List Cell × Nat) → List Symbol → List Symbol
  | [], tail => tail
  | (cells, value) :: rows, tail => markerWord cells ++
      (copies [15] (4 ^ (value + 1)) ++ finalResult rows tail)

/-- Every ordinary counter's exact result run is preserved, in label order;
the deleted halt counter contributes no extra run. -/
theorem halt_output_grammar (rows : List (List Cell × Nat)) (haltMemory last : List Cell) :
    haltOutput (rows.map (fun row => (row.1, 2 * row.2))) haltMemory last =
      finalResult rows (markerWord haltMemory ++ pass true (pass false (memory last))) := by
  unfold haltOutput
  induction rows with
  | nil => rfl
  | cons row rows ih =>
    obtain ⟨cells, value⟩ := row
    simp only [List.map_cons, incrementResultPrefix, finalResult, result_counter_word, ih]

/-- Memory separators contain no published 16. -/
theorem marker_no_result_symbol (cells : List Cell) : (15 : Symbol) ∉ markerWord cells := by
  induction cells with
  | nil => simp [markerWord]
  | cons cell cells ih =>
    obtain ⟨h, a⟩ := cell
    cases a <;> simpa [markerWord, markerComponent] using ih

theorem component_parity_no_result : ∀ h a q p : Bool,
    (15 : Symbol) ∉ pass p (pass q (component h a)) := by decide +kernel

theorem memory_parity_no_result (cells : List Cell) (q p : Bool) :
    (15 : Symbol) ∉ pass p (pass q (memory cells)) := by
  induction cells generalizing q with
  | nil => simp [pass]
  | cons cell cells ih =>
    obtain ⟨h, a⟩ := cell
    rw [memory_cons, pass_append, pass_append, command_phase_stable]
    simp only [List.mem_append, not_or]
    exact ⟨component_parity_no_result h a q p, ih _⟩

/-- Every separator in the grammar is nonempty and excludes 16, and each
counter run has length at least four. Thus these are distinct maximal runs. -/
theorem result_separator_properties (cells : List Cell) (value : Nat) (hne : cells ≠ []) :
    markerWord cells ≠ [] ∧ (15 : Symbol) ∉ markerWord cells ∧
      4 ≤ (copies [15] (4 ^ (value + 1))).length := by
  refine ⟨?_, marker_no_result_symbol cells, ?_⟩
  · intro h
    have hh := markerWord_head cells hne []
    simp [h] at hh
  · simp only [copies_length, List.length_cons, List.length_nil, Nat.zero_add, Nat.one_mul]
    rw [Nat.pow_succ]
    have hpos : 0 < 4 ^ value := Nat.pow_pos (by decide)
    omega

end SOnlySimulation

#print axioms SOnlySimulation.halt_output_exact
#print axioms SOnlySimulation.halt_run
#print axioms SOnlySimulation.halt_output_grammar
#print axioms SOnlySimulation.result_separator_properties
