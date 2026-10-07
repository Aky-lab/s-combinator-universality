import SOnlySimulationComplete

namespace SOnlySimulation

open SOnlySource SOnlyCounter SOnlyMemory SOnlyTemporalMemory

set_option maxRecDepth 20000
set_option maxHeartbeats 5000000

/-- A one-pass structural reader of maximal runs of published symbol 16.
The pending accumulator makes no reference to the source program or history. -/
def runLengthsAux : Nat → List Symbol → List Nat
  | n, [] => if n = 0 then [] else [n]
  | n, symbol :: tail => if symbol = 15 then runLengthsAux (n+1) tail
      else (if n = 0 then [] else [n]) ++ runLengthsAux 0 tail

def runLengths (word : List Symbol) : List Nat := runLengthsAux 0 word

theorem runLengths_skip (separator tail : List Symbol) (hn : (15 : Symbol) ∉ separator) :
    runLengthsAux 0 (separator ++ tail) = runLengthsAux 0 tail := by
  induction separator with
  | nil => rfl
  | cons a as ih =>
    have ha : a ≠ 15 := by intro h; subst a; exact hn (by simp)
    have has : (15 : Symbol) ∉ as := fun h => hn (by simp [h])
    simpa [runLengthsAux, ha] using ih has

theorem runLengths_separator (separator tail : List Symbol) (n : Nat)
    (hne : separator ≠ []) (hn : (15 : Symbol) ∉ separator) :
    runLengthsAux n (separator ++ tail) =
      (if n = 0 then [] else [n]) ++ runLengthsAux 0 tail := by
  cases separator with
  | nil => contradiction
  | cons a as =>
    have ha : a ≠ 15 := by intro h; subst a; exact hn (by simp)
    have has : (15 : Symbol) ∉ as := fun h => hn (by simp [h])
    simp only [List.cons_append, runLengthsAux, if_neg ha, runLengths_skip as tail has]

theorem runLengths_copies (count n : Nat) (tail : List Symbol) :
    runLengthsAux n (copies [15] count ++ tail) = runLengthsAux (n+count) tail := by
  induction count generalizing n with
  | zero => simp [copies]
  | succ count ih =>
    simp only [copies_succ, List.singleton_append, List.cons_append, List.nil_append, runLengthsAux, ite_true]
    rw [ih]
    congr 1; omega

theorem finalResult_readout (rows : List (List Cell × Nat)) (tail : List Symbol)
    (rowsNonempty : ∀ row ∈ rows, row.1 ≠ []) (tailNonempty : tail ≠ [])
    (tailNo16 : (15 : Symbol) ∉ tail) (n : Nat) :
    runLengthsAux n (finalResult rows tail) =
      (if n = 0 then [] else [n]) ++ rows.map (fun row => 4 ^ (row.2 + 1)) := by
  induction rows generalizing n with
  | nil =>
    simpa [finalResult, runLengthsAux] using runLengths_separator tail [] n tailNonempty tailNo16
  | cons row rows ih =>
    obtain ⟨cells, value⟩ := row
    have hcell := rowsNonempty (cells,value) (by simp)
    have hprops := result_separator_properties cells value hcell
    simp only [finalResult]
    rw [runLengths_separator _ _ n hprops.1 hprops.2.1, runLengths_copies, Nat.zero_add]
    rw [ih (fun r hr => rowsNonempty r (by simp [hr]))]
    have hpower : 4 ^ (value+1) ≠ 0 := by have := Nat.pow_pos (n:=value+1) (by decide : 0<4); omega
    simp [hpower]

theorem indexedIncrement_map_double (mem : Nat → List Cell) (value : Nat → Nat) (n base : Nat) :
    indexedIncrementRows mem (fun b => 2*value b) n base =
      (indexedIncrementRows mem value n base).map (fun row => (row.1, 2*row.2)) := by
  induction n generalizing base with
  | zero => rfl
  | succ n ih => simp [indexedIncrementRows, ih]

def encodedRunLengths (value : Nat → Nat) : Nat → Nat → List Nat
  | 0, _ => []
  | n+1, base => 4 ^ (value base+1) :: encodedRunLengths value n (base+1)

theorem indexedIncrement_runLengths (mem : Nat → List Cell) (value : Nat → Nat) (n base : Nat) :
    (indexedIncrementRows mem value n base).map (fun row => 4^(row.2+1)) =
      encodedRunLengths value n base := by
  induction n generalizing base with
  | zero => rfl
  | succ n ih => simp [indexedIncrementRows, encodedRunLengths, ih]

/-- The decoder reads exactly the C source counter powers, in label order;
it does not report the deleted halt counter or any memory symbols. -/
theorem finalEvent_readout (depth count : Nat) (program : BPProgram) (value : Nat → Nat) :
    runLengths (finalEvent depth count program value).word = encodedRunLengths value count 0 := by
  let mem := programMemory depth count program (2*program.length+3)
  change runLengths (haltOutput (indexedIncrementRows mem (fun b => 2*value b) count 0) (mem count) (mem (count+1))) = _
  rw [indexedIncrement_map_double, halt_output_grammar]
  have hn : ∀ b, mem b ≠ [] := fun b => epoch_nonempty depth _ _ _ b
  have hhead := markerWord_head (mem count) (hn count) (pass true (pass false (memory (mem (count+1)))))
  have htail : markerWord (mem count) ++ pass true (pass false (memory (mem (count+1)))) ≠ [] := by
    intro h; simp [h] at hhead
  have hno : (15 : Symbol) ∉ markerWord (mem count) ++ pass true (pass false (memory (mem (count+1)))) := by
    simp only [List.mem_append, not_or]
    exact ⟨marker_no_result_symbol _, memory_parity_no_result _ false true⟩
  rw [runLengths, finalResult_readout _ _ (indexedIncrement_nonempty mem value count 0 hn) htail hno 0]
  simp only [ite_true, List.nil_append, indexedIncrement_runLengths]

/-- Any first observed tag event has precisely the source's retained output
queue. This theorem accepts an actual microstep index, not a macro-boundary. -/
theorem first_event_exact (depth count : Nat) (program : BPProgram)
    (valid : WellFormed count program) (capacity : 2*program.length+3 < 2^depth)
    (time : Nat) (event : Selected (iterate time ⟨seed depth count program, true⟩))
    (first : ∀ earlier, earlier < time → ¬Selected (iterate earlier ⟨seed depth count program, true⟩)) :
    ∃ n, SOnlyMachineBP2.Halted program (SOnlyMachineBP2.run program n initialState) ∧
      iterate time ⟨seed depth count program, true⟩ =
        finalEvent depth count program (SOnlyMachineBP2.run program n initialState).value ∧
      runLengths (iterate time ⟨seed depth count program, true⟩).word =
        encodedRunLengths (SOnlyMachineBP2.run program n initialState).value count 0 := by
  obtain ⟨n, hn⟩ := (source_halting_iff_event depth count program valid capacity).mpr ⟨time,event⟩
  obtain ⟨⟨steps, _, hsteps, hsafe⟩, hselected⟩ := source_termination_first_event depth count program valid capacity n hn
  have heq : steps = time := by
    have hnotlt : ¬ steps < time := by intro h; exact first steps h (hsteps ▸ hselected)
    have hnotgt : ¬ time < steps := by intro h; exact (hsafe time h).1 event
    omega
  subst steps
  refine ⟨n, hn, hsteps, ?_⟩
  rw [hsteps]
  exact finalEvent_readout depth count program _

/-- Choosing W=2N, with any power-of-two N large enough for the expanded
commands, discharges the complete horizon premise. This includes the least N. -/
theorem compact_capacity (depth : Nat) (program : BPProgram) (enough : program.length+3 ≤ 2^depth) :
    2*program.length+3 < 2^(depth+1) := by
  rw [Nat.pow_succ]
  omega

theorem compact_source_halting_iff_event (depth count : Nat) (program : BPProgram)
    (valid : WellFormed count program) (enough : program.length+3 ≤ 2^depth) :
    (∃ n, SOnlyMachineBP2.Halted program (SOnlyMachineBP2.run program n initialState)) ↔
      ∃ time, Selected (iterate time ⟨seed (depth+1) count program, true⟩) :=
  source_halting_iff_event (depth+1) count program valid (compact_capacity depth program enough)

end SOnlySimulation

#print axioms SOnlySimulation.finalEvent_readout
#print axioms SOnlySimulation.first_event_exact
#print axioms SOnlySimulation.compact_source_halting_iff_event
