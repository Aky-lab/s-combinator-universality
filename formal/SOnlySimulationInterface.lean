import SOnlySimulationReadout
import SOnlyResultBits

namespace SOnlySimulation

open SOnlySource SOnlyCounter SOnlyMemory SOnlyTemporalMemory PureSFormal

set_option maxRecDepth 20000
set_option maxHeartbeats 5000000

/-- The actual encoder's least-N choice: N is the least power of two at least
L+3, and the memory width is W=2N. This depth is logarithmic in literal code. -/
def compilerDepth (program : BPProgram) : Nat := (program.length+2).log2+2

def compiledSeed (count : Nat) (program : BPProgram) : List Symbol := seed (compilerDepth program) count program

def compiledBits (count : Nat) (program : BPProgram) : List Bool := encodeWord (compiledSeed count program)

theorem compiler_capacity (program : BPProgram) : 2*program.length+3 < 2^(compilerDepth program) := by
  have h := Nat.lt_log2_self (n:=program.length+2)
  have henough : program.length+3 ≤ 2^((program.length+2).log2+1) := by omega
  exact compact_capacity _ program henough

/-- The emitted memory width remains linear in literal source program length. -/
theorem compiler_width_bound (program : BPProgram) : 2^(compilerDepth program) ≤ 4*program.length+8 := by
  have hl := Nat.log2_self_le (n:=program.length+2) (by omega)
  unfold compilerDepth
  rw [Nat.pow_add]
  change 2^((program.length+2).log2) * 4 ≤ 4*program.length+8
  omega

theorem published_copies (symbol : Symbol) (n : Nat) :
    SOnlyResultBits.published (copies [symbol] n) = List.replicate n (symbol.val+1) := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [copies, SOnlyResultBits.published, List.replicate_succ] using congrArg (List.cons (symbol.val+1)) ih

theorem published_no16 (word : List Symbol) (hn : (15 : Symbol) ∉ word) :
    ∀ symbol ∈ SOnlyResultBits.published word, symbol ≠ 16 := by
  intro symbol hs heq
  obtain ⟨s, hs, hval⟩ := List.mem_map.mp hs
  have hindex : s.val = 15 := by omega
  have hs16 : s = (15 : Symbol) := Fin.ext hindex
  exact hn (hs16 ▸ hs)

/-- The existing fixed structural counter reader succeeds on the actual event
queue, without access to source execution or a search through the trace. -/
theorem finalEvent_readCounter (depth count : Nat) (program : BPProgram) (value : Nat → Nat)
    (positive : 0 < count) :
    SOnlyResult.readCounter (SOnlyResultBits.published (finalEvent depth count program value).word) = some (value 0) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : count ≠ 0)
  let mem := programMemory depth (k+1) program (2*program.length+3)
  let rest := indexedIncrementRows mem (fun b => 2*value b) k 1
  have hmem : ∀ b, mem b ≠ [] := fun b => epoch_nonempty depth _ _ _ b
  have hhead := (halt_output_selected rest (mem (k+1)) (mem (k+2)) (hmem (k+1))
    (indexedIncrement_nonempty mem _ k 1 hmem)).2
  have htail : (SOnlyResultBits.published (haltOutput rest (mem (k+1)) (mem (k+2)))).head? ≠ some 16 := by
    simp [SOnlyResultBits.published, List.head?_map, hhead]
    decide
  change SOnlyResult.readCounter (SOnlyResultBits.published
    (markerWord (mem 0) ++ (copies [15,15] (2^(2*value 0+1)) ++ haltOutput rest (mem (k+1)) (mem (k+2))))) = _
  rw [result_counter_word]
  simp only [SOnlyResultBits.published, List.map_append]
  change SOnlyResult.readCounter ((SOnlyResultBits.published (markerWord (mem 0))) ++
    (SOnlyResultBits.published (copies [15] (4^(value 0+1))) ++
      SOnlyResultBits.published (haltOutput rest (mem (k+1)) (mem (k+2))))) = _
  rw [published_copies, ← List.append_assoc]
  exact SOnlyResult.readCounter_correct _ _ _ (published_no16 _ (marker_no_result_symbol _)) htail

/-- The fixed odd-counter numerical convention is also decoded successfully. -/
theorem finalEvent_readMachineValue (depth count : Nat) (program : BPProgram) (value : Nat → Nat)
    (positive : 0 < count) (result : Nat) (hresult : value 0 = 2*result+3) :
    SOnlyResult.readMachineValue (SOnlyResultBits.published (finalEvent depth count program value).word) = some result := by
  unfold SOnlyResult.readMachineValue
  rw [finalEvent_readCounter depth count program value positive, hresult]
  exact SOnlyResult.decodeMachineValue_correct result

/-- Any source nonempty prestate keeps all nineteen bit positions of its
one-hot block nonempty, including the partially consumed event block. -/
theorem cts_nonempty_from_source (config : Config) (time : Nat)
    (hne : (iterate (time/19) config).word ≠ []) :
    (CTS.iterate SOnly38.program time (encode config)).data ≠ [] := by
  have ht : time = 19*(time/19) + time%19 := (Nat.div_add_mod time 19).symm
  rw [ht, Nat.add_comm, CTS.iterate_add, trajectory_simulation]
  have hoff : time%19 < 19 := Nat.mod_lt _ (by decide)
  generalize hc : iterate (time/19) config = state at *
  cases state with
  | mk word take =>
    cases word with
    | nil => contradiction
    | cons symbol tail =>
      have ho := ordinary_at_offset symbol tail take (time%19) hoff
      intro h
      unfold CTS.ordinaryStep at ho
      rw [h] at ho
      contradiction

/-- A selected prestate is necessarily a nonempty queue. -/
theorem selected_nonempty (config : Config) (selected : Selected config) : config.word ≠ [] := by
  intro h; simp [Selected, h] at selected

/-- Before any CTS exhaustion, an actual designated CTS event has already
occurred. This is the exact NoPrematureEmpty interface needed on the S side. -/
theorem compiled_noPrematureEmpty (count : Nat) (program : BPProgram) (valid : WellFormed count program) :
    ∀ time, (CTS.iterate SOnly38.program time (CTS.initial SOnly38.program (compiledBits count program))).data = [] →
      ∃ eventTime, eventTime ≤ time ∧ Event
        (CTS.iterate SOnly38.program eventTime (CTS.initial SOnly38.program (compiledBits count program))) := by
  intro time hempty
  let config : Config := ⟨compiledSeed count program, true⟩
  have hinitial : CTS.initial SOnly38.program (compiledBits count program) = encode config := rfl
  rw [hinitial] at hempty ⊢
  by_cases halt : ∃ n, SOnlyMachineBP2.Halted program (SOnlyMachineBP2.run program n initialState)
  · obtain ⟨n, hn⟩ := halt
    obtain ⟨⟨steps, _, hsteps, hsafe⟩, hselected⟩ :=
      source_termination_first_event (compilerDepth program) count program valid (compiler_capacity program) n hn
    have hevent : Selected (iterate steps config) := hsteps ▸ hselected
    have hcts := (event_at_time steps config ⟨17,by decide⟩).mpr ⟨hevent,rfl⟩
    refine ⟨19*steps+17, ?_, hcts⟩
    apply Nat.le_of_not_gt
    intro hbefore
    have hbound : time/19 ≤ steps := by omega
    have hnempty : (iterate (time/19) config).word ≠ [] := by
      by_cases hlt : time/19 < steps
      · exact (hsafe _ hlt).2
      · have heq : time/19 = steps := by omega
        rw [heq]; exact selected_nonempty _ hevent
    exact cts_nonempty_from_source config time hnempty hempty
  · have nonhalt : ∀ n, ¬SOnlyMachineBP2.Halted program (SOnlyMachineBP2.run program n initialState) := by
      simpa only [not_exists] using halt
    have hne := (source_nontermination_safe (compilerDepth program) count program valid
      (compiler_capacity program) nonhalt (time/19)).2
    exact False.elim (cts_nonempty_from_source config time hne hempty)

theorem compiled_halting_iff_cts_event (count : Nat) (program : BPProgram) (valid : WellFormed count program) :
    (∃ n, SOnlyMachineBP2.Halted program (SOnlyMachineBP2.run program n initialState)) ↔
      ∃ time, Event (CTS.iterate SOnly38.program time (CTS.initial SOnly38.program (compiledBits count program))) := by
  exact (source_halting_iff_event (compilerDepth program) count program valid (compiler_capacity program)).trans
    (SOnlySource.event_exists_iff ⟨compiledSeed count program,true⟩).symm

end SOnlySimulation

#print axioms SOnlySimulation.compiler_width_bound
#print axioms SOnlySimulation.finalEvent_readCounter
#print axioms SOnlySimulation.finalEvent_readMachineValue
#print axioms SOnlySimulation.compiled_noPrematureEmpty
#print axioms SOnlySimulation.compiled_halting_iff_cts_event
