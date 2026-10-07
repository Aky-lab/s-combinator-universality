import SOnlySimulationRestart

namespace SOnlySimulation

open SOnlySource SOnlyCounter SOnlyMemory SOnlyTemporalMemory
open SOnlyMachine (put)

set_option maxRecDepth 20000
set_option maxHeartbeats 5000000

/-- Exact retained-counter event queue, computed structurally from the final
source values and the fixed encoded program memories. -/
def finalEvent (depth count : Nat) (program : BPProgram) (value : Nat → Nat) : Config :=
  let mem := programMemory depth count program (2 * program.length + 3)
  ⟨haltOutput (indexedIncrementRows mem (fun b => 2*value b) count 0) (mem count) (mem (count+1)), true⟩

/-- Actual fall-through reaches the first selected 18 after the final five
passes: three ordinary decrements and the exceptional halt pair. -/
theorem source_halt_run (depth count : Nat) (program : BPProgram) (value : Nat → Nat)
    (haltZero : value count = 0) (capacity : 2 * program.length + 3 < 2 ^ depth) :
    SafeRun (boundary depth count program program.length value) (finalEvent depth count program value) ∧
      Selected (finalEvent depth count program value) := by
  let time := 2*program.length+3
  let mem := programMemory depth count program time
  let rows := indexedIncrementRows mem (fun b => 2*value b) count 0
  have fits := scheduled_exceptional_fits depth count program time count (fun b => 2*value b)
    (by omega) capacity (fun b _ => scheduledAction_halt_second count program b)
  simp only [time, Nat.sub_self, indexedIncrementRows, scheduledParity_halt] at fits
  have hne : ∀ b, mem b ≠ [] := fun b => epoch_nonempty depth _ _ time b
  have h2 := halt_run rows (mem count) (mem (count+1))
    (scheduledEntry count program time 0) fits (hne count)
    (indexedIncrement_nonempty mem _ count 0 hne)
  have hi : programWord depth count program time (fun b => C (2*value b)) =
      exceptionalWord rows [] (mem count) (mem (count+1)) := by
    unfold programWord
    rw [indexed_exceptional_word _ _ (fun b => 2*value b) count count (by omega) (by intro b hb hbt; rfl)]
    simp only [haltZero, Nat.mul_zero, Nat.sub_self, indexedIncrementRows, incrementPrefix]
    rfl
  have hp : scheduledEntry count program time 0 = true := by simp [time]
  rw [← hi, hp] at h2
  have h1 := scheduled_normal_run depth count program (2*program.length+2)
    (fun b => NormalAction.dec (2*value b)) (by omega)
    (by intro b hb; rw [scheduledAction_halt_first]; rfl)
    (scheduledParity_normal program _ (by omega))
  have hp1 : decide (2*program.length+2 ≠ 0) = true := by simp
  simp only [NormalAction.input, NormalAction.output, Piece.word, hp1] at h1
  rw [show 2*program.length+2+1 = time from by omega] at h1
  exact ⟨h1.trans h2.1, h2.2⟩

/-- Labels occupy a fixed finite range; unused counters are harmless. -/
def WellFormed (count : Nat) (program : BPProgram) : Prop :=
  ∀ command ∈ program, match command with | .inc target | .dec target => target < count

def initialState : SOnlyMachineBP2.State Nat := ⟨0, fun _ => 0⟩

def sourceConfig (depth count : Nat) (program : BPProgram) (state : SOnlyMachineBP2.State Nat) : Config :=
  boundary depth count program state.pc state.value

/-- Every nonhalting literal source step is implemented by a finite, event-free
and nonempty UT19 run, including zero-decrement restarts. -/
theorem source_step_run (depth count : Nat) (program : BPProgram)
    (state : SOnlyMachineBP2.State Nat) (valid : WellFormed count program)
    (active : state.pc < program.length) (capacity : 2 * program.length + 3 < 2 ^ depth) :
    SafeRun (sourceConfig depth count program state)
      (sourceConfig depth count program (SOnlyMachineBP2.advance program state)) := by
  have fetch : program[state.pc]? = some program[state.pc] := List.getElem?_eq_getElem active
  have targetBound := valid program[state.pc] (List.getElem_mem active)
  have hadv : SOnlyMachineBP2.advance program state = SOnlyMachineBP2.execute program[state.pc] state := by
    simp [SOnlyMachineBP2.advance, SOnlyMachineBP2.step?, fetch]
  rw [hadv]
  cases hc : program[state.pc] with
  | inc target =>
    rw [hc] at fetch
    simpa [sourceConfig, SOnlyMachineBP2.execute] using
      source_increment_run depth count program state.pc target state.value fetch (by omega)
  | dec target =>
    rw [hc] at fetch targetBound
    by_cases hz : state.value target = 0
    · simpa [sourceConfig, SOnlyMachineBP2.execute, hz] using
        source_zero_decrement_run depth count program state.pc target state.value fetch (by omega) hz (by omega)
    · simpa [sourceConfig, SOnlyMachineBP2.execute, hz] using
        source_positive_decrement_run depth count program state.pc target state.value fetch (by omega) (by omega)

/-- Source stepping cannot overshoot the end, and cannot alter its fresh halt counter. -/
theorem source_invariants (count : Nat) (program : BPProgram) (valid : WellFormed count program)
    (state : SOnlyMachineBP2.State Nat) (pc : state.pc ≤ program.length) (hz : state.value count = 0) :
    (SOnlyMachineBP2.advance program state).pc ≤ program.length ∧
      (SOnlyMachineBP2.advance program state).value count = 0 := by
  by_cases active : state.pc < program.length
  · have fetch : program[state.pc]? = some program[state.pc] := List.getElem?_eq_getElem active
    have targetBound := valid program[state.pc] (List.getElem_mem active)
    have hadv : SOnlyMachineBP2.advance program state = SOnlyMachineBP2.execute program[state.pc] state := by
      simp [SOnlyMachineBP2.advance, SOnlyMachineBP2.step?, fetch]
    rw [hadv]
    cases hc : program[state.pc] with
    | inc target =>
      rw [hc] at targetBound
      have hne : count ≠ target := by omega
      simp [SOnlyMachineBP2.execute, put, hne, hz]
      omega
    | dec target =>
      rw [hc] at targetBound
      have hne : count ≠ target := by omega
      by_cases ht : state.value target = 0 <;> simp [SOnlyMachineBP2.execute, ht, put, hne, hz]
      omega
  · have halted : SOnlyMachineBP2.Halted program state := by unfold SOnlyMachineBP2.Halted; omega
    rw [SOnlyMachineBP2.advance_halted program state halted]
    exact ⟨pc, hz⟩

theorem source_run_succ (program : BPProgram) (n : Nat) (state : SOnlyMachineBP2.State Nat) :
    SOnlyMachineBP2.run program (n+1) state = SOnlyMachineBP2.advance program (SOnlyMachineBP2.run program n state) := by
  rw [SOnlyMachineBP2.run_add]
  rfl

theorem source_run_invariants (count : Nat) (program : BPProgram) (valid : WellFormed count program) (n : Nat) :
    (SOnlyMachineBP2.run program n initialState).pc ≤ program.length ∧
      (SOnlyMachineBP2.run program n initialState).value count = 0 := by
  induction n with
  | zero => simp [initialState]
  | succ n ih => rw [source_run_succ]; exact source_invariants count program valid _ ih.1 ih.2

/-- Initial leading 19 plus the two dummy halves establish the ordinary zero tuple. -/
theorem startup_run (depth count : Nat) (program : BPProgram) (capacity : 1 < 2 ^ depth) :
    SafeRun ⟨seed depth count program, true⟩ (sourceConfig depth count program initialState) := by
  have h1 := seed_prefix_run depth count program
  have h2 := dummy_run depth count program (fun _ => 0) capacity
  exact h1.trans h2

/-- Every finite source prefix is realized from the literal encoded seed.
After fall-through the total source semantics remains at the same boundary. -/
theorem source_prefix_run (depth count : Nat) (program : BPProgram) (valid : WellFormed count program)
    (capacity : 2 * program.length + 3 < 2 ^ depth) (n : Nat) :
    SafeRun ⟨seed depth count program, true⟩
      (sourceConfig depth count program (SOnlyMachineBP2.run program n initialState)) := by
  induction n with
  | zero => exact startup_run depth count program (by omega)
  | succ n ih =>
    rw [source_run_succ]
    by_cases active : (SOnlyMachineBP2.run program n initialState).pc < program.length
    · exact ih.trans (source_step_run depth count program _ valid active capacity)
    · have halted : SOnlyMachineBP2.Halted program (SOnlyMachineBP2.run program n initialState) := by
        unfold SOnlyMachineBP2.Halted; omega
      rw [SOnlyMachineBP2.advance_halted program _ halted]
      exact ih

/-- A terminating source has the first exact output event, with every preceding
UT19 state nonempty and event-free. This quantifies over arbitrary programs. -/
theorem source_termination_first_event (depth count : Nat) (program : BPProgram)
    (valid : WellFormed count program) (capacity : 2 * program.length + 3 < 2 ^ depth)
    (n : Nat) (halted : SOnlyMachineBP2.Halted program (SOnlyMachineBP2.run program n initialState)) :
    SafeRun ⟨seed depth count program, true⟩
      (finalEvent depth count program (SOnlyMachineBP2.run program n initialState).value) ∧
      Selected (finalEvent depth count program (SOnlyMachineBP2.run program n initialState).value) := by
  have inv := source_run_invariants count program valid n
  have pc : (SOnlyMachineBP2.run program n initialState).pc = program.length := by
    unfold SOnlyMachineBP2.Halted at halted; omega
  have hp := source_prefix_run depth count program valid capacity n
  have hh := source_halt_run depth count program (SOnlyMachineBP2.run program n initialState).value inv.2 capacity
  unfold sourceConfig at hp
  rw [pc] at hp
  exact ⟨hp.trans hh.1, hh.2⟩

/-- Nonhalting source prefixes consume at least one real microstep per source
step. This progress bound closes the converse, without a bounded search. -/
theorem nonhalting_prefix_progress (depth count : Nat) (program : BPProgram)
    (valid : WellFormed count program) (capacity : 2 * program.length + 3 < 2 ^ depth)
    (nonhalt : ∀ n, ¬SOnlyMachineBP2.Halted program (SOnlyMachineBP2.run program n initialState)) (n : Nat) :
    ∃ steps, n < steps ∧
      iterate steps ⟨seed depth count program, true⟩ =
        sourceConfig depth count program (SOnlyMachineBP2.run program n initialState) ∧
      ∀ time, time < steps → ¬Selected (iterate time ⟨seed depth count program, true⟩) ∧
        (iterate time ⟨seed depth count program, true⟩).word ≠ [] := by
  induction n with
  | zero => exact startup_run depth count program (by omega)
  | succ n ih =>
    obtain ⟨m, hm, hend, hsafe⟩ := ih
    have active : (SOnlyMachineBP2.run program n initialState).pc < program.length := by
      have hn := nonhalt n; unfold SOnlyMachineBP2.Halted at hn; omega
    obtain ⟨k, hk, hstep, hsafe'⟩ := source_step_run depth count program _ valid active capacity
    refine ⟨m+k, by omega, ?_, ?_⟩
    · rw [Nat.add_comm, SOnlyCounter.iterate_add, hend, hstep, source_run_succ]
    · intro time ht
      by_cases htm : time < m
      · exact hsafe time htm
      · rw [show time = (time-m)+m from by omega, SOnlyCounter.iterate_add, hend]
        exact hsafe' (time-m) (by omega)

/-- Nonhalting source computation has neither a designated event nor queue
exhaustion at any actual UT19 microstep. -/
theorem source_nontermination_safe (depth count : Nat) (program : BPProgram)
    (valid : WellFormed count program) (capacity : 2 * program.length + 3 < 2 ^ depth)
    (nonhalt : ∀ n, ¬SOnlyMachineBP2.Halted program (SOnlyMachineBP2.run program n initialState)) (time : Nat) :
    ¬Selected (iterate time ⟨seed depth count program, true⟩) ∧
      (iterate time ⟨seed depth count program, true⟩).word ≠ [] := by
  obtain ⟨steps, hbound, _, hsafe⟩ := nonhalting_prefix_progress depth count program valid capacity nonhalt time
  exact hsafe time hbound

/-- The unbounded compiler correctness equivalence, for the exact finite seed
and actual FIFO selected-symbol event. -/
theorem source_halting_iff_event (depth count : Nat) (program : BPProgram)
    (valid : WellFormed count program) (capacity : 2 * program.length + 3 < 2 ^ depth) :
    (∃ n, SOnlyMachineBP2.Halted program (SOnlyMachineBP2.run program n initialState)) ↔
      ∃ time, Selected (iterate time ⟨seed depth count program, true⟩) := by
  constructor
  · rintro ⟨n, hn⟩
    obtain ⟨⟨time, _, htime, _⟩, hevent⟩ := source_termination_first_event depth count program valid capacity n hn
    exact ⟨time, htime ▸ hevent⟩
  · intro hevent
    apply Classical.byContradiction
    intro h
    have nonhalt : ∀ n, ¬SOnlyMachineBP2.Halted program (SOnlyMachineBP2.run program n initialState) := by
      simpa only [not_exists] using h
    obtain ⟨time, htime⟩ := hevent
    exact (source_nontermination_safe depth count program valid capacity nonhalt time).1 htime

end SOnlySimulation

#print axioms SOnlySimulation.source_halt_run
#print axioms SOnlySimulation.source_step_run
#print axioms SOnlySimulation.source_termination_first_event
#print axioms SOnlySimulation.source_nontermination_safe
#print axioms SOnlySimulation.source_halting_iff_event
