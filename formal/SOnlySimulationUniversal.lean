import SOnlySimulationInterface
import SOnlyMachineNat

namespace SOnlySimulation

open SOnlySource SOnlyCounter SOnlyMemory SOnlyTemporalMemory PureSFormal

set_option maxRecDepth 20000
set_option maxHeartbeats 5000000

/-- Complete finite machine/input-to-CTS compiler. The 38 appendants remain
fixed; only this finite initial bitword depends on machine and input. -/
def machineBits (M : SOnlyMachine.Machine d n) (input : Fin (d+1) → Nat) : List Bool :=
  compiledBits (SOnlyMachineNat.counterCount d n) (SOnlyMachineNat.compile M input)

/-- Full register-machine halting equivalence for the literal fixed 38-phase CTS. -/
theorem machine_halting_iff_cts_event (M : SOnlyMachine.Machine d n) (input : Fin (d+1) → Nat) :
    (∃ k, M.instruction (SOnlyMachine.sourceRun M k (SOnlyMachine.initial M input)).label = .halt) ↔
      ∃ time, Event (CTS.iterate SOnly38.program time (CTS.initial SOnly38.program (machineBits M input))) := by
  exact (SOnlyMachineNat.halt_iff M input).symm.trans
    (compiled_halting_iff_cts_event _ _ (SOnlyMachineNat.compile_bounded M input))

/-- The compiled machine inputs satisfy the source liveness premise required
by the fixed S-event equivalence. Exhaustion after a prior event is allowed. -/
theorem machine_noPrematureEmpty (M : SOnlyMachine.Machine d n) (input : Fin (d+1) → Nat) :
    ∀ time, (CTS.iterate SOnly38.program time (CTS.initial SOnly38.program (machineBits M input))).data = [] →
      ∃ eventTime, eventTime ≤ time ∧ Event
        (CTS.iterate SOnly38.program eventTime (CTS.initial SOnly38.program (machineBits M input))) :=
  compiled_noPrematureEmpty _ _ (SOnlyMachineNat.compile_bounded M input)

/-- The phase-17 reader is successful whenever the current tag event word has
a successful structural numerical read. No trace search is used by the reader. -/
theorem selected_readMachineBits (config : Config) (result : Nat) (selected : Selected config)
    (reads : SOnlyResult.readMachineValue (SOnlyResultBits.published config.word) = some result) :
    SOnlyResultBits.readMachineBits (CTS.iterate SOnly38.program 17 (encode config)).data = some result := by
  cases config with
  | mk word take =>
    obtain ⟨htake, hhead⟩ := selected
    change take = true at htake
    subst take
    change word.head? = some (17 : Symbol) at hhead
    obtain ⟨tail, hword⟩ := List.head?_eq_some_iff.mp hhead
    subst word
    have he : (17 : Symbol) = (⟨17, by decide⟩ : Symbol) := by decide
    rw [he]
    rw [SOnlyResultBits.event_word, SOnlyResultBits.readMachineBits, SOnlyResultBits.decodeEventWord_correct]
    exact reads

/-- Exact current-state numerical readout at every first CTS event, for every
finite register-machine/input compilation. -/
theorem machine_first_cts_result (M : SOnlyMachine.Machine d n) (input : Fin (d+1) → Nat)
    (time : Nat)
    (event : Event (CTS.iterate SOnly38.program time (CTS.initial SOnly38.program (machineBits M input))))
    (first : ∀ earlier, earlier < time →
      ¬Event (CTS.iterate SOnly38.program earlier (CTS.initial SOnly38.program (machineBits M input)))) :
    ∃ k, M.instruction (SOnlyMachine.sourceRun M k (SOnlyMachine.initial M input)).label = .halt ∧
      SOnlyResultBits.readMachineBits
        (CTS.iterate SOnly38.program time (CTS.initial SOnly38.program (machineBits M input))).data =
          some ((SOnlyMachine.sourceRun M k (SOnlyMachine.initial M input)).value 0) := by
  let program := SOnlyMachineNat.compile M input
  let count := SOnlyMachineNat.counterCount d n
  let config : Config := ⟨compiledSeed count program, true⟩
  have hinitial : CTS.initial SOnly38.program (machineBits M input) = encode config := rfl
  rw [hinitial] at event first ⊢
  obtain ⟨htag, hmod⟩ := (event_at_arbitrary_time time config).mp event
  have firstTag : ∀ earlier, earlier < time/19 → ¬Selected (iterate earlier config) := by
    intro earlier hearly hselected
    have hcts := (event_at_time earlier config ⟨17,by decide⟩).mpr ⟨hselected,rfl⟩
    exact first (19*earlier+17) (by omega) hcts
  obtain ⟨k, hhalt, hword, _⟩ := SOnlySimulation.first_event_exact
    (compilerDepth program) count program (SOnlyMachineNat.compile_bounded M input)
    (compiler_capacity program) (time/19) htag firstTag
  change iterate (time/19) config = finalEvent (compilerDepth program) count program
    (SOnlyMachineBP2.run program k initialState).value at hword
  obtain ⟨hmachine, hvalue⟩ := SOnlyMachineNat.halt_output M input k hhalt
  refine ⟨k, hmachine, ?_⟩
  have hread := finalEvent_readMachineValue (compilerDepth program) count program
    (SOnlyMachineBP2.run program k initialState).value (SOnlyMachineNat.counterCount_pos d n)
    ((SOnlyMachine.sourceRun M k (SOnlyMachine.initial M input)).value 0) hvalue
  have hread' : SOnlyResult.readMachineValue (SOnlyResultBits.published (iterate (time/19) config).word) =
      some ((SOnlyMachine.sourceRun M k (SOnlyMachine.initial M input)).value 0) := by
    rw [hword]; exact hread
  have hbits := selected_readMachineBits (iterate (time/19) config) _ htag hread'
  have ht : time = 19*(time/19)+17 := by omega
  rw [ht, Nat.add_comm, CTS.iterate_add, trajectory_simulation]
  exact hbits

end SOnlySimulation

#print axioms SOnlySimulation.machine_halting_iff_cts_event
#print axioms SOnlySimulation.machine_noPrematureEmpty
#print axioms SOnlySimulation.machine_first_cts_result
