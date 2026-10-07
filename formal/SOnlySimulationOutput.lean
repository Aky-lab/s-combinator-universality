import SOnlySimulationUniversal
import SOnlyMachineCorrectness

namespace SOnlySimulation

open SOnlySource PureSFormal

set_option maxRecDepth 20000
set_option maxHeartbeats 5000000

/-- At any first CTS event, the fixed current-word reader returns the output
of any supplied halting source run, regardless of its particular time index. -/
theorem machine_first_cts_reads_given_result (M : SOnlyMachine.Machine d n)
    (input : Fin (d+1) → Nat) (steps : Nat)
    (halted : M.instruction (SOnlyMachine.sourceRun M steps (SOnlyMachine.initial M input)).label = .halt)
    (time : Nat)
    (event : Event (CTS.iterate SOnly38.program time (CTS.initial SOnly38.program (machineBits M input))))
    (first : ∀ earlier, earlier < time →
      ¬Event (CTS.iterate SOnly38.program earlier (CTS.initial SOnly38.program (machineBits M input)))) :
    SOnlyResultBits.readMachineBits
      (CTS.iterate SOnly38.program time (CTS.initial SOnly38.program (machineBits M input))).data =
        some ((SOnlyMachine.sourceRun M steps (SOnlyMachine.initial M input)).value 0) := by
  obtain ⟨k, hk, hread⟩ := machine_first_cts_result M input time event first
  have heq := SOnlyMachineCorrectness.source_halted_unique M (SOnlyMachine.initial M input) steps k halted hk
  rw [← heq] at hread
  exact hread

/-- The same theorem accepts an explicit expected numerical value. -/
theorem machine_first_cts_reads_value (M : SOnlyMachine.Machine d n)
    (input : Fin (d+1) → Nat) (steps value : Nat)
    (halted : M.instruction (SOnlyMachine.sourceRun M steps (SOnlyMachine.initial M input)).label = .halt)
    (output : (SOnlyMachine.sourceRun M steps (SOnlyMachine.initial M input)).value 0 = value)
    (time : Nat)
    (event : Event (CTS.iterate SOnly38.program time (CTS.initial SOnly38.program (machineBits M input))))
    (first : ∀ earlier, earlier < time →
      ¬Event (CTS.iterate SOnly38.program earlier (CTS.initial SOnly38.program (machineBits M input)))) :
    SOnlyResultBits.readMachineBits
      (CTS.iterate SOnly38.program time (CTS.initial SOnly38.program (machineBits M input))).data = some value := by
  rw [← output]
  exact machine_first_cts_reads_given_result M input steps halted time event first

/-- Exact output-specific universality of the fixed CTS designated event:
a given result occurs at its first event iff the source halts with that result. -/
theorem machine_result_iff_first_cts_result (M : SOnlyMachine.Machine d n)
    (input : Fin (d+1) → Nat) (value : Nat) :
    (∃ steps, M.instruction (SOnlyMachine.sourceRun M steps (SOnlyMachine.initial M input)).label = .halt ∧
      (SOnlyMachine.sourceRun M steps (SOnlyMachine.initial M input)).value 0 = value) ↔
    (∃ time, Event (CTS.iterate SOnly38.program time (CTS.initial SOnly38.program (machineBits M input))) ∧
      (∀ earlier, earlier < time →
        ¬Event (CTS.iterate SOnly38.program earlier (CTS.initial SOnly38.program (machineBits M input)))) ∧
      SOnlyResultBits.readMachineBits
        (CTS.iterate SOnly38.program time (CTS.initial SOnly38.program (machineBits M input))).data = some value) := by
  constructor
  · rintro ⟨steps, hhalt, hvalue⟩
    have hex := (machine_halting_iff_cts_event M input).mp ⟨steps,hhalt⟩
    have least : ∀ t, Event (CTS.iterate SOnly38.program t (CTS.initial SOnly38.program (machineBits M input))) →
        ∃ time, Event (CTS.iterate SOnly38.program time (CTS.initial SOnly38.program (machineBits M input))) ∧
          ∀ earlier, earlier < time →
            ¬Event (CTS.iterate SOnly38.program earlier (CTS.initial SOnly38.program (machineBits M input))) := by
      intro t
      induction t using Nat.strongRecOn with
      | ind t ih =>
        intro ht
        by_cases previous : ∃ earlier, earlier < t ∧
            Event (CTS.iterate SOnly38.program earlier (CTS.initial SOnly38.program (machineBits M input)))
        · obtain ⟨earlier, hearlier, hevent⟩ := previous
          exact ih earlier hearlier hevent
        · exact ⟨t, ht, fun earlier hearlier hevent => previous ⟨earlier,hearlier,hevent⟩⟩
    obtain ⟨someTime, hsome⟩ := hex
    obtain ⟨time, hevent, hfirst⟩ := least someTime hsome
    exact ⟨time, hevent, hfirst, machine_first_cts_reads_value M input steps value hhalt hvalue time hevent hfirst⟩
  · rintro ⟨time, hevent, hfirst, hread⟩
    obtain ⟨steps, hhalt, hresult⟩ := machine_first_cts_result M input time hevent hfirst
    rw [hread] at hresult
    exact ⟨steps, hhalt, (Option.some.inj hresult).symm⟩

end SOnlySimulation

#print axioms SOnlySimulation.machine_first_cts_reads_given_result
#print axioms SOnlySimulation.machine_first_cts_reads_value
#print axioms SOnlySimulation.machine_result_iff_first_cts_result
