import SOnlySimulationOutput
import SOnlyEventEquivalence
import SOnlyGlobalFirstEvent
import SOnlyDecoderBoundCurrent

/-!
# Uniform finite-register-machine computation in the fixed S-only system

The encoder is the checked finite-machine/BP2/UT19/one-hot compiler. The
root-reset controller, finite event observer and current-tree decoder are
fixed before receiving a machine or input. Every computation step is one
ordinary S occurrence contraction. Halting is equivalent to event existence,
and the first accepted tree decodes to the source machine's output.
-/
namespace SOnlyUniversality

open PureSFormal PureSFormal.PureS

set_option maxRecDepth 20000
set_option maxHeartbeats 10000000

abbrev controller := SOnly38.controller
abbrev selector := SOnly38.selector
abbrev event := SOnlyObserver.event
abbrev decode := SOnlyCurrentDecoder.read

/-- Finite closed S syntax, with all source data confined to the initial term. -/
def encode (machine : SOnlyMachine.Machine d n) (input : Fin (d + 1) → Nat) : Term :=
  SOnly38.encode (SOnlySimulation.machineBits machine input)

def trajectory (machine : SOnlyMachine.Machine d n)
    (input : Fin (d + 1) → Nat) (index : Nat) : Term :=
  SOnly38.trajectory (SOnlySimulation.machineBits machine input) index

def Halts (machine : SOnlyMachine.Machine d n) (input : Fin (d + 1) → Nat) : Prop :=
  ∃ steps, machine.instruction
    (SOnlyMachine.sourceRun machine steps (SOnlyMachine.initial machine input)).label = .halt

def FirstEvent (machine : SOnlyMachine.Machine d n)
    (input : Fin (d + 1) → Nat) (index : Nat) : Prop :=
  event (trajectory machine input index) = true ∧
    ∀ earlier, earlier < index → event (trajectory machine input earlier) = false

theorem starts_at_encoder (machine : SOnlyMachine.Machine d n)
    (input : Fin (d + 1) → Nat) : trajectory machine input 0 = encode machine input := rfl

/-- Each invocation starts from the same finite control at the tree root. -/
theorem root_reset (term : Term) :
    controller.initial term = ⟨some controller.start, Cursor.atRoot term⟩ :=
  SOnly38.same_root_start term

/-- Only the resulting term persists between controller invocations. -/
theorem no_interinvocation_state : controller.InterInvocationState = Unit := rfl

/-- Every invocation terminates within one fixed linear input-size bound. -/
theorem all_input_linear (term : Term) :
    controller.stoppingTime term ≤ controller.coefficient * (term.size + 1) :=
  SOnly38.every_input_linear term

/-- The encoded path consists entirely of native contextual S contractions. -/
theorem every_step_native (machine : SOnlyMachine.Machine d n)
    (input : Fin (d + 1) → Nat) (index : Nat) :
    Step (trajectory machine input index) (trajectory machine input (index + 1)) :=
  SOnly38.trajectory_contracts _ index

/-- No source-liveness or event-provenance assumption remains in this equivalence. -/
theorem halting_iff_event (machine : SOnlyMachine.Machine d n) (input : Fin (d + 1) → Nat) :
    Halts machine input ↔ ∃ index, event (trajectory machine input index) = true := by
  exact (SOnlySimulation.machine_halting_iff_cts_event machine input).trans
    (SOnlyEventEquivalence.event_exists_iff _ (SOnlySimulation.machine_noPrematureEmpty machine input)).symm

private theorem least_witness (P : Nat → Prop) (bound : Nat) (holds : P bound) :
    ∃ first, P first ∧ ∀ earlier, earlier < first → ¬P earlier := by
  induction bound using Nat.strongRecOn with
  | ind bound ih =>
      rcases Classical.em (∃ earlier, earlier < bound ∧ P earlier) with previous | none
      · obtain ⟨earlier, less, previous⟩ := previous
        exact ih earlier less previous
      · refine ⟨bound, holds, ?_⟩
        intro earlier less previous
        exact none ⟨earlier, less, previous⟩

/-- A halting computation reaches its first accepted current tree with the
correct source output. The decoder receives only that tree. -/
theorem halting_first_result (machine : SOnlyMachine.Machine d n)
    (input : Fin (d + 1) → Nat) (halts : Halts machine input) :
    ∃ index steps,
      machine.instruction (SOnlyMachine.sourceRun machine steps
        (SOnlyMachine.initial machine input)).label = .halt ∧
      FirstEvent machine input index ∧
      decode (trajectory machine input index) =
        some ((SOnlyMachine.sourceRun machine steps (SOnlyMachine.initial machine input)).value 0) := by
  obtain ⟨time, occurred⟩ := (SOnlySimulation.machine_halting_iff_cts_event machine input).mp halts
  obtain ⟨first, eventAt, earlier⟩ := least_witness
    (fun time => SOnlySource.Event (CTS.iterate SOnly38.program time
      (CTS.initial SOnly38.program (SOnlySimulation.machineBits machine input)))) time occurred
  obtain ⟨steps, sourceHalt, numerical⟩ := SOnlySimulation.machine_first_cts_result
    machine input first eventAt earlier
  obtain ⟨accepted, silent, _, decoded⟩ := SOnlyGlobalFirstEvent.firstSourceEvent_current_read
    (SOnlySimulation.machineBits machine input) first _ earlier eventAt numerical
  exact ⟨_, steps, sourceHalt, ⟨accepted, silent⟩, decoded⟩

/-- Any first accepted sample is the one certified by the source computation. -/
theorem first_event_correct (machine : SOnlyMachine.Machine d n)
    (input : Fin (d + 1) → Nat) (index : Nat) (first : FirstEvent machine input index) :
    ∃ steps,
      machine.instruction (SOnlyMachine.sourceRun machine steps
        (SOnlyMachine.initial machine input)).label = .halt ∧
      decode (trajectory machine input index) =
        some ((SOnlyMachine.sourceRun machine steps (SOnlyMachine.initial machine input)).value 0) := by
  have halts := (halting_iff_event machine input).mpr ⟨index, first.1⟩
  obtain ⟨certified, steps, sourceHalt, firstCertified, decoded⟩ := halting_first_result machine input halts
  have left : index ≤ certified := by
    apply Nat.le_of_not_gt
    intro less
    have impossible := first.2 certified less
    rw [firstCertified.1] at impossible
    cases impossible
  have right : certified ≤ index := by
    apply Nat.le_of_not_gt
    intro less
    have impossible := firstCertified.2 index less
    rw [first.1] at impossible
    cases impossible
  have equal : index = certified := Nat.le_antisymm left right
  exact ⟨steps, sourceHalt, equal ▸ decoded⟩

/-- Exact value-specific computation equivalence, not just a halting signal. -/
theorem result_iff_first_event (machine : SOnlyMachine.Machine d n)
    (input : Fin (d + 1) → Nat) (value : Nat) :
    (∃ steps,
      machine.instruction (SOnlyMachine.sourceRun machine steps
        (SOnlyMachine.initial machine input)).label = .halt ∧
      (SOnlyMachine.sourceRun machine steps (SOnlyMachine.initial machine input)).value 0 = value) ↔
    ∃ index, FirstEvent machine input index ∧
      decode (trajectory machine input index) = some value := by
  constructor
  · rintro ⟨steps, halted, output⟩
    obtain ⟨index, otherSteps, otherHalt, first, decoded⟩ :=
      halting_first_result machine input ⟨steps, halted⟩
    have same := SOnlyMachineCorrectness.source_halted_unique machine
      (SOnlyMachine.initial machine input) steps otherSteps halted otherHalt
    rw [← same, output] at decoded
    exact ⟨index, first, decoded⟩
  · rintro ⟨index, first, decoded⟩
    obtain ⟨steps, halted, actual⟩ := first_event_correct machine input index first
    exact ⟨steps, halted, Option.some.inj (actual.symm.trans decoded)⟩

/-- Divergent source computations never trigger the fixed event observer. -/
theorem nonhalting_no_event (machine : SOnlyMachine.Machine d n)
    (input : Fin (d + 1) → Nat) (nonhalt : ¬Halts machine input) :
    ∀ index, event (trajectory machine input index) = false := by
  intro index
  cases observed : event (trajectory machine input index) with
  | false => rfl
  | true => exact False.elim (nonhalt ((halting_iff_event machine input).mpr ⟨index, observed⟩))

end SOnlyUniversality

#print axioms SOnlyUniversality.halting_iff_event
#print axioms SOnlyUniversality.halting_first_result
#print axioms SOnlyUniversality.first_event_correct
#print axioms SOnlyUniversality.nonhalting_no_event
#print axioms SOnlyUniversality.all_input_linear
#print axioms SOnlyUniversality.every_step_native

#print axioms SOnlyUniversality.root_reset
#print axioms SOnlyUniversality.no_interinvocation_state
#print axioms SOnlyUniversality.result_iff_first_event
