import SOnlyEventTransfer
import SOnlyEventPattern

/-!
# The exact target-completion sample and its public audit

This module joins the actual normal-response constructor, the fixed target
pattern, and the public audit decoder. Starting at an actual persistent
sample followed by a certified cursor-only bridge into the response script,
it identifies the exact root-reset completion sample, its accepted descendant,
and that descendant's source prestate readout. The 56-contraction response
bound excludes the preceding C4 deletion contraction.

It does not yet prove global firstness or exclusion of other accepted
occurrences. Those need the generated-occurrence invariant and stage lift.
-/
namespace SOnlyEventResponse

open PureSFormal PureSFormal.PureS PureSFormal.Research
open SOnlyEventTransfer SOnlyEventPattern

set_option maxRecDepth 20000
set_option maxHeartbeats 5000000

/-- The target's FRAME, route, and nineteen-bit appender have exact cost 56. -/
theorem target_response_cost :
    LocalResponse.completedCost SOnly38.program SOnly38.targetRoute SOnly38.targetLabel = 56 := by
  decide

/-- A cursor-only bridge and the imported response constructor identify the
literal final response tree at its exact contraction index. -/
theorem response_final_sample
    (inputBits : List Bool) (registers : SchedulerControl.Registers SOnly38.program)
    (bit : Bool) (seedBits : List Bool) (continuation carrier : Term)
    (parents : List ParentFrame) (sampleIndex bridgeTicks : Nat)
    (before : SchedulerInvariant.Configuration SOnly38.program SOnly38.dispatcher)
    (beforeEq : (persistentSystem inputBits).contractionRun sampleIndex = before)
    (bridge : SchedulerInvariant.ZeroMutationRun (SchedulerControl.machine SOnly38.program SOnly38.dispatcher)
      bridgeTicks before
      (SchedulerResponse.responseStartConfiguration SOnly38.program SOnly38.dispatcher
        registers bit seedBits continuation carrier parents)) :
    SOnly38.trajectory inputBits
      (sampleIndex + LocalResponse.completedCost SOnly38.program
        (SOnly38.dispatcher.route (registers.phase, bit)) (registers.phase, bit)) =
      Cursor.rebuild parents (LocalResponse.completed seedBits continuation carrier
        (SchedulerResponse.completedRoute SOnly38.program SOnly38.dispatcher registers bit carrier)) := by
  obtain ⟨configurations, scriptChain, pairs⟩ :=
    SchedulerCycle.normalResponse_exactPairedMutationChain SOnly38.program SOnly38.dispatcher
      registers bit seedBits continuation carrier parents
  have flags := SchedulerCycle.responseEntries_finalFlags SOnly38.program
    (SOnly38.dispatcher.route_valid (registers.phase, bit)) seedBits continuation carrier
  obtain ⟨leading, checkpoint, decomposition, erased⟩ :=
    SchedulerNestedResponse.ResponseSamplePairs.terminalDecomposition SOnly38.program SOnly38.dispatcher
      registers bit seedBits continuation carrier parents pairs flags
  have final : SchedulerTraceAlgebra.LastSample configurations checkpoint := by
    rw [decomposition]
    exact (SchedulerTraceAlgebra.LastSample.one checkpoint).appendLeft leading
  have chain := SchedulerResponseInvariant.ExactMutationChain.prepend bridge scriptChain
  have sampled := SchedulerTraceAlgebra.ExactMutationChain.contractionRun_eq_last
    SOnly38.program SOnly38.dispatcher inputBits
    (SchedulerRecurrence.initialGood SOnly38.program SOnly38.dispatcher inputBits)
    chain final beforeEq
  have lengthEq := pairs.length_eq.trans
    (SchedulerResponseInvariant.responseEntries_length SOnly38.program
      (SOnly38.dispatcher.route_valid (registers.phase, bit)) seedBits continuation carrier)
  rw [lengthEq] at sampled
  rw [trajectory_eq_contractionRun, sampled]
  exact erased

/-- Target completion is exactly 56 contractions after entry, at every outer
zipper, including nonfinal jobs whose public checkpoint decoder is silent. -/
theorem target_final_sample
    (inputBits : List Bool) (registers : SchedulerControl.Registers SOnly38.program)
    (phaseEq : registers.phase = SOnly38.targetPhase)
    (seedBits : List Bool) (continuation carrier : Term)
    (parents : List ParentFrame) (sampleIndex bridgeTicks : Nat)
    (before : SchedulerInvariant.Configuration SOnly38.program SOnly38.dispatcher)
    (beforeEq : (persistentSystem inputBits).contractionRun sampleIndex = before)
    (bridge : SchedulerInvariant.ZeroMutationRun (SchedulerControl.machine SOnly38.program SOnly38.dispatcher)
      bridgeTicks before
      (SchedulerResponse.responseStartConfiguration SOnly38.program SOnly38.dispatcher
        registers true seedBits continuation carrier parents)) :
    SOnly38.trajectory inputBits (sampleIndex + 56) =
      Cursor.rebuild parents (LocalResponse.completed seedBits continuation carrier
        (SchedulerResponse.completedRoute SOnly38.program SOnly38.dispatcher registers true carrier)) := by
  have result := response_final_sample inputBits registers true seedBits continuation carrier
    parents sampleIndex bridgeTicks before beforeEq bridge
  have labelEq : (registers.phase, true) = SOnly38.targetLabel := by rw [phaseEq]; rfl
  rw [labelEq, SOnly38.target_selected_route, target_response_cost] at result
  exact result

/-- At that actual root-reset sample there is a matching target occurrence,
and its seed-free audit reader reconstructs the exact pre-transition word. -/
theorem target_completion_event_and_readout
    (inputBits : List Bool) (registers : SchedulerControl.Registers SOnly38.program)
    (phaseEq : registers.phase = SOnly38.targetPhase)
    (seedBits : List Bool) (continuation carrier : Term)
    (admissible : Carrier.Admissible continuation) (suffix : List Bool)
    (decoded : CarrierDecoder.decode? SOnly38.program SOnly38.dispatcher.tree
      seedBits continuation admissible carrier = some suffix)
    (parents : List ParentFrame) (sampleIndex bridgeTicks : Nat)
    (before : SchedulerInvariant.Configuration SOnly38.program SOnly38.dispatcher)
    (beforeEq : (persistentSystem inputBits).contractionRun sampleIndex = before)
    (bridge : SchedulerInvariant.ZeroMutationRun (SchedulerControl.machine SOnly38.program SOnly38.dispatcher)
      bridgeTicks before
      (SchedulerResponse.responseStartConfiguration SOnly38.program SOnly38.dispatcher
        registers true seedBits continuation carrier parents)) :
    ∃ address shell,
      (SOnly38.trajectory inputBits (sampleIndex + 56)).subterm? address = some shell ∧
      targetPattern.matchesBool shell = true ∧
      readPrestate SOnly38.program SOnly38.dispatcher.tree true shell = some (true :: suffix) := by
  let shell := LocalResponse.completed seedBits continuation carrier
    (SchedulerResponse.completedRoute SOnly38.program SOnly38.dispatcher registers true carrier)
  let cursor : Cursor := ⟨shell, parents⟩
  refine ⟨RootResetSelectorContract.cursorAddress cursor, shell, ?_, ?_, ?_⟩
  · rw [target_final_sample inputBits registers phaseEq seedBits continuation carrier
      parents sampleIndex bridgeTicks before beforeEq bridge]
    exact RootResetSelectorContract.subterm?_erase_cursorAddress cursor
  · exact completed_target_matches registers phaseEq seedBits continuation carrier
  · exact completed_readPrestate SOnly38.program SOnly38.dispatcher.tree seedBits
      continuation carrier _ admissible true suffix decoded

/-- The selected normal-response theorem itself discharges the audit-decode
premise. Its source phase and actual script-entry bridge remain visible. -/
theorem selectedTarget_event_and_readout
    (inputBits seedBits : List Bool) (continuation source : Term)
    (admissible : Carrier.Admissible continuation)
    (registers : SchedulerControl.Registers SOnly38.program)
    (phaseEq : registers.phase = SOnly38.targetPhase) (suffix : List Bool)
    (outerContext fullContext innerContext targetContext : Context)
    (parents : List ParentFrame) (responseTicks sampleIndex bridgeTicks : Nat)
    (response : SchedulerCycle.SelectedResponseTrace SOnly38.program SOnly38.dispatcher
      seedBits continuation source admissible registers true suffix outerContext
      fullContext innerContext targetContext parents responseTicks)
    (before : SchedulerInvariant.Configuration SOnly38.program SOnly38.dispatcher)
    (beforeEq : (persistentSystem inputBits).contractionRun sampleIndex = before)
    (bridge : SchedulerInvariant.ZeroMutationRun
      (SchedulerControl.machine SOnly38.program SOnly38.dispatcher) bridgeTicks before
      (SchedulerResponse.responseStartConfiguration SOnly38.program SOnly38.dispatcher
        (SchedulerCycle.scannedRegisters registers true suffix) true seedBits continuation
        (SchedulerCycle.deletedCarrier true outerContext innerContext) parents)) :
    ∃ address shell,
      (SOnly38.trajectory inputBits (sampleIndex + 56)).subterm? address = some shell ∧
      targetPattern.matchesBool shell = true ∧
      readPrestate SOnly38.program SOnly38.dispatcher.tree true shell = some (true :: suffix) := by
  have scannedPhase : (SchedulerCycle.scannedRegisters registers true suffix).phase =
      SOnly38.targetPhase := by
    rw [SchedulerCycle.scannedRegisters, SchedulerCycle.scanRegisters_phase]
    unfold SchedulerControl.Registers.observeLive
    split <;> exact phaseEq
  exact target_completion_event_and_readout inputBits
    (SchedulerCycle.scannedRegisters registers true suffix) scannedPhase seedBits continuation
    (SchedulerCycle.deletedCarrier true outerContext innerContext) admissible suffix
    response.targetDecode parents sampleIndex bridgeTicks before beforeEq bridge

end SOnlyEventResponse

#print axioms SOnlyEventResponse.target_response_cost
#print axioms SOnlyEventResponse.response_final_sample
#print axioms SOnlyEventResponse.target_final_sample
#print axioms SOnlyEventResponse.target_completion_event_and_readout

#print axioms SOnlyEventResponse.selectedTarget_event_and_readout
