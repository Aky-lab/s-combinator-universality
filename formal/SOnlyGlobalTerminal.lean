import SOnlyGlobalOrigins
import SOnlyGlobalAncestors

/-!
# Licensed generated terminal jobs

This strengthens the actual upstream nonempty terminal-job constructor with
licenses for its ordered contraction samples and the newly retained parents.
-/
namespace SOnlyGlobalTerminal
open PureSFormal PureSFormal.PureS
open SchedulerControl SchedulerInvariant SchedulerCycle SchedulerResponseInvariant
open SchedulerNestedResponse SchedulerCompletedContext SchedulerTraceAlgebra
open SOnlyProvenance SOnlyProvenanceRows SOnlyGeneratedOrigins SOnlyCanonicalOrigins
open SOnlySchedulerOrigins SOnlyResponseLabels SOnlyGlobalOrigins SOnlyGlobalAncestors
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000

theorem completeNonemptyTerminalJobRaw_licensed
    (program : CTS.Program) (dispatcher : ActionDispatcher program)
    (bit : Bool) (suffix : List Bool) (fuel sampleIndex : Nat)
    (outerParents : List ParentFrame) (layers : Nat)
    (outer : CompletedParents program dispatcher outerParents layers)
    (allowed : OriginSet program)
    (outerLicensed : LicensedParents program dispatcher allowed outerParents)
    (fuelPositive : fuel ≠ 0)
    (allNonempty : ∀ k, k ≤ fuel →
      (CTS.iterate program k
        (CTS.initial program (bit :: suffix))).data ≠ [])
    (sourceAllowed : SourceAllowed allowed (CTS.initial program (bit :: suffix)) fuel) :
    let bits := bit :: suffix
    let environment :=
      environmentCode (compileActions program dispatcher.tree) bits
    let continuation := Dovetail.clockExit fuel 0 environment
    ∃ nextParents leading checkpoint configurations,
      ExactMutationChain (SchedulerControl.machine program dispatcher)
        (SchedulerRootContinuation.nextStageSourceConfiguration program
          dispatcher fuel environment nextParents)
        (SchedulerNestedPhase.fuelTerminalConfigurationAt program dispatcher
          bits (Registers.newJob program) continuation outerParents fuel 0)
        configurations ∧
      configurations = leading ++ [checkpoint] ∧
      configurations.length =
        ExactCheckpointRun.jobCost program dispatcher bits fuel ∧
      FreshTerminalData program dispatcher bits fuel checkpoint nextParents
        (layers + 1) ∧
      (∀ {activeContext : Context}
          {checkpointChain : CheckpointDecoder.ChainView program},
        CheckpointRun.PositivePrefix program dispatcher bits fuel
            checkpoint.cursor.erase
            (ExactCheckpointRun.checkpointTime program dispatcher bits fuel)
            activeContext checkpointChain →
        sampleIndex + configurations.length =
            ExactCheckpointRun.checkpointTime program dispatcher bits fuel →
        IndexedResponseSampledStates program dispatcher bits sampleIndex
          configurations) ∧
      SamplesLicensed (RootLicensed program dispatcher.tree allowed) configurations ∧
      LicensedParents program dispatcher allowed nextParents := by
  cases fuel with
  | zero => exact (fuelPositive rfl).elim
  | succ remaining =>
      let bits := bit :: suffix
      let environment :=
        environmentCode (compileActions program dispatcher.tree) bits
      let continuation := Dovetail.clockExit (remaining + 1) 0 environment
      have he : Ordinary (RootLicensed program dispatcher.tree allowed) environment :=
        environment_ordinary _ program dispatcher bits
      have hb : Ordinary (RootLicensed program dispatcher.tree allowed) continuation :=
        clockExit_ordinary (remaining + 1) 0 he.1
      have baseLicensed : Licensed program dispatcher.tree allowed (baseCarrier environment continuation) :=
        (base_ordinary he hb).1
      have prefixAllowed : SourceAllowed allowed
          ⟨CTS.zeroPhase program, bit :: suffix⟩ remaining := by
        intro index bound label snapshot labelEq
        exact sourceAllowed index (Nat.lt_trans bound (Nat.lt_succ_self remaining))
          label snapshot labelEq
      let fullParents := PrimitiveFuel.pendingParents environment continuation
        (remaining + 1) outerParents
      let afterParents := PrimitiveFuel.pendingParents environment continuation
        remaining outerParents
      obtain ⟨outerContext, fullContext, innerContext, targetContext,
          descentTicks, responseTicks, response, baseRun⟩ :=
        nonemptyBase_toSelected_zeroRunAt program dispatcher bit suffix
          continuation
          (Dovetail.clockExit_admissible (remaining + 1) 0 environment)
          remaining outerParents
      have parentSplit : fullParents =
          .right (SchedulerResponse.pendingFunction program dispatcher bits
            continuation) :: afterParents := by
        simpa [fullParents, afterParents, environment, continuation,
          SchedulerResponse.pendingFunction,
          PendingFrame.environmentCode_eq_envelope,
          PendingFrame.frameFunction] using
          (SchedulerCycle.pendingParents_succ_cons environment continuation
            remaining outerParents)
      have baseRun' : ZeroMutationRun
          (SchedulerControl.machine program dispatcher) descentTicks
          (SchedulerNestedPhase.fuelTerminalConfigurationAt program dispatcher
            bits (Registers.newJob program) continuation outerParents
            (remaining + 1) 0)
          (upConfiguration program dispatcher
            (Registers.newJob program).clearScan omega
            (ContextCursor.frames fullContext omega
              (.right (SchedulerResponse.pendingFunction program dispatcher bits
                continuation) :: afterParents))) := by
        rw [← parentSplit]
        simpa [bits, environment, continuation, fullParents] using baseRun
      have response' : SelectedResponseTrace program dispatcher bits continuation
          (baseCarrier environment continuation)
          (Dovetail.clockExit_admissible (remaining + 1) 0 environment)
          (Registers.newJob program).clearScan bit suffix outerContext fullContext
          innerContext targetContext afterParents responseTicks := by
        simpa [bits, environment, continuation, afterParents] using response
      have prefixNonempty : ∀ k, k ≤ remaining →
          (CTS.iterate program k
            ⟨CTS.zeroPhase program, bit :: suffix⟩).data ≠ [] := by
        intro k bound
        have fuelBound : k ≤ remaining + 1 :=
          Nat.le_trans bound (Nat.le_succ remaining)
        simpa [bits, CTS.initial] using allNonempty k fuelBound
      obtain ⟨terminalRegisters, terminalPhase, terminalBit,
          terminalSuffix, terminalSource, terminalOuterContext,
          terminalFullContext, terminalInnerContext, terminalTargetContext,
          terminalTicks, prefixConfigurations, prefixChain, prefixSampled,
          prefixLength, terminalCoherent, terminalTrace, terminalEq, prefixLicensed, terminalLicensed⟩ :=
        selectedNonemptyPendingPrefix_licensed program dispatcher bits bits continuation
          (Dovetail.clockExit_admissible (remaining + 1) 0 environment)
          outerParents layers outer allowed hb outerLicensed.wraps remaining sampleIndex
          (Registers.newJob program).clearScan (CTS.zeroPhase program) bit suffix
          (baseCarrier environment continuation) outerContext fullContext
          innerContext targetContext responseTicks
          (RegistersCoherent.initial program).clearScan response' prefixNonempty baseLicensed prefixAllowed
      have stepEq : CTS.absorbingStep program
            ⟨terminalRegisters.phase, terminalBit :: terminalSuffix⟩ =
          CTS.iterate program (remaining + 1)
            (CTS.initial program bits) := by
        calc
          CTS.absorbingStep program
                ⟨terminalRegisters.phase,
                  terminalBit :: terminalSuffix⟩ =
              CTS.absorbingStep program
                ⟨terminalPhase, terminalBit :: terminalSuffix⟩ := by
                  rw [terminalCoherent.phase_eq]
          _ = CTS.absorbingStep program
              (CTS.iterate program remaining
                ⟨CTS.zeroPhase program, bit :: suffix⟩) := by
                  rw [← terminalEq]
          _ = CTS.iterate program (remaining + 1)
              (CTS.initial program bits) := by
                  rw [CTS.iterate_succ]
                  rfl
      have horizonNonempty :
          (CTS.iterate program (remaining + 1)
            (CTS.initial program bits)).data ≠ [] := by
        simpa [bits] using allNonempty (remaining + 1) (Nat.le_refl _)
      cases dataEq : (CTS.absorbingStep program
          ⟨terminalRegisters.phase,
            terminalBit :: terminalSuffix⟩).data with
      | nil =>
          have empty : (CTS.iterate program (remaining + 1)
              (CTS.initial program bits)).data = [] := by
            rw [← stepEq]
            exact dataEq
          exact (horizonNonempty empty).elim
      | cons nextBit nextSuffix =>
          let finalCarrier := deletedCarrier terminalBit terminalOuterContext
            terminalInnerContext
          let nextParents :=
            SchedulerRootContinuation.freshContinuationParents program
              dispatcher (scannedRegisters terminalRegisters terminalBit
                terminalSuffix) terminalBit bits finalCarrier outerParents
          obtain ⟨rawLeading, checkpoint, rawConfigurations, rawChain, rawEq,
              checkpointEq, rawLength, rawOuter, classifyRaw⟩ :=
            selectedFreshTerminalRawSegmentAt program dispatcher bits bits
              remaining terminalRegisters terminalPhase terminalCoherent
              terminalBit terminalSuffix
              (sampleIndex + prefixConfigurations.length) outerParents layers
              outer (by
                simpa [bits, environment, continuation] using terminalTrace)
              nextBit nextSuffix dataEq horizonNonempty
          let returnCheckpoint := selectedReturnConfiguration program dispatcher
            terminalRegisters terminalBit terminalSuffix bits continuation
            finalCarrier outerParents
          have semantic : FreshTerminalData program dispatcher bits
              (remaining + 1) returnCheckpoint nextParents (layers + 1) := by
            simpa [bits, environment, continuation, finalCarrier, nextParents,
              returnCheckpoint] using
              (selectedFreshTerminalShapeAt program dispatcher bits remaining
                terminalRegisters terminalPhase terminalCoherent terminalBit
                terminalSuffix outerParents layers outer
                (by simpa [bits, environment, continuation] using terminalTrace)
                (by simpa [bits, CTS.initial] using terminalEq)
                horizonNonempty)
          have checkpointErase : checkpoint.cursor.erase =
              returnCheckpoint.cursor.erase := by
            simpa [returnCheckpoint, selectedReturnConfiguration,
              SchedulerResponse.returnConfiguration,
              SchedulerResponse.completedCursor, finalCarrier] using!
              checkpointEq
          have terminalData : FreshTerminalData program dispatcher bits
              (remaining + 1) checkpoint nextParents (layers + 1) :=
            FreshTerminalData.of_checkpointErase semantic checkpointErase
          have prefixAndRaw :=
            SchedulerRecurrence.ExactMutationChain.append prefixChain rawChain
          have completeChain := ExactMutationChain.prepend baseRun' prefixAndRaw
          let leading := prefixConfigurations ++ rawLeading
          let configurations := prefixConfigurations ++ rawConfigurations
          have configurationsEq : configurations = leading ++ [checkpoint] := by
            simp [configurations, leading, rawEq, List.append_assoc]
          have scannedTerminalCoherent : RegistersCoherent
              (scannedRegisters terminalRegisters terminalBit terminalSuffix)
              terminalPhase (terminalBit :: terminalSuffix) false :=
            scannedRegisters_coherentAt program terminalRegisters terminalPhase
              terminalCoherent terminalBit terminalSuffix
          have scannedPhase :
              (scannedRegisters terminalRegisters terminalBit
                terminalSuffix).phase = terminalRegisters.phase :=
            scannedTerminalCoherent.phase_eq.trans
              terminalCoherent.phase_eq.symm
          have currentLabel : sourceLabel? program
              (CTS.iterate program remaining (CTS.initial program bits)) =
                some ((scannedRegisters terminalRegisters terminalBit terminalSuffix).phase,
                  terminalBit) := by
            have stateEq : ⟨terminalPhase, terminalBit :: terminalSuffix⟩ =
                CTS.iterate program remaining (CTS.initial program bits) := by
              simpa [bits, CTS.initial] using terminalEq
            rw [← stateEq, scannedTerminalCoherent.phase_eq]
            rfl
          have origin : allowed
              ((scannedRegisters terminalRegisters terminalBit terminalSuffix).phase, terminalBit)
              finalCarrier :=
            sourceAllowed remaining (Nat.lt_succ_self remaining) _ finalCarrier currentLabel
          have rawLicensed : SamplesLicensed
              (RootLicensed program dispatcher.tree allowed) rawConfigurations :=
            selectedResponse_licensed program dispatcher allowed bits continuation terminalSource
              (Dovetail.clockExit_admissible (remaining + 1) 0 environment)
              terminalRegisters terminalBit terminalSuffix terminalOuterContext terminalFullContext
              terminalInnerContext terminalTargetContext outerParents terminalTicks terminalTrace
              terminalCoherent.seen_eq hb terminalLicensed outerLicensed.wraps origin rawChain rawLength
          have deleted : Licensed program dispatcher.tree allowed finalCarrier :=
            selectedResponse_deleted_licensed allowed terminalTrace hb.2 terminalLicensed
          have nextLicensed : LicensedParents program dispatcher allowed nextParents :=
            outerLicensed.fresh (scannedRegisters terminalRegisters terminalBit terminalSuffix)
              terminalBit bits deleted (holds_endpoint hb.2 terminalTrace.targetHolds) origin
          have terminalTransitionCost : rawConfigurations.length =
              CheckedTransition.totalCost program dispatcher terminalPhase
                (terminalBit :: terminalSuffix) := by
            rw [rawLength]
            rw [scannedPhase]
            rw [← terminalCoherent.phase_eq]
            rw [CheckedTransition.totalCost_cons, dataEq,
              CheckedTransition.markerCost_cons, Nat.add_zero]
          have iterateCost :
              CheckedTransition.totalCost program dispatcher terminalPhase
                  (terminalBit :: terminalSuffix) =
                CheckedTransition.totalCost program dispatcher
                  (CTS.iterate program remaining
                    (CTS.initial program bits)).phase
                  (CTS.iterate program remaining
                    (CTS.initial program bits)).data := by
            have exactState :
                ⟨terminalPhase, terminalBit :: terminalSuffix⟩ =
                  CTS.iterate program remaining
                    (CTS.initial program bits) := by
              simpa [bits, CTS.initial] using terminalEq
            exact congrArg
              (fun current => CheckedTransition.totalCost program dispatcher
                current.phase current.data) exactState
          have configurationsLength : configurations.length =
              ExactCheckpointRun.jobCost program dispatcher bits
                (remaining + 1) := by
            simp only [configurations, List.length_append]
            calc
              prefixConfigurations.length + rawConfigurations.length =
                  nonemptySweepCost program dispatcher remaining
                      (CTS.initial program bits) +
                    CheckedTransition.totalCost program dispatcher terminalPhase
                      (terminalBit :: terminalSuffix) := by
                rw [prefixLength, terminalTransitionCost]
                rfl
              _ = nonemptySweepCost program dispatcher remaining
                      (CTS.initial program bits) +
                    CheckedTransition.totalCost program dispatcher
                      (CTS.iterate program remaining
                        (CTS.initial program bits)).phase
                      (CTS.iterate program remaining
                        (CTS.initial program bits)).data := by
                rw [iterateCost]
              _ = nonemptySweepCost program dispatcher (remaining + 1)
                    (CTS.initial program bits) :=
                (nonemptySweepCost_succ_last program dispatcher remaining
                  (CTS.initial program bits)).symm
              _ = ExactCheckpointRun.jobCost program dispatcher bits
                    (remaining + 1) :=
                nonemptySweepCost_initial_eq_jobCost program dispatcher bits
                  (remaining + 1)
          refine ⟨nextParents, leading, checkpoint, configurations, ?_,
            configurationsEq, configurationsLength, terminalData, ?_, ?_, nextLicensed⟩
          · simpa [bits, environment, continuation, nextParents,
              SchedulerRootContinuation.freshNextStageSourceConfiguration,
              configurations] using completeChain
          · intro activeContext checkpointChain certificate indexEq
            have rawIndex :
                (sampleIndex + prefixConfigurations.length) +
                    rawConfigurations.length =
                  ExactCheckpointRun.checkpointTime program dispatcher bits
                    (remaining + 1) := by
              simpa [configurations, List.length_append, Nat.add_assoc] using
                indexEq
            have rawSampled := classifyRaw certificate rawIndex
            have completeSampled :=
              SchedulerNestedPhase.IndexedResponseSampledStates.append program
                dispatcher bits prefixSampled rawSampled
            simpa [configurations] using completeSampled

          · exact samples_append prefixLicensed rawLicensed

#print axioms completeNonemptyTerminalJobRaw_licensed
end SOnlyGlobalTerminal
