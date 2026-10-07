import SOnlyGlobalStages

/-! Generated first-job prefixes retain licensed Local origins up to the exact source prestate. -/
namespace SOnlyGlobalFirstPrefix
open PureSFormal PureSFormal.PureS PureSFormal.Research
open SchedulerControl SchedulerInvariant SchedulerCycle SchedulerResponseInvariant
open SchedulerNestedResponse SchedulerCompletedContext SchedulerTraceAlgebra
open SOnlyProvenance SOnlyProvenanceRows SOnlyGeneratedOrigins SOnlySchedulerOrigins
open SOnlyGlobalAncestors SOnlyGlobalOrigins SOnlyGlobalStages SOnlyStageEvents
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000

theorem stageStart_licensed (bits : List Bool) (r : Nat)
    (allNonempty : ∀ k, k ≤ r → (CTS.iterate SOnly38.program k (CTS.initial SOnly38.program bits)).data ≠ [])
    (allowed : OriginSet SOnly38.program)
    (sourceAllowed : SourceAllowed allowed (CTS.initial SOnly38.program bits) r) :
    ∃ parents configurations,
      ExactMutationChain (SchedulerControl.machine SOnly38.program SOnly38.dispatcher)
        (SchedulerRecurrence.stageSourceConfiguration SOnly38.program SOnly38.dispatcher bits (r + 1) parents)
        (SchedulerControl.initialConfiguration SOnly38.program SOnly38.dispatcher bits) configurations ∧
      configurations.length = SOnlyStageEvents.stageStartTime bits r ∧
      CompletedParents SOnly38.program SOnly38.dispatcher parents (CheckpointRun.cumulativeLayers r) ∧
      SamplesLicensed (RootLicensed SOnly38.program SOnly38.dispatcher.tree allowed) configurations ∧
      LicensedParents SOnly38.program SOnly38.dispatcher allowed parents := by
  cases r with
  | zero =>
      exact ⟨[], SchedulerRecurrence.initialPreludeConfigurations SOnly38.program SOnly38.dispatcher bits,
        SchedulerRecurrence.initialPreludeChain SOnly38.program SOnly38.dispatcher bits,
        rfl, CompletedParents.root SOnly38.program SOnly38.dispatcher,
        prelude_list_licensed _ SOnly38.program SOnly38.dispatcher bits,
        LicensedParents.nil SOnly38.program SOnly38.dispatcher allowed⟩
  | succ r =>
      cases bits with
      | nil => exact (allNonempty 0 (Nat.zero_le _) rfl).elim
      | cons bit suffix =>
          obtain ⟨past, licensed, parentsLicensed⟩ := positiveStages_licensed SOnly38.program SOnly38.dispatcher
            bit suffix allowed r allNonempty sourceAllowed
          exact ⟨past.nextParents, past.configurations, past.chain, past.count, past.nextOuter, licensed, parentsLicensed⟩


theorem firstJob_response_prefix_licensed (bit : Bool) (suffix : List Bool) (r : Nat)
    (allNonempty : ∀ k, k ≤ r →
      (CTS.iterate SOnly38.program k
        (CTS.initial SOnly38.program (bit :: suffix))).data ≠ [])
    (allowed : OriginSet SOnly38.program)
    (sourceAllowed : SourceAllowed allowed (CTS.initial SOnly38.program (bit :: suffix)) r) :
    let bits := bit :: suffix
    let environment := environmentCode (compileActions SOnly38.program SOnly38.dispatcher.tree) bits
    let continuation := Dovetail.clockExit (r + 1) r environment
    ∃ parents registers phase responseBit responseSuffix source
        outerContext fullContext innerContext targetContext ticks configurations,
      ExactMutationChain (SchedulerControl.machine SOnly38.program SOnly38.dispatcher)
        (upConfiguration SOnly38.program SOnly38.dispatcher registers omega
          (ContextCursor.frames fullContext omega
            (.right (SchedulerResponse.pendingFunction SOnly38.program SOnly38.dispatcher
              bits continuation) :: parents)))
        (SchedulerControl.initialConfiguration SOnly38.program SOnly38.dispatcher bits)
        configurations ∧
      configurations.length = firstJobPreResponseTime bits r ∧
      RegistersCoherent registers phase [] false ∧
      SelectedResponseTrace SOnly38.program SOnly38.dispatcher bits continuation source
        (Dovetail.clockExit_admissible (r + 1) r environment)
        registers responseBit responseSuffix outerContext fullContext innerContext
        targetContext parents ticks ∧
      ⟨phase, responseBit :: responseSuffix⟩ =
        CTS.iterate SOnly38.program r (CTS.initial SOnly38.program bits) ∧
      SamplesLicensed (RootLicensed SOnly38.program SOnly38.dispatcher.tree allowed) configurations ∧
      LicensedParents SOnly38.program SOnly38.dispatcher allowed parents ∧
      Ordinary (RootLicensed SOnly38.program SOnly38.dispatcher.tree allowed) continuation ∧
      Licensed SOnly38.program SOnly38.dispatcher.tree allowed source := by
  let bits := bit :: suffix
  let environment := environmentCode (compileActions SOnly38.program SOnly38.dispatcher.tree) bits
  let continuation := Dovetail.clockExit (r + 1) r environment
  have hb : Ordinary (RootLicensed SOnly38.program SOnly38.dispatcher.tree allowed) continuation :=
    clockExit_ordinary (r + 1) r (environment_carries _ SOnly38.program SOnly38.dispatcher.tree bits)
  obtain ⟨parents, prefixConfigurations, prefixChain, prefixCount, outer, prefixLicensed, outerLicensed⟩ :=
    stageStart_licensed bits r allNonempty allowed sourceAllowed
  let phaseConfigurations := SchedulerNestedPhase.positiveStageConfigurationsAt
    SOnly38.program SOnly38.dispatcher bits (Registers.newJob SOnly38.program) parents r
  have phase := SchedulerNestedPhase.positiveStagePhaseInvariantAt
    SOnly38.program SOnly38.dispatcher bits (Registers.newJob SOnly38.program)
    (CTS.zeroPhase SOnly38.program) [] false (RegistersCoherent.initial SOnly38.program)
    parents (CheckpointRun.cumulativeLayers r) outer (stageStartTime bits r) r
  have phaseChain : ExactMutationChain
      (SchedulerControl.machine SOnly38.program SOnly38.dispatcher)
      (SchedulerNestedPhase.fuelTerminalConfigurationAt SOnly38.program SOnly38.dispatcher
        bits (Registers.newJob SOnly38.program) continuation parents (r + 1) 0)
      (SchedulerRecurrence.stageSourceConfiguration SOnly38.program SOnly38.dispatcher
        bits (r + 1) parents) phaseConfigurations := by
    simpa [phaseConfigurations, continuation, environment,
      SchedulerRecurrence.stageSourceConfiguration] using phase.chain
  obtain ⟨outerContext, fullContext, innerContext, targetContext, descentTicks,
      responseTicks, response, baseRun⟩ := nonemptyBase_toSelected_zeroRunAt
        SOnly38.program SOnly38.dispatcher bit suffix continuation
        (Dovetail.clockExit_admissible (r + 1) r environment) r parents
  have parentSplit : PrimitiveFuel.pendingParents environment continuation (r + 1) parents =
      .right (SchedulerResponse.pendingFunction SOnly38.program SOnly38.dispatcher bits continuation) ::
        PrimitiveFuel.pendingParents environment continuation r parents := by
    simpa [environment, SchedulerResponse.pendingFunction, PendingFrame.environmentCode_eq_envelope,
      PendingFrame.frameFunction] using
      (SchedulerCycle.pendingParents_succ_cons environment continuation r parents)
  have baseRun' : ZeroMutationRun
      (SchedulerControl.machine SOnly38.program SOnly38.dispatcher) descentTicks
      (SchedulerNestedPhase.fuelTerminalConfigurationAt SOnly38.program SOnly38.dispatcher
        bits (Registers.newJob SOnly38.program) continuation parents (r + 1) 0)
      (upConfiguration SOnly38.program SOnly38.dispatcher (Registers.newJob SOnly38.program).clearScan omega
        (ContextCursor.frames fullContext omega
          (.right (SchedulerResponse.pendingFunction SOnly38.program SOnly38.dispatcher bits continuation) ::
            PrimitiveFuel.pendingParents environment continuation r parents))) := by
    rw [← parentSplit]
    exact baseRun
  obtain ⟨finalRegisters, finalPhase, finalBit, finalSuffix, finalSource,
      finalOuterContext, finalFullContext, finalInnerContext, finalTargetContext,
      finalTicks, pendingConfigurations, pendingChain, pendingSampled,
      pendingCount, coherent, finalTrace, sourceEq, pendingLicensed, finalLicensed⟩ :=
    selectedNonemptyPendingPrefix_licensed SOnly38.program SOnly38.dispatcher bits bits
      continuation (Dovetail.clockExit_admissible (r + 1) r environment)
      parents (CheckpointRun.cumulativeLayers r) outer allowed hb outerLicensed.wraps r
      (stageStartTime bits r + phaseConfigurations.length)
      (Registers.newJob SOnly38.program).clearScan (CTS.zeroPhase SOnly38.program)
      bit suffix (baseCarrier environment continuation)
      outerContext fullContext innerContext targetContext responseTicks
      (RegistersCoherent.initial SOnly38.program).clearScan response allNonempty
      (base_ordinary (environment_ordinary _ SOnly38.program SOnly38.dispatcher bits) hb).1 sourceAllowed
  have restChain := ExactMutationChain.prepend baseRun' pendingChain
  have completeChain := SchedulerRecurrence.ExactMutationChain.append prefixChain
    (SchedulerRecurrence.ExactMutationChain.append phaseChain restChain)
  have phaseLicensed := phase_list_licensed SOnly38.program SOnly38.dispatcher bits
    (Registers.newJob SOnly38.program) parents outerLicensed.wraps r
  have licensed := samples_append prefixLicensed (samples_append phaseLicensed pendingLicensed)
  refine ⟨parents, finalRegisters, finalPhase, finalBit, finalSuffix, finalSource,
    finalOuterContext, finalFullContext, finalInnerContext, finalTargetContext,
    finalTicks, prefixConfigurations ++ (phaseConfigurations ++ pendingConfigurations),
    completeChain, ?_, coherent, finalTrace, sourceEq, licensed, outerLicensed, hb, finalLicensed⟩
  simp only [List.length_append, prefixCount, pendingCount]
  rw [SchedulerNestedPhase.positiveStageConfigurationsAt_length]
  simp only [firstJobPreResponseTime, Nat.add_assoc]
  rfl


end SOnlyGlobalFirstPrefix

#print axioms SOnlyGlobalFirstPrefix.stageStart_licensed
#print axioms SOnlyGlobalFirstPrefix.firstJob_response_prefix_licensed
