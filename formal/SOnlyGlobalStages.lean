import SOnlyGlobalTerminal
import SOnlyResponseLabels
import SOnlyFirstEventOrigins

/-!
# Licensed generated nonempty stages

Actual job, handoff, phase and prelude constructors are composed with their
label/snapshot origin certificates. The whole-stage invariant is constructed
from finite source-prefix permissions and generated parent certificates.
-/
namespace SOnlyGlobalStages
open PureSFormal PureSFormal.PureS PureSFormal.Research
open SchedulerControl SchedulerInvariant SchedulerCycle SchedulerResponseInvariant
open SchedulerNestedResponse SchedulerCompletedContext SchedulerTraceAlgebra
open SOnlyProvenance SOnlyGeneratedOrigins SOnlyGlobalAncestors SOnlyGlobalOrigins
open SOnlyGlobalTerminal SOnlySchedulerOrigins SOnlyResponseLabels
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000

def LicensedNonfinalJobs
    (program : CTS.Program) (dispatcher : ActionDispatcher program)
    (bit : Bool) (suffix : List Bool) (fuel count sampleIndex : Nat)
    (outerParents : List ParentFrame) (layers : Nat)
    (_outer : CompletedParents program dispatcher outerParents layers)
    (allowed : OriginSet program) : Prop :=
  ∃ nextParents : List ParentFrame,
  ∃ configurations : List (SchedulerInvariant.Configuration program dispatcher),
    let bits := bit :: suffix
    let environment :=
      environmentCode (compileActions program dispatcher.tree) bits
    ExactMutationChain (SchedulerControl.machine program dispatcher)
      (SchedulerNestedPhase.fuelTerminalConfigurationAt program dispatcher bits
        (Registers.newJob program)
        (Dovetail.clockExit (fuel + 1) 0 environment) nextParents (fuel + 1) 0)
      (SchedulerNestedPhase.fuelTerminalConfigurationAt program dispatcher bits
        (Registers.newJob program)
        (Dovetail.clockExit (fuel + 1) count environment) outerParents
        (fuel + 1) 0)
      configurations ∧
    IndexedResponseSampledStates program dispatcher (bit :: suffix)
      sampleIndex configurations ∧
    configurations.length =
      ExactCheckpointRun.jobsCost program dispatcher (bit :: suffix) (fuel + 1)
        count ∧
    CompletedParents program dispatcher nextParents (layers + count) ∧
    SamplesLicensed (RootLicensed program dispatcher.tree allowed) configurations ∧
    LicensedParents program dispatcher allowed nextParents

/-- Construct all nonfinal jobs using the verified response and handoff phase
executors. -/
theorem nonfinalJobs_licensed
    (program : CTS.Program) (dispatcher : ActionDispatcher program)
    (bit : Bool) (suffix : List Bool) (fuel : Nat)
    (allowed : OriginSet program)
    (sourceAllowed : SourceAllowed allowed (CTS.initial program (bit :: suffix)) (fuel + 1))
    (allNonempty : ∀ index, index ≤ fuel + 1 →
      (CTS.iterate program index
        (CTS.initial program (bit :: suffix))).data ≠ []) :
    ∀ (count sampleIndex : Nat) (outerParents : List ParentFrame)
      (layers : Nat)
      (outer : CompletedParents program dispatcher outerParents layers)
      (_outerLicensed : LicensedParents program dispatcher allowed outerParents),
      LicensedNonfinalJobs program dispatcher bit suffix fuel count sampleIndex
        outerParents layers outer allowed
  | 0, sampleIndex, outerParents, layers, outer, outerLicensed => by
      exact ⟨outerParents, [], .done 0 ⟨rfl, rfl⟩, .nil sampleIndex, rfl,
        by simpa using outer, (by intro configuration member; cases member), outerLicensed⟩
  | count + 1, sampleIndex, outerParents, layers, outer, outerLicensed => by
      let bits := bit :: suffix
      let environment :=
        environmentCode (compileActions program dispatcher.tree) bits
      let continuation := Dovetail.clockExit (fuel + 1) (count + 1) environment
      obtain ⟨responseParents, checkRegisters, responseConfigurations,
          responseChain, responseSampled, responseLength, responseOuter,
          responseErase, responseArity, responseLicensed, responseParentsLicensed⟩ :=
        SOnlyGlobalOrigins.completeNonemptyJob_licensed program dispatcher bit
          suffix (fuel + 1) count (fuel + 1) sampleIndex environment outerParents
          layers outer allowed (environment_ordinary _ program dispatcher bits).1 outerLicensed
          (Nat.succ_ne_zero fuel) allNonempty sourceAllowed
      have handoff := SchedulerJobHandoff.handoffFuelInvariantAt program
        dispatcher bits checkRegisters fuel count
        (sampleIndex + responseConfigurations.length) responseParents
        (layers + 1) responseOuter
      have tail := nonfinalJobs_licensed program dispatcher bit suffix fuel allowed sourceAllowed allNonempty count
        (sampleIndex + responseConfigurations.length +
          (SchedulerJobHandoff.handoffFuelConfigurationsAt program dispatcher
            bits fuel count responseParents).length)
        responseParents (layers + 1) responseOuter responseParentsLicensed
      obtain ⟨terminalParents, tailConfigurations, tailChain, tailSampled,
          tailLength, terminalOuter, tailLicensed, terminalLicensed⟩ := tail
      let handoffConfigurations :=
        SchedulerJobHandoff.handoffFuelConfigurationsAt program dispatcher bits
          fuel count responseParents
      let configurations := responseConfigurations ++
        handoffConfigurations ++ tailConfigurations
      have responseThenHandoff : ExactMutationChain
          (SchedulerControl.machine program dispatcher)
          (SchedulerNestedPhase.fuelTerminalConfigurationAt program dispatcher
            bits (Registers.newJob program)
            (Dovetail.clockExit (fuel + 1) count environment) responseParents
            (fuel + 1) 0)
          (SchedulerNestedPhase.fuelTerminalConfigurationAt program dispatcher
            bits (Registers.newJob program) continuation outerParents
            (fuel + 1) 0)
          (responseConfigurations ++ handoffConfigurations) := by
        exact SchedulerRecurrence.ExactMutationChain.append responseChain
          (by simpa [bits, environment, handoffConfigurations,
              SchedulerJobHandoff.continuationCursorAt] using handoff.chain)
      have completeChain := SchedulerRecurrence.ExactMutationChain.append
        responseThenHandoff tailChain
      have handoffSampled : IndexedResponseSampledStates program dispatcher bits
          (sampleIndex + responseConfigurations.length)
          handoffConfigurations := by
        simpa [handoffConfigurations] using handoff.sampled
      have responseAndHandoffSampled :=
        SchedulerNestedPhase.IndexedResponseSampledStates.append program
          dispatcher bits responseSampled handoffSampled
      have completeSampled :=
        SchedulerNestedPhase.IndexedResponseSampledStates.append program
          dispatcher bits responseAndHandoffSampled (by
            simpa [handoffConfigurations, Nat.add_assoc] using tailSampled)
      have handoffLicensed := handoff_list_licensed program dispatcher bits fuel count
        responseParents responseParentsLicensed.wraps
      have allLicensed := samples_append (samples_append responseLicensed handoffLicensed) tailLicensed
      refine ⟨terminalParents, configurations, ?_, ?_, ?_, ?_, ?_, terminalLicensed⟩
      · simpa [bits, environment, continuation, configurations,
          handoffConfigurations] using completeChain
      · simpa [bits, configurations, handoffConfigurations] using
          completeSampled
      · simp only [configurations, List.length_append]
        rw [responseLength,
          SchedulerJobHandoff.handoffFuelConfigurationsAt_length, tailLength]
        rw [ExactCheckpointRun.jobsCost_succ]
        simp [Nat.add_assoc, Nat.add_comm]
      · have layerEq : (layers + 1) + count = layers + (count + 1) := by
          calc
            (layers + 1) + count = layers + (1 + count) :=
              Nat.add_assoc layers 1 count
            _ = layers + (count + 1) :=
              congrArg (Nat.add layers) (Nat.add_comm 1 count)
        rw [← layerEq]
        exact terminalOuter

      · simpa [configurations, handoffConfigurations, List.append_assoc] using allLicensed

theorem allNonemptyRaw_licensed
    (program : CTS.Program) (dispatcher : ActionDispatcher program)
    (bit : Bool) (suffix : List Bool) (fuel sampleIndex : Nat)
    (parents : List ParentFrame)
    (outer : CompletedParents program dispatcher parents
      (CheckpointRun.cumulativeLayers fuel))
    (allowed : OriginSet program)
    (outerLicensed : LicensedParents program dispatcher allowed parents)
    (sourceAllowed : SourceAllowed allowed (CTS.initial program (bit :: suffix)) (fuel + 1))
    (allNonempty : ∀ index, index ≤ fuel + 1 →
      (CTS.iterate program index
        (CTS.initial program (bit :: suffix))).data ≠ [])
    (indexEq : sampleIndex +
        ExactCheckpointRun.stageCost program dispatcher (bit :: suffix)
          (fuel + 1) =
      ExactCheckpointRun.checkpointTime program dispatcher (bit :: suffix)
        (fuel + 1)) :
    ∃ nextParents configurations checkpoint semantic,
      SchedulerStageAssembly.RawStageSegment program dispatcher (bit :: suffix) (fuel + 1) sampleIndex
        parents (CheckpointRun.cumulativeLayers fuel) nextParents configurations
        checkpoint semantic ∧
      SamplesLicensed (RootLicensed program dispatcher.tree allowed) configurations ∧
      LicensedParents program dispatcher allowed nextParents := by
  let bits := bit :: suffix
  let environment :=
    environmentCode (compileActions program dispatcher.tree) bits
  let stage := fuel + 1
  let phaseConfigurations :=
    SchedulerNestedPhase.positiveStageConfigurationsAt program dispatcher bits
      (Registers.newJob program) parents fuel
  have phase := SchedulerNestedPhase.positiveStagePhaseInvariantAt program
    dispatcher bits (Registers.newJob program) (CTS.zeroPhase program) [] false
    (RegistersCoherent.initial program) parents
    (CheckpointRun.cumulativeLayers fuel) outer sampleIndex fuel
  have phaseChain : ExactMutationChain
      (SchedulerControl.machine program dispatcher)
      (SchedulerNestedPhase.fuelTerminalConfigurationAt program dispatcher bits
        (Registers.newJob program) (Dovetail.clockExit stage fuel environment)
        parents stage 0)
      (SchedulerRecurrence.stageSourceConfiguration program dispatcher bits
        stage parents)
      phaseConfigurations := by
    simpa [phaseConfigurations, stage, environment, bits,
      SchedulerRecurrence.stageSourceConfiguration] using phase.chain
  have phaseSampled : IndexedResponseSampledStates program dispatcher bits
      sampleIndex phaseConfigurations := by
    simpa [phaseConfigurations, bits] using phase.sampled
  obtain ⟨terminalParents, nonfinalConfigurations, nonfinalChain,
      nonfinalSampled, nonfinalLength, nonfinalOuter, nonfinalLicensed, nonfinalParentsLicensed⟩ :=
    nonfinalJobs_licensed program dispatcher bit suffix fuel allowed sourceAllowed
      allNonempty fuel (sampleIndex + phaseConfigurations.length) parents
      (CheckpointRun.cumulativeLayers fuel) outer outerLicensed
  obtain ⟨nextParents, terminalLeading, checkpoint, terminalConfigurations,
      terminalChain, terminalEq, terminalLength, terminalData,
      classifyTerminal, terminalLicensed, nextParentsLicensed⟩ :=
    SOnlyGlobalTerminal.completeNonemptyTerminalJobRaw_licensed program dispatcher
      bit suffix stage
      (sampleIndex + phaseConfigurations.length +
        nonfinalConfigurations.length)
      terminalParents
      (CheckpointRun.cumulativeLayers fuel + fuel) nonfinalOuter allowed nonfinalParentsLicensed
      (Nat.succ_ne_zero fuel) allNonempty sourceAllowed
  let configurations := phaseConfigurations ++ nonfinalConfigurations ++
    terminalConfigurations
  have phaseThenNonfinal := SchedulerRecurrence.ExactMutationChain.append phaseChain nonfinalChain
  have completeChain := SchedulerRecurrence.ExactMutationChain.append phaseThenNonfinal terminalChain
  have prefixSampled :=
    SchedulerNestedPhase.IndexedResponseSampledStates.append program dispatcher
      bits phaseSampled (by simpa using nonfinalSampled)
  have terminalLast : LastSample terminalConfigurations checkpoint := by
    rw [terminalEq]
    exact LastSample.appendLeft terminalLeading (.one checkpoint)
  have completeLast : LastSample configurations checkpoint := by
    exact LastSample.appendLeft
      (phaseConfigurations ++ nonfinalConfigurations) terminalLast
  obtain ⟨result, shape, shapeLayers, shapeTerminal, queue, completed⟩ :=
    terminalData
  have layerEq :
      (CheckpointRun.cumulativeLayers fuel + fuel) + 1 =
        CheckpointRun.cumulativeLayers (fuel + 1) := by
    rw [CheckpointRun.cumulativeLayers_succ]
    exact Nat.add_assoc (CheckpointRun.cumulativeLayers fuel) fuel 1
  have completed' : CompletedParents program dispatcher nextParents
      (CheckpointRun.cumulativeLayers (fuel + 1)) := by
    exact Eq.mp
      (congrArg
        (fun count => CompletedParents program dispatcher nextParents count)
        layerEq)
      completed
  have semantic : SchedulerRecurrence.PositiveCertificateData program dispatcher
      bits (fuel + 1) checkpoint nextParents := by
    exact SchedulerRecurrence.PositiveCertificateData.ofTerminalShape program
      dispatcher bits (fuel + 1) checkpoint nextParents completed' .fresh result
      shape (by simpa [layerEq] using shapeLayers) shapeTerminal queue
  have completeLength : configurations.length =
      ExactCheckpointRun.stageCost program dispatcher bits (fuel + 1) := by
    simp only [configurations, List.length_append]
    rw [SchedulerNestedPhase.positiveStageConfigurationsAt_length,
      nonfinalLength, terminalLength]
    simp [ExactCheckpointRun.stageCost, stage, Nat.succ_mul, Nat.mul_succ,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    rw [← Nat.add_assoc 2 8]
  have checkpointIndex : sampleIndex + configurations.length =
      ExactCheckpointRun.checkpointTime program dispatcher bits (fuel + 1) := by
    rw [completeLength]
    exact indexEq
  have phaseLicensed := phase_list_licensed program dispatcher bits (Registers.newJob program)
    parents outerLicensed.wraps fuel
  have allLicensed := samples_append (samples_append phaseLicensed nonfinalLicensed) terminalLicensed
  have licensed : SamplesLicensed (RootLicensed program dispatcher.tree allowed) configurations := by
    simpa [configurations, phaseConfigurations, List.append_assoc] using allLicensed
  refine ⟨nextParents, configurations, checkpoint, semantic, ?_, licensed, nextParentsLicensed⟩
  refine
    { chain := ?_
      count := completeLength
      last := completeLast
      nextOuter := ?_
      checkpointIndex := checkpointIndex
      classify := ?_ }
  · simpa [configurations, stage, bits, environment,
      SchedulerRecurrence.stageSourceConfiguration,
      SchedulerRootContinuation.nextStageSourceConfiguration] using completeChain
  · exact completed'
  · intro activeContext checkpointChain certificate
    have terminalIndex :
        (sampleIndex + phaseConfigurations.length +
            nonfinalConfigurations.length) + terminalConfigurations.length =
          ExactCheckpointRun.checkpointTime program dispatcher bits
            (fuel + 1) := by
      simpa [configurations, List.length_append, Nat.add_assoc] using
        checkpointIndex
    have terminalSampled := classifyTerminal certificate terminalIndex
    have completeSampled :=
      SchedulerNestedPhase.IndexedResponseSampledStates.append program dispatcher
        bits prefixSampled (by
          simpa [Nat.add_assoc] using terminalSampled)
    simpa [configurations] using completeSampled


/-- Actual finite scheduler prefixes preserve generated origin licenses, with
licensed parents carried into the next stage. -/
theorem positiveStages_licensed
    (program : CTS.Program) (dispatcher : ActionDispatcher program)
    (bit : Bool) (suffix : List Bool) (allowed : OriginSet program) :
    ∀ offset,
      (∀ index, index ≤ offset + 1 →
        (CTS.iterate program index (CTS.initial program (bit :: suffix))).data ≠ []) →
      SourceAllowed allowed (CTS.initial program (bit :: suffix)) (offset + 1) →
      ∃ stages : SchedulerRecurrence.PositiveStages program dispatcher (bit :: suffix) (offset + 1),
        SamplesLicensed (RootLicensed program dispatcher.tree allowed) stages.configurations ∧
        LicensedParents program dispatcher allowed stages.nextParents
  | 0, allNonempty, sourceAllowed => by
      have indexEq : 1 + ExactCheckpointRun.stageCost program dispatcher (bit :: suffix) 1 =
          ExactCheckpointRun.checkpointTime program dispatcher (bit :: suffix) 1 :=
        (ExactCheckpointRun.checkpointTime_one program dispatcher (bit :: suffix)).symm
      obtain ⟨nextParents, configurations, checkpoint, semantic, raw, licensed, nextLicensed⟩ :=
        allNonemptyRaw_licensed program dispatcher bit suffix 0 1 []
          (CompletedParents.root program dispatcher) allowed (LicensedParents.nil program dispatcher allowed)
          sourceAllowed allNonempty indexEq
      let stages := SchedulerStageAssembly.RawStageSegment.first program dispatcher
        (bit :: suffix) semantic raw
      refine ⟨stages, ?_, nextLicensed⟩
      change SamplesLicensed (RootLicensed program dispatcher.tree allowed)
        (SchedulerRecurrence.initialPreludeConfigurations program dispatcher (bit :: suffix) ++ configurations)
      exact samples_append (prelude_list_licensed _ program dispatcher (bit :: suffix)) licensed
  | offset + 1, allNonempty, sourceAllowed => by
      obtain ⟨past, pastLicensed, pastParentsLicensed⟩ := positiveStages_licensed program dispatcher
        bit suffix allowed offset
        (fun index bound => allNonempty index (Nat.le_trans bound (Nat.le_succ _)))
        (sourceAllowed_mono sourceAllowed (Nat.le_succ _))
      have indexEq : past.configurations.length +
          ExactCheckpointRun.stageCost program dispatcher (bit :: suffix) (offset + 2) =
          ExactCheckpointRun.checkpointTime program dispatcher (bit :: suffix) (offset + 2) := by
        rw [past.count]
        exact ExactCheckpointRun.checkpointTime_positive_succ program dispatcher (bit :: suffix) offset
      obtain ⟨nextParents, configurations, checkpoint, semantic, raw, licensed, nextLicensed⟩ :=
        allNonemptyRaw_licensed program dispatcher bit suffix (offset + 1)
          past.configurations.length past.nextParents past.nextOuter allowed pastParentsLicensed
          sourceAllowed allNonempty indexEq
      let stages := SchedulerStageAssembly.RawStageSegment.extend past semantic raw
      refine ⟨stages, ?_, nextLicensed⟩
      change SamplesLicensed (RootLicensed program dispatcher.tree allowed)
        (past.configurations ++ configurations)
      exact samples_append pastLicensed licensed

/-- Every actual noninitial persistent sample receives its license from a
constructed finite stage prefix, rather than a reachability assumption. -/
theorem contractionRun_licensed (bits : List Bool) (index : Nat)
    (allowed : OriginSet SOnly38.program)
    (allNonempty : ∀ k, k ≤ index + 1 →
      (CTS.iterate SOnly38.program k (CTS.initial SOnly38.program bits)).data ≠ [])
    (sourceAllowed : SourceAllowed allowed (CTS.initial SOnly38.program bits) (index + 1)) :
    Licensed SOnly38.program SOnly38.dispatcher.tree allowed
      ((SOnlyEventTransfer.persistentSystem bits).contractionRun (index + 1)).cursor.erase := by
  cases bits with
  | nil => exact (allNonempty 0 (Nat.zero_le _) rfl).elim
  | cons bit suffix =>
      obtain ⟨stages, licensed, _⟩ := positiveStages_licensed SOnly38.program SOnly38.dispatcher
        bit suffix allowed index allNonempty sourceAllowed
      have inRange : index < stages.configurations.length := Nat.lt_of_lt_of_le
        (Nat.lt_succ_self index) stages.horizonLower
      let configuration := stages.configurations[index]
      have atIndex : stages.configurations[index]? = some configuration := by simp [configuration, inRange]
      have sampled := SOnlyEventTransfer.exactChain_sample SOnly38.program SOnly38.dispatcher
        (bit :: suffix) (SchedulerRecurrence.initialGood SOnly38.program SOnly38.dispatcher (bit :: suffix))
        stages.chain (sampleIndex := 0) rfl atIndex
      have sampleEq : (SOnlyEventTransfer.persistentSystem (bit :: suffix)).contractionRun (index + 1) = configuration := by
        simpa using sampled
      rw [sampleEq]
      exact licensed configuration (List.getElem_mem inRange)

/-- Global event soundness in the nonempty regime: an event-free CTS source
has no target-shaped descendant at any actual root-reset contraction sample. -/
theorem no_event_on_nonempty_event_free_run (bits : List Bool)
    (nonempty : ∀ k, (CTS.iterate SOnly38.program k (CTS.initial SOnly38.program bits)).data ≠ [])
    (noEvent : ∀ k, ¬ SOnlySource.Event
      (CTS.iterate SOnly38.program k (CTS.initial SOnly38.program bits))) :
    ∀ index, SOnlyObserver.event (SOnly38.trajectory bits index) = false := by
  let allowed : OriginSet SOnly38.program := fun label _ => label ≠ SOnly38.targetLabel
  have excludes : ∀ snapshot, ¬allowed SOnly38.targetLabel snapshot := by
    intro snapshot h; exact h rfl
  intro index
  rw [SOnlyEventTransfer.trajectory_eq_contractionRun]
  apply SOnlyFirstEventOrigins.event_false_of_excludes (allowed := allowed) ?_ excludes
  cases index with
  | zero => exact initial_licensed _ SOnly38.program SOnly38.dispatcher bits
  | succ index =>
      apply contractionRun_licensed bits index allowed (fun k _ => nonempty k)
      intro sourceIndex bound label snapshot sourceLabel
      change label ≠ SOnly38.targetLabel
      intro equal
      subst label
      exact noEvent sourceIndex ((target_sourceLabel_iff _).mp sourceLabel)

end SOnlyGlobalStages

#print axioms SOnlyGlobalStages.nonfinalJobs_licensed
#print axioms SOnlyGlobalStages.allNonemptyRaw_licensed
#print axioms SOnlyGlobalStages.positiveStages_licensed
#print axioms SOnlyGlobalStages.contractionRun_licensed
#print axioms SOnlyGlobalStages.no_event_on_nonempty_event_free_run
